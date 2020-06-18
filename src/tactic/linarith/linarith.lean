/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import tactic.ring
import tactic.linarith.preprocessing
import tactic.linarith.elimination
import tactic.cancel_denoms

/-!
# Linear arithmetic

`linarith` is a tactic for discharging linear arithmetic goals using Fourier-Motzkin elimination.

`linarith` is (in principle) complete for ℚ and ℝ. It is not complete for non-dense orders, i.e. ℤ.

- @TODO: investigate storing comparisons in a list instead of a set, for possible efficiency gains
- @TODO: delay proofs of denominator normalization and nat casting until after contradiction is
  found
-/

open native
namespace linarith


/-!
### Parsing input expressions into linear form

`linarith` computes the linear form of its input expressions,
assuming (without justification) that the type of these expressions
is a commutative semiring.

It identifies atoms up to ring-equivalence: that is, `(y*3)*x` will be identified `3*(x*y)`,
where the monomial `x*y` is the linear atom.

* Variables are represented by natural numbers.
* Monomials are represented by `monom := rb_map ℕ ℕ`. The monomial `1` is represented by the empty map.
* Linear combinations of monomials are represented by `sum := rb_map monom ℤ`.

All input expressions are converted to `sum`s, preserving the map from expressions to variables.
We then discard the monomial information, mapping each distinct monomial to a natural number.
The resulting `rb_map ℕ ℤ` represents the ring-normalized linear form of the expression.

This is ultimately converted into a `linexp` in the obvious way.

#### Parsing datatypes
-/

/-- Variables (represented by natural numbers) map to their power. -/
@[reducible] meta def monom : Type := rb_map ℕ ℕ

/-- Compare monomials by first comparing their keys and then their powers. -/
@[reducible] meta def monom.lt : monom → monom → Prop :=
λ a b, (a.keys < b.keys) || ((a.keys = b.keys) && (a.values < b.values))

/-- The `has_lt` instance for `monom` is only needed locally. -/
local attribute [instance]
meta def monom_has_lt : has_lt monom := ⟨monom.lt⟩

/-- Linear combinations of monomials are represented by mapping monomials to coefficients. -/
@[reducible] meta def sum : Type := rb_map monom ℤ

/-- `sum.scale_by_monom s m` multiplies every monomial in `s` by `m`. -/
meta def sum.scale_by_monom (s : sum) (m : monom) : sum :=
s.fold mk_rb_map $ λ m' coeff sm, sm.insert (m.add m') coeff

/-- `sum.mul s1 s2` distributes the multiplication of two sums.` -/
meta def sum.mul (s1 s2 : sum) : sum :=
s1.fold mk_rb_map $ λ mn coeff sm, sm.add $ (s2.scale_by_monom mn).scale coeff

/-- `sum_of_monom m` lifts `m` to a sum with coefficient `1`. -/
meta def sum_of_monom (m : monom) : sum :=
mk_rb_map.insert m 1

/-- The unit monomial `one` is represented by the empty rb map. -/
meta def one : monom := mk_rb_map

/-- A scalar `z` is represented by a `sum` with coefficient `z` and monomial `one` -/
meta def scalar (z : ℤ) : sum :=
mk_rb_map.insert one z

/-- A single variable `n` is represented by a sum with coefficient `1` and monomial `n`. -/
meta def var (n : ℕ) : sum :=
mk_rb_map.insert (mk_rb_map.insert n 1) 1

section parse

open ineq tactic

/-! #### Parsing algorithms -/

/--
`map_of_expr red map e` computes the linear form of `e`.

`map` is a lookup map from atomic expressions to variable numbers.
If a new atomic expression is encountered, it is added to the map with a new number.
It matches atomic expressions up to reducibility given by `red`.

Because it matches up to definitional equality, this function must be in the `tactic` monad,
and forces some functions that call it into `tactic` as well.
-/
meta def map_of_expr (red : transparency) : expr_map ℕ → expr → tactic (expr_map ℕ × sum)
| m e@`(%%e1 * %%e2) :=
   do (m', comp1) ← map_of_expr m e1,
      (m', comp2) ← map_of_expr m' e2,
      return (m', comp1.mul comp2)
| m `(%%e1 + %%e2) :=
   do (m', comp1) ← map_of_expr m e1,
      (m', comp2) ← map_of_expr m' e2,
      return (m', comp1.add comp2)
| m `(%%e1 - %%e2) :=
   do (m', comp1) ← map_of_expr m e1,
      (m', comp2) ← map_of_expr m' e2,
      return (m', comp1.add (comp2.scale (-1)))
| m `(-%%e) := do (m', comp) ← map_of_expr m e, return (m', comp.scale (-1))
| m e :=
  match e.to_int with
  | some 0 := return ⟨m, mk_rb_map⟩
  | some z := return ⟨m, scalar z⟩
  | none :=
    (do k ← m.find_defeq red e, return (m, var k)) <|>
    (let n := m.size + 1 in return (m.insert e n, var n))
  end

/--
`sum_to_lf s map` eliminates the monomial level of the `sum` `s`.

`map` is a lookup map from monomials to variable numbers.
The output `rb_map ℕ ℤ` has the same structure as `sum`,
but each monomial key is replaced with its index according to `map`.
If any new monomials are encountered, they are assigned variable numbers and `map` is updated.
 -/
meta def sum_to_lf (s : sum) (m : rb_map monom ℕ) : rb_map monom ℕ × rb_map ℕ ℤ :=
s.fold (m, mk_rb_map) $ λ mn coeff ⟨map, out⟩,
  match map.find mn with
  | some n := ⟨map, out.insert n coeff⟩
  | none := let n := map.size in ⟨map.insert mn n, out.insert n coeff⟩
  end

/--
`to_comp red e e_map monom_map` converts an expression of the form `t < 0`, `t ≤ 0`, or `t = 0`
into a `comp` object.

`e_map` maps atomic expressions to indices; `monom_map` maps monomials to indices.
Both of these are updated during processing and returned.
-/
meta def to_comp (red : transparency) (e : expr) (e_map : expr_map ℕ) (monom_map : rb_map monom ℕ) :
  tactic (comp × expr_map ℕ × rb_map monom ℕ) :=
do (iq, e) ← parse_into_comp_and_expr e,
   (m', comp') ← map_of_expr red e_map e,
   let ⟨nm, mm'⟩ := sum_to_lf comp' monom_map,
   return ⟨⟨iq, mm'.to_linexp⟩,m',nm⟩

/--
`to_comp_fold red e_map exprs monom_map` folds `to_comp` over `exprs`,
updating `e_map` and `monom_map` as it goes.
 -/
meta def to_comp_fold (red : transparency) : expr_map ℕ → list expr → rb_map monom ℕ →
      tactic (list comp × expr_map ℕ × rb_map monom ℕ)
| m [] mm := return ([], m, mm)
| m (h::t) mm :=
  do (c, m', mm') ← to_comp red h m mm,
      (l, mp, mm') ← to_comp_fold m' t mm',
      return (c::l, mp, mm')

/-! ### Control functions -/

/--
`mk_linarith_structure red l` takes a list of proofs of props of the form `t {<, ≤, =} 0`,
and creates a `linarith_structure`. The transparency setting `red` is used to unify atoms.

Along with a `linarith_structure`, it produces a map `ℕ → (expr × expr)`.
This map assigns indices to the hypotheses in `l`. It maps a natural number `n` to a pair
`(prf, tp)`, where `prf` is the `n`th element of `l` and is a proof of the comparison `tp`.
-/
meta def mk_linarith_structure (red : transparency) (l : list expr) :
  tactic (linarith_structure × rb_map ℕ (expr × expr)) :=
do pftps ← l.mmap infer_type,
  (l', _, map) ← to_comp_fold red mk_rb_map pftps mk_rb_map,
  let lz := list.enum $ (l.zip pftps).zip l',
  let prmap := rb_map.of_list $ lz.map (λ ⟨n, x⟩, (n, x.1)),
  let vars : rb_set ℕ := rb_map.set_of_list $ list.range map.size,
  let pc : rb_set pcomp :=
    rb_set.of_list_core mk_pcomp_set $ lz.map (λ ⟨n, x⟩, ⟨x.2, comp_source.assump n⟩),
  return (⟨vars, pc⟩, prmap)

/--
`linarith_monad.run red tac l` runs the `linarith` process `tac` on input `l`.
It returns the value produced by `tac` if `tac` does not find a contradiction.
Otherwise it returns a `pcomp` representing a proof of `0 < 0`.

It also produces a map `ℕ → (expr × expr)`.
This map assigns indices to the hypotheses in `l`. It maps a natural number `n` to a pair
`(prf, tp)`, where `prf` is the `n`th element of `l` and is a proof of the comparison `tp`.
This map is needed to reconstruct the proof of the discovered contradiction.
 -/
meta def linarith_monad.run (red : transparency) {α} (tac : linarith_monad α) (l : list expr) :
  tactic ((pcomp ⊕ α) × rb_map ℕ (expr × expr)) :=
do (struct, inputs) ← mk_linarith_structure red l,
match (state_t.run (validate >> tac) struct).run with
| (except.ok (a, _)) := return (sum.inr a, inputs)
| (except.error contr) := return (sum.inl contr, inputs)
end

end parse

/-!
### Verification

`linarith_monad.run` is used to search for a way to derive `false` from a set of hypotheses.
This search is unverified, but it returns a certificate:
a map `m` from hypothesis indices to natural number coefficients.
If our set of hypotheses has the form  `{tᵢ Rᵢ 0}`,
then the elimination process should have guaranteed that
1.\ `∑ (m i)*tᵢ = 0`,
with at least one `i` such that `m i > 0` and `Rᵢ` is `<`.

We have also that
2.\ `∑ (m i)*tᵢ < 0`,
since for each `i`, `(m i)*tᵢ ≤ 0` and at least one is strictly negative.
So we conclude a contradiction `0 < 0`.

It remains to produce proofs of (1) and (2). (1) is verified by calling the `discharger` tactic
of the `linarith_config` object, which is typically `ring`. We prove (2) by folding over the
set of hypotheses.

#### Auxiliary functions for assembling proofs
-/

section prove
open ineq tactic

/--
`mul_expr n e` creates a `pexpr` representing `n*e`.
When elaborated, the coefficient will be a native numeral of the same type as `e`.
-/
meta def mul_expr (n : ℕ) (e : expr) : pexpr :=
if n = 1 then ``(%%e) else
``(%%(nat.to_pexpr n) * %%e)

private meta def add_exprs_aux : pexpr → list pexpr → pexpr
| p [] := p
| p [a] := ``(%%p + %%a)
| p (h::t) := add_exprs_aux ``(%%p + %%h) t

/--
`add_exprs l` creates a `pexpr` representing the sum of the elements of `l`, associated left.
If `l` is empty, it will be the `pexpr` 0. Otherwise, it does not include 0 in the sum.
-/
meta def add_exprs : list pexpr → pexpr
| [] := ``(0)
| (h::t) := add_exprs_aux h t

/--
If our goal is to add together two inequalities `t1 R1 0` and `t2 R2 0`,
`ineq_const_nm R1 R2` produces the strength of the inequality in the sum `R`,
along with the name of a lemma to apply in order to conclude `t1 + t2 R 0`.
-/
meta def ineq_const_nm : ineq → ineq → (name × ineq)
| eq eq := (``eq_of_eq_of_eq, eq)
| eq le := (``le_of_eq_of_le, le)
| eq lt := (``lt_of_eq_of_lt, lt)
| le eq := (``le_of_le_of_eq, le)
| le le := (`add_nonpos, le)
| le lt := (`add_neg_of_nonpos_of_neg, lt)
| lt eq := (``lt_of_lt_of_eq, lt)
| lt le := (`add_neg_of_neg_of_nonpos, lt)
| lt lt := (`add_neg, lt)

/--
`mk_lt_zero_pf_aux c pf npf coeff` assumes that `pf` is a proof of `t1 R1 0` and `npf` is a proof
of `t2 R2 0`. It uses `mk_single_comp_zero_pf` to prove `t1 + coeff*t2 R 0`, and returns `R`
along with this proof.
-/
meta def mk_lt_zero_pf_aux (c : ineq) (pf npf : expr) (coeff : ℕ) : tactic (ineq × expr) :=
do (iq, h') ← mk_single_comp_zero_pf coeff npf,
   let (nm, niq) := ineq_const_nm c iq,
   n ← resolve_name nm,
   e' ← to_expr ``(%%n %%pf %%h'),
   return (niq, e')

/--
`mk_lt_zero_pf coeffs pfs` takes a list of coefficients and a list of proofs of the form `tᵢ Rᵢ 0`,
of equal length. It produces a proof that `∑tᵢ R 0`, where `R` is as strong as possible.
-/
meta def mk_lt_zero_pf : list ℕ → list expr → tactic expr
| _ [] := fail "no linear hypotheses found"
| [c] [h] := prod.snd <$> mk_single_comp_zero_pf c h
| (c::ct) (h::t) :=
  do (iq, h') ← mk_single_comp_zero_pf c h,
     prod.snd <$> (ct.zip t).mfoldl (λ pr ce, mk_lt_zero_pf_aux pr.1 pr.2 ce.2 ce.1) (iq, h')
| _ _ := fail "not enough args to mk_lt_zero_pf"

/-- If `prf` is a proof of `t R s`, `term_of_ineq_prf prf` returns `t`. -/
meta def term_of_ineq_prf (prf : expr) : tactic expr :=
prod.fst <$> (infer_type prf >>= get_rel_sides)

/-- If `prf` is a proof of `t R s`, `ineq_prf_tp prf` returns the type of `t`. -/
meta def ineq_prf_tp (prf : expr) : tactic expr :=
term_of_ineq_prf prf >>= infer_type

/--
`mk_neg_one_lt_zero_pf tp` returns a proof of `-1 < 0`,
where the numerals are natively of type `tp`.
-/
meta def mk_neg_one_lt_zero_pf (tp : expr) : tactic expr :=
to_expr ``((neg_neg_of_pos zero_lt_one : -1 < (0 : %%tp)))

/--
If `e` is a proof that `t = 0`, `mk_neg_eq_zero_pf e` returns a proof that `-t = 0`.
-/
meta def mk_neg_eq_zero_pf (e : expr) : tactic expr :=
to_expr ``(neg_eq_zero.mpr %%e)

/--
`prove_eq_zero_using tac e` tries to use `tac` to construct a proof of `e = 0`.
-/
meta def prove_eq_zero_using (tac : tactic unit) (e : expr) : tactic expr :=
do tgt ← to_expr ``(%%e = 0),
   prod.snd <$> solve_aux tgt (tac >> done)

/--
`add_neg_eq_pfs l` inspects the list of proofs `l` for proofs of the form `t = 0`. For each such
proof, it adds a proof of `-t = 0` to the list.
-/
meta def add_neg_eq_pfs : list expr → tactic (list expr)
| [] := return []
| (h::t) :=
  do some (iq, tp) ← parse_into_comp_and_expr <$> infer_type h,
  match iq with
  | ineq.eq := do nep ← mk_neg_eq_zero_pf h, tl ← add_neg_eq_pfs t, return $ h::nep::tl
  | _ := list.cons h <$> add_neg_eq_pfs t
  end

/-! #### The main method -/

/--
`prove_false_by_linarith` is the main workhorse of `linarith`.
Given a list `l` of proofs of `tᵢ Rᵢ 0` and a proof state with target `false`,
it tries to derive a contradiction from `l` and use this to close the goal.
-/
meta def prove_false_by_linarith (cfg : linarith_config) : list expr → tactic unit
| [] := fail "no args to linarith"
| l@(h::t) := do
    -- for the elimination to work properly, we must add a proof of `-1 < 0` to the list,
    -- along with negated equality proofs.
    l' ← add_neg_eq_pfs l,
    hz ← ineq_prf_tp h >>= mk_neg_one_lt_zero_pf,
    -- perform the elimination and fail if no contradiction is found.
    (sum.inl contr, inputs) ← elim_all_vars.run cfg.transparency (hz::l')
      | fail "linarith failed to find a contradiction",
    -- we construct two lists `coeffs` and `pfs` of equal length,
    -- filtering out the comparisons that were not used in deriving the contradiction.
    linarith_trace "linarith has found a contradiction",
    let coeff_map := contr.src.flatten,
    let coeffs := inputs.keys.map coeff_map.ifind,
    let pfs : list expr := inputs.keys.map (λ k, (inputs.ifind k).1),
    let zip := (coeffs.zip pfs).filter (λ pr, pr.1 ≠ 0),
    let (coeffs, pfs) := zip.unzip,
    mls ← zip.mmap (λ pr, do e ← term_of_ineq_prf pr.2, return (mul_expr pr.1 e)),
    -- `sm` is the sum of input terms, scaled to cancel out all variables.
    sm ← to_expr $ add_exprs mls,
    pformat! "The expression\n  {sm}\nshould be both 0 and negative" >>= linarith_trace,
    -- we prove that `sm = 0`, typically with `ring`.
    sm_eq_zero ← prove_eq_zero_using cfg.discharger sm,
    linarith_trace "We have proved that it is zero",
    -- we also prove that `sm < 0`.
    sm_lt_zero ← mk_lt_zero_pf coeffs pfs,
    linarith_trace "We have proved that it is negative",
    -- this is a contradiction.
    pftp ← infer_type sm_lt_zero,
    (_, nep, _) ← rewrite_core sm_eq_zero pftp,
    pf' ← mk_eq_mp nep sm_lt_zero,
    mk_app `lt_irrefl [pf'] >>= exact

end prove


section
open tactic linarith

/-! ### Control -/

-- return : the type it compares over
meta def apply_contr_lemma : tactic (option (expr × expr)) :=
do t ← target,
   match get_contr_lemma_name_and_type t with
   | some (nm, tp) := do applyc nm, v ← intro1, return $ some (tp, v)
   | none := return none
   end

meta def partition_by_type_aux : rb_lmap expr expr → list expr → tactic (rb_lmap expr expr)
| m [] := return m
| m (h::t) := do tp ← ineq_prf_tp h, partition_by_type_aux (m.insert tp h) t

meta def partition_by_type (l : list expr) : tactic (rb_lmap expr expr) :=
partition_by_type_aux mk_rb_map l



meta def try_linarith_on_lists (cfg : linarith_config) (ls : list (list expr)) : tactic unit :=
(first $ ls.map $ prove_false_by_linarith cfg) <|> fail "linarith failed to find a contradiction"

meta def run_linarith_on_pfs (cfg : linarith_config) (hyps : list expr) (pref_type : option expr) :
  tactic unit :=
do hyps ← preprocess (cfg.preprocessors.get_or_else default_preprocessors) hyps,
   linarith_trace_proofs
     ("after preprocessing, linarith has " ++ to_string hyps.length ++ " facts:") hyps,
   hyp_set ← partition_by_type hyps,
   linarith_trace format!"hypotheses appear in {hyp_set.size} different types",
   match pref_type with
   | some t := prove_false_by_linarith cfg (hyp_set.ifind t) <|>
               try_linarith_on_lists cfg (rb_map.values (hyp_set.erase t))
   | none := try_linarith_on_lists cfg (rb_map.values hyp_set)
   end

meta def filter_hyps_to_type (restr_type : expr) : list expr → tactic (list expr)
| [] := return []
| (h::t) := do ht ← infer_type h,
  match get_contr_lemma_name_and_type ht with
  | some (_, h_type) :=
    do t ← (filter_hyps_to_type t), unify h_type restr_type >> return (h::t) <|> return t
  | none := filter_hyps_to_type t
  end

meta def get_restrict_type (e : expr) : tactic expr :=
do m ← mk_mvar,
   unify `(some %%m : option Type) e,
   instantiate_mvars m

end
end linarith

open linarith tactic
meta def tactic.linarith (reduce_semi : bool) (only_on : bool) (hyps : list pexpr)
  (cfg : linarith_config := {}) : tactic unit :=
do t ← target,
-- if the target is an equality, we run `linarith` twice, to prove ≤ and ≥.
if t.is_eq.is_some then
  linarith_trace "target is an equality: splitting" >>
    seq' (applyc ``eq_of_not_lt_of_not_gt) tactic.linarith else
do when cfg.split_hypotheses (linarith_trace "trying to split hypotheses" >> try auto.split_hyps),
/- If we are proving a comparison goal (and not just `false`), we consider the type of the
   elements in the comparison to be the "preferred" type. That is, if we find comparison
   hypotheses in multiple types, we will run `linarith` on the goal type first.
   In this case we also recieve a new variable from moving the goal to a hypothesis.
   Otherwise, there is no preferred type and no new variable; we simply change the goal to `false`. -/
   pref_type_and_new_var_from_tgt ← apply_contr_lemma,
   when pref_type_and_new_var_from_tgt.is_none $
     if cfg.exfalso then linarith_trace "using exfalso" >> exfalso
     else fail "linarith failed: target is not a valid comparison",
   let cfg := cfg.update_reducibility reduce_semi,
   let (pref_type, new_var) := pref_type_and_new_var_from_tgt.elim (none, none) (λ ⟨a, b⟩, (some a, some b)),
   -- set up the list of hypotheses, considering the `only_on` and `restrict_type` options
   hyps ← hyps.mmap i_to_expr,
   hyps ← if only_on then return (new_var.elim [] singleton ++ hyps) else (++ hyps) <$> local_context,
   hyps ← (do t ← get_restrict_type cfg.restrict_type_reflect, filter_hyps_to_type t hyps) <|> return hyps,
   linarith_trace_proofs "linarith is running on the following hypotheses:" hyps,
   run_linarith_on_pfs cfg hyps pref_type
