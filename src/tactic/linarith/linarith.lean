/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import tactic.ring
import tactic.linarith.preprocessing
import tactic.linarith.elimination
import tactic.linarith.parsing
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
### Verification

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
`mk_lt_zero_pf coeffs pfs` takes a list of proofs of the form `tᵢ Rᵢ 0`,
paired with coefficients `cᵢ`.
It produces a proof that `∑cᵢ * tᵢ R 0`, where `R` is as strong as possible.
-/
meta def mk_lt_zero_pf : list (expr × ℕ) → tactic expr
| [] := fail "no linear hypotheses found"
| [(h, c)] := prod.snd <$> mk_single_comp_zero_pf c h
| ((h, c)::t) :=
  do (iq, h') ← mk_single_comp_zero_pf c h,
     prod.snd <$> t.mfoldl (λ pr ce, mk_lt_zero_pf_aux pr.1 pr.2 ce.1 ce.2) (iq, h')

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

An oracle is used to search for a certificate of unsatisfiability.
In the current implementation, this is the Fourier Motzkin elimination routine in
`elimination.lean`, but other oracles could easily be swapped in.

The returned certificate is a map `m` from hypothesis indices to natural number coefficients.
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
-/
meta def prove_false_by_linarith (cfg : linarith_config) : list expr → tactic unit
| [] := fail "no args to linarith"
| l@(h::t) := do
    -- for the elimination to work properly, we must add a proof of `-1 < 0` to the list,
    -- along with negated equality proofs.
    l' ← add_neg_eq_pfs l,
    hz ← ineq_prf_tp h >>= mk_neg_one_lt_zero_pf,
    let inputs := hz::l',
    -- perform the elimination and fail if no contradiction is found.
    (comps, vars) ← linear_forms_and_vars cfg.transparency inputs,
    certificate ← fourier_motzkin.produce_certificate comps vars
      | fail "linarith failed to find a contradiction",
    linarith_trace "linarith has found a contradiction",
    let enum_inputs := inputs.enum,
    -- construct a list pairing nonzero coeffs with the proof of their corresponding comparison
    let zip := enum_inputs.filter_map $ λ ⟨n, e⟩, prod.mk e <$> certificate.find n,
    mls ← zip.mmap (λ ⟨e, n⟩, do e ← term_of_ineq_prf e, return (mul_expr n e)),
    -- `sm` is the sum of input terms, scaled to cancel out all variables.
    sm ← to_expr $ add_exprs mls,
    pformat! "The expression\n  {sm}\nshould be both 0 and negative" >>= linarith_trace,
    -- we prove that `sm = 0`, typically with `ring`.
    sm_eq_zero ← prove_eq_zero_using cfg.discharger sm,
    linarith_trace "We have proved that it is zero",
    -- we also prove that `sm < 0`.
    sm_lt_zero ← mk_lt_zero_pf zip,
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

/--
`apply_contr_lemma` inspects the target to see if it can be moved to a hypothesis by negation.
For example, a goal `⊢ a ≤ b` can become `a > b ⊢ false`.
If this is the case, it applies the appropriate lemma and introduces the new hypothesis.
It returns the type of the terms in the comparison (e.g. the type of `a` and `b` above) and the
newly introduced local constant.
Otherwise returns `none`.
-/
meta def apply_contr_lemma : tactic (option (expr × expr)) :=
do t ← target,
   match get_contr_lemma_name_and_type t with
   | some (nm, tp) := do applyc nm, v ← intro1, return $ some (tp, v)
   | none := return none
   end

/--
`partition_by_type l` takes a list `l` of proofs of comparisons. It sorts these proofs by
the type of the variables in the comparison, e.g. `(a : ℚ) < 1` and `(b : ℤ) > c` will be separated.
Returns a map from a type to a list of comparisons over that type.
-/
meta def partition_by_type (l : list expr) : tactic (rb_lmap expr expr) :=
l.mfoldl (λ m h, do tp ← ineq_prf_tp h, return $ m.insert tp h) mk_rb_map

/--
Given a list `ls` of lists of proofs of comparisons, `try_linarith_on_lists cfg ls` will try to
prove `false` by calling `linarith` on each list in succession. It will stop at the first proof of
`false`, and fail if no contradiction is found with any list.
-/
meta def try_linarith_on_lists (cfg : linarith_config) (ls : list (list expr)) : tactic unit :=
(first $ ls.map $ prove_false_by_linarith cfg) <|> fail "linarith failed to find a contradiction"

/--
Given a list `hyps` of proofs of comparisons, `run_linarith_on_pfs cfg hyps pref_type`
preprocesses `hyps` according to the list of preprocessors in `cfg`.
It then partitions the resulting list of hypotheses by type, and runs `linarith` on each class
in the partition.

If `pref_type` is given, it will first use the class of proofs of comparisons over that type.
-/
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

/--
`filter_hyps_to_type restr_type hyps` takes a list of proofs of comparisons `hyps`, and filters it
to only those that are comparisons over the type `restr_type`.
-/
meta def filter_hyps_to_type (restr_type : expr) (hyps : list expr) : tactic (list expr) :=
hyps.mfilter $ λ h, do
  ht ← infer_type h,
  match get_contr_lemma_name_and_type ht with
  | some (_, htype) := succeeds $ unify htype restr_type
  | none := return ff
  end

/-- A hack to allow users to write `{restr_type := ℚ}` in configuration structures. -/
meta def get_restrict_type (e : expr) : tactic expr :=
do m ← mk_mvar,
   unify `(some %%m : option Type) e,
   instantiate_mvars m

end
end linarith

open linarith tactic

/--
`linarith reduce_semi only_on hyps cfg` tries to close the goal using linear arithmetic. It fails
if it does not succeed at doing this.

* If `reduce_semi` is true, it will unfold semireducible definitions when trying to match atomic
expressions.
* `hyps` is a list of proofs of comparisons to include in the search.
* If `only_on` is true, the search will be restricted to `hyps`. Otherwise it will use all
  comparisons in the local context.
-/
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
