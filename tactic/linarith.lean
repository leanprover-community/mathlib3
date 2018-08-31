/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

A tactic for discharging linear arithmetic goals using Fourier-Motzkin elimination.

`linarith` is (in principle) complete for ℚ and ℝ. It is not complete for non-dense orders, i.e. ℤ.

@TODO: investigate storing comparisons in a list instead of a set, for possible efficiency gains
@TODO: (partial) support for ℕ by casting to ℤ 
@TODO: alternative discharger to `ring`
@TODO: support rational coefficients
-/

import tactic.ring data.nat.gcd data.list.basic meta.rb_map 

open native 
namespace linarith

section lemmas

lemma eq_of_eq_of_eq {α} [ordered_semiring α] {a b : α} (ha : a = 0) (hb : b = 0) : a + b = 0 :=
by simp *

lemma le_of_eq_of_le {α} [ordered_semiring α] {a b : α} (ha : a = 0) (hb : b ≤ 0) : a + b ≤ 0 :=
by simp *

lemma lt_of_eq_of_lt {α} [ordered_semiring α] {a b : α} (ha : a = 0) (hb : b < 0) : a + b < 0 :=
by simp *

lemma le_of_le_of_eq {α} [ordered_semiring α] {a b : α} (ha : a ≤ 0) (hb : b = 0) : a + b ≤ 0 :=
by simp *

lemma lt_of_lt_of_eq {α} [ordered_semiring α] {a b : α} (ha : a < 0) (hb : b = 0) : a + b < 0 :=
by simp *

lemma mul_neg {α} [ordered_ring α] {a b : α} (ha : a < 0) (hb : b > 0) : b * a < 0 :=
have (-b)*a > 0, from mul_pos_of_neg_of_neg (neg_neg_of_pos hb) ha,
neg_of_neg_pos (by simpa)

lemma mul_nonpos {α} [ordered_ring α] {a b : α} (ha : a ≤ 0) (hb : b > 0) : b * a ≤ 0 :=
have (-b)*a ≥ 0, from mul_nonneg_of_nonpos_of_nonpos (le_of_lt (neg_neg_of_pos hb)) ha,
nonpos_of_neg_nonneg (by simp at this; exact this)

lemma mul_eq {α} [ordered_semiring α] {a b : α} (ha : a = 0) (hb : b > 0) : b * a = 0 :=
by simp *

lemma eq_of_not_lt_of_not_gt {α} [linear_order α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b :=
le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)

end lemmas 

section datatypes

@[derive decidable_eq]
inductive ineq
| eq | le | lt

open ineq 

def ineq.max : ineq → ineq → ineq
| eq a := a 
| le a := a 
| lt a := lt 

def ineq.is_lt : ineq → ineq → bool 
| eq le := tt
| eq lt := tt 
| le lt := tt 
| _ _ := ff

def ineq.to_string : ineq → string 
| eq := "="
| le := "≤"
| lt := "<"

instance : has_to_string ineq := ⟨ineq.to_string⟩

/--
  The main datatype for FM elimination.
  Variables are represented by natural numbers, each of which has an integer coefficient.
  Index 0 is reserved for constants, i.e. `coeffs.find 0` is the coefficient of 1.
  The represented term is coeffs.keys.sum (λ i, coeffs.find i * Var[i]).
  str determines the direction of the comparison -- is it < 0, ≤ 0, or = 0?
-/
meta structure comp :=
(str : ineq)
(coeffs : rb_map ℕ int)

meta instance : inhabited comp := ⟨⟨ineq.eq, mk_rb_map⟩⟩

meta inductive comp_source 
| assump : ℕ → comp_source
| add : comp_source → comp_source → comp_source
| scale : ℕ → comp_source → comp_source

meta def comp_source.flatten : comp_source → rb_map ℕ ℕ
| (comp_source.assump n) := mk_rb_map.insert n 1
| (comp_source.add c1 c2) := (comp_source.flatten c1).add (comp_source.flatten c2)
| (comp_source.scale n c) := (comp_source.flatten c).map (λ v, v * n)

meta def comp_source.to_string : comp_source → string 
| (comp_source.assump e) := to_string e
| (comp_source.add c1 c2) := comp_source.to_string c1 ++ " + " ++ comp_source.to_string c2
| (comp_source.scale n c) := to_string n ++ " * " ++ comp_source.to_string c 

meta instance comp_source.has_to_format : has_to_format (comp_source) :=
⟨λ a, comp_source.to_string a⟩

meta structure pcomp :=
(c : comp)
(src : comp_source)

def alist_lt : list (ℕ × ℤ) → list (ℕ × ℤ) → bool 
| [] [] := ff
| [] (_::_) := tt
| (_::_) [] := ff
| ((a1, z1)::t1) ((a2, z2)::t2) :=
    (a1 < a2) || ((a1 = a2) && ((z1 < z2) || (z1 = z2 ∧ alist_lt t1 t2)))  

meta def map_lt (m1 m2 : rb_map ℕ int) : bool :=
alist_lt m1.to_list m2.to_list

-- make more efficient
meta def comp.lt (c1 c2 : comp) : bool :=
(c1.str.is_lt c2.str) || (map_lt c1.coeffs c2.coeffs) 

meta instance comp.has_lt : has_lt comp := ⟨λ a b, comp.lt a b⟩
meta instance pcomp.has_lt : has_lt pcomp := ⟨λ p1 p2, p1.c < p2.c⟩
meta instance pcomp.has_lt_dec : decidable_rel ((<) : pcomp → pcomp → Prop) := by apply_instance

meta def comp.coeff_of (c : comp) (a : ℕ) : ℤ :=
c.coeffs.zfind a

meta def comp.scale (c : comp) (n : ℕ) : comp :=
{ c with coeffs := c.coeffs.map ((*) (n : ℤ)) }

meta def comp.add (c1 c2 : comp) : comp :=
⟨c1.str.max c2.str, c1.coeffs.add c2.coeffs⟩

meta def pcomp.scale (c : pcomp) (n : ℕ) : pcomp := 
⟨c.c.scale n, comp_source.scale n c.src⟩ 

meta def pcomp.add (c1 c2 : pcomp) : pcomp :=
⟨c1.c.add c2.c, comp_source.add c1.src c2.src⟩

meta instance pcomp.to_format : has_to_format pcomp :=
⟨λ p, to_fmt p.c.coeffs ++ to_string p.c.str ++ "0"⟩

meta instance comp.to_format : has_to_format comp :=
⟨λ p, to_fmt p.coeffs⟩

end datatypes

section fm_elim

/-- If c1 and c2 both contain variable a with opposite coefficients,
   produces v1, v2, and c such that a has been cancelled in c := v1*c1 + v2*c2 -/
meta def elim_var (c1 c2 : comp) (a : ℕ) : option (ℕ × ℕ × comp) :=
let v1 := c1.coeff_of a,
    v2 := c2.coeff_of a in
if v1 * v2 < 0 then 
  let vlcm :=  nat.lcm v1.nat_abs v2.nat_abs,
      v1' := vlcm / v1.nat_abs,
      v2' := vlcm / v2.nat_abs in
  some ⟨v1', v2', comp.add (c1.scale v1') (c2.scale v2')⟩ 
else none

meta def pelim_var (p1 p2 : pcomp) (a : ℕ) : option pcomp := 
do (n1, n2, c) ← elim_var p1.c p2.c a,
   return ⟨c, comp_source.add (p1.src.scale n1) (p2.src.scale n2)⟩

meta def comp.is_contr (c : comp) : bool := c.coeffs.keys = [] ∧ c.str = ineq.lt

meta def pcomp.is_contr (p : pcomp) : bool := p.c.is_contr

meta def elim_with_set (a : ℕ) (p : pcomp) (comps : rb_set pcomp) : rb_set pcomp :=
if ¬ p.c.coeffs.contains a then mk_rb_set.insert p else 
comps.fold mk_rb_set $ λ pc s, 
match pelim_var p pc a with 
| some pc := s.insert pc
| none := s 
end

meta def find_contr_in_set (comps : rb_set pcomp) : option pcomp :=
match (comps.filter pcomp.is_contr).keys with 
| [] := none 
| (h::t) := some h
end

/-- 
  The state for the elimination monad.
    vars: the set of variables present in comps
    comps: a set of comparisons
    inputs: a set of pairs of exprs (t, pf), where t is a term and pf is a proof that t {<, ≤, =} 0,
      indexed by ℕ.
    has_false: stores a pcomp of 0 < 0 if one has been found
    TODO: is it more efficient to store comps as a list, to avoid comparisons?
-/
meta structure linarith_structure :=
(vars : rb_set ℕ)
(comps : rb_set pcomp)
(inputs : rb_map ℕ (expr × expr)) -- first is term, second is proof of comparison
(has_false : option pcomp) 

@[reducible] meta def linarith_monad := state (linarith_structure)

meta instance : monad (linarith_monad) := state_t.monad 

meta def get_var_list : linarith_monad (list ℕ) :=
⟨λ s, ⟨s.vars.to_list, s⟩⟩

meta def get_vars : linarith_monad (rb_set ℕ) :=
⟨λ s, ⟨s.vars, s⟩⟩

meta def get_comps : linarith_monad (rb_set pcomp) :=
⟨λ s, ⟨s.comps, s⟩⟩

meta def get_contr : linarith_monad (option pcomp) :=
linarith_structure.has_false <$> get

meta def is_contr : linarith_monad bool :=
option.is_some <$> get_contr 

meta def assert_contr (p : pcomp) : linarith_monad unit :=
⟨λ s, ((), { s with has_false := some p })⟩

meta def update_vars_and_comps (vars : rb_set ℕ) (comps : rb_set pcomp) : linarith_monad unit := 
⟨λ s, ⟨(), ⟨vars, comps, s.inputs, s.has_false⟩⟩⟩

-- TODO: possible to short circuit earlier
meta def monad.elim_var (a : ℕ) : linarith_monad unit :=
do vs ← get_vars, isc ← is_contr,
   if (¬ vs.contains a) ∨ isc then return () else
do comps ← get_comps,
   let cs' := comps.fold mk_rb_set (λ p s, s.union (elim_with_set a p comps)),
   match find_contr_in_set cs' with 
   | none := update_vars_and_comps (vs.erase a) cs'
   | some p := assert_contr p 
   end

meta def elim_all_vars : linarith_monad unit := 
do vs ← get_var_list,
   vs.mfoldl (λ _ a, monad.elim_var a) ()

end fm_elim

section parse

open ineq tactic 

meta def map_of_expr_mul_aux (c1 c2 : rb_map ℕ ℤ) : option (rb_map ℕ ℤ) :=
match c1.keys, c2.keys with 
| [0], _ := some $ c2.scale (c1.zfind 0)
| _, [0] := some $ c1.scale (c2.zfind 0)
| _, _ := none
end

/--
  Turns an expression into a map from ℕ to ℤ, for use in a comp object.
    The rb_map expr ℕ argument identifies which expressions have already been assigned numbers.
    The ℕ argument identifies the next unused number.
    Returns a new map and new max.
-/
meta def map_of_expr : rb_map expr ℕ → ℕ → expr → option (rb_map expr ℕ × ℕ × rb_map ℕ ℤ)
| m max `(%%e1 * %%e2) := 
   do (m', max', comp1) ← map_of_expr m max e1, 
      (m', max', comp2) ← map_of_expr m' max' e2,
      mp ← map_of_expr_mul_aux comp1 comp2,
      return (m', max', mp)
| m max `(%%e1 + %%e2) :=
   do (m', max', comp1) ← map_of_expr m max e1, 
      (m', max', comp2) ← map_of_expr m' max' e2,
      return (m', max', comp1.add comp2)
| m max `(%%e1 - %%e2) :=
   do (m', max', comp1) ← map_of_expr m max e1, 
      (m', max', comp2) ← map_of_expr m' max' e2,
      return (m', max', comp1.add (comp2.scale (-1)))
| m max `(-%%e) := do (m', max', comp) ← map_of_expr m max e, return (m', max', comp.scale (-1))
| m max e := 
  match e.to_int, m.find e with
  | some z, _ := return ⟨m, max, mk_rb_map.insert 0 z⟩ 
  | none, some k := return (m, max, mk_rb_map.insert k 1) 
  | none, none := return (m.insert e max, max + 1, mk_rb_map.insert max 1)
  end

meta def parse_into_comp_and_expr : expr → option (ineq × expr)
| `(%%e < 0) := (ineq.lt, e)
| `(%%e ≤ 0) := (ineq.le, e)
| `(%%e = 0) := (ineq.eq, e) 
| _ := none

meta def to_comp (e : expr) (m : rb_map expr ℕ) (max : ℕ) : option (comp × rb_map expr ℕ × ℕ) :=
do (iq, e) ← parse_into_comp_and_expr e,
   (m', max', comp') ← map_of_expr m max e,
   return ⟨⟨iq, comp'⟩, m', max'⟩

meta def to_comp_fold : rb_map expr ℕ → ℕ → list expr → 
      (list (option comp) × rb_map expr ℕ × ℕ)
| m max [] := ([], m, max)
| m max (h::t) := 
  match to_comp h m max with 
  | some (c, m', max') := let (l, mp, n) := to_comp_fold m' max' t in (c::l, mp, n)
  | none := let (l, mp, n) := to_comp_fold m max t in (none::l, mp, n)
  end

def reduce_pair_option {α β} : list (α × option β) → list (α × β)
| [] := []
| ((a,none)::t) := reduce_pair_option t 
| ((a,some b)::t) := (a,b)::reduce_pair_option t 

/--
  Takes a list of proofs of props of the form t {<, ≤, =} 0, and creates a linarith_structure.
-/
meta def mk_linarith_structure (l : list expr) : tactic linarith_structure := 
do pftps ← l.mmap infer_type,
   let (l', map, max) := to_comp_fold mk_rb_map 1 pftps,
   let lz := reduce_pair_option ((l.zip pftps).zip l'),
   let prmap := rb_map.of_list $ (list.range lz.length).map (λ n, (n, (lz.inth n).1)),
   let vars : rb_set ℕ := rb_map.of_list $ (list.range (max)).map (λ k, (k, ())),
   let pc : rb_set pcomp := 
     rb_map.of_list $ (list.range lz.length).map (λ n, (⟨(lz.inth n).2, comp_source.assump n⟩, ())),
   return ⟨vars, pc, prmap, none⟩ 

end parse 

section prove
open ineq tactic 

meta def nat.to_pexpr : ℕ → pexpr
| 0 := ``(0)
| 1 := ``(1)
| n := if n % 2 = 0 then ``(bit0 %%(nat.to_pexpr (n/2))) else ``(bit1 %%(nat.to_pexpr (n/2)))

meta def mul_expr (n : ℕ) (e : expr) : pexpr :=
``(%%(nat.to_pexpr n) * %%e)

meta def add_exprs_aux : pexpr → list pexpr → pexpr 
| p [] := p
| p [a] := ``(%%p + %%a)
| p (h::t) := add_exprs_aux ``(%%p + %%h) t 

meta def add_exprs : list pexpr → pexpr 
| [] := ``(0)
| (h::t) := add_exprs_aux h t

meta def find_contr (m : rb_set pcomp) : option pcomp :=
m.keys.find (λ p, p.c.is_contr)

meta def ineq_const_mul_nm : ineq → name 
| lt := ``mul_neg
| le := ``mul_nonpos
| eq := ``mul_eq

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

meta def mk_lt_zero_pf_aux (c : ineq) (pf npf : expr) (coeff : ℕ) : tactic (ineq × expr) :=
do tp ← infer_type npf,
   some (iq, e) ← return $ parse_into_comp_and_expr tp,
   nm ← resolve_name (ineq_const_mul_nm iq),
   if ¬ coeff = 0 then do
     h' ← to_expr ``(%%nm.mk_explicit _ _ _ %%(nat.to_pexpr coeff) %%npf (by norm_num)),
     (nm, niq) ← return $ ineq_const_nm c iq,
     e' ← mk_app nm [pf, h'],
     return (niq, e')
   else do
     h' ← to_expr ``(zero_mul %%e),
     (nm, niq) ← return $ ineq_const_nm c eq,
     e' ← mk_app nm [pf, h'],
     return (niq, e')

/--
  TODO: clean this up.
  Takes a list of coefficients [c] and list of expressions, of equal length.
  Each expression is a proof of a prop of the form t {<, ≤, =} 0.
  Produces a proof that the sum of (c*t) < 0.
  At least one expression should be a <, otherwise this doesn't work.
-/
meta def mk_lt_zero_pf : list ℕ → list expr → tactic expr 
| _ [] := fail "no linear hypotheses found"
| [c] [h] := 
  do tp ← infer_type h,
   some (iq, e) ← return $ parse_into_comp_and_expr tp,
   match iq with 
   | ineq.lt := to_expr ``(@mul_neg _ _ _ %%(nat.to_pexpr c) %%e (by norm_num)) ff
   | _ := fail "error in linarith.mk_lt_zero_pf : not an lt"
   end  
| (c::ct) (h::t) := 
  do tp ← infer_type h,
   some (iq, e) ← return $ parse_into_comp_and_expr tp,
   if c = 0 then 
     do h' ← to_expr ``(zero_mul %%e),
     (iq, e') ← (ct.zip t).mfoldl (λ pr ce, mk_lt_zero_pf_aux pr.1 pr.2 ce.2 ce.1) (eq, h'),
     match iq with 
     | ineq.lt := return e' 
     | _ := fail "error in linarith.mk_lt_zero_pf : not an lt"
     end
   else      
     do nm ← resolve_name (ineq_const_mul_nm iq), 
        h' ← to_expr ``(%%nm.mk_explicit _ _ _ %%(nat.to_pexpr c) %%h (by norm_num)) ff, 
       (iq, e') ← (ct.zip t).mfoldl (λ pr ce, mk_lt_zero_pf_aux pr.1 pr.2 ce.2 ce.1) (iq, h'),
       match iq with 
       | ineq.lt := return e' 
       | _ := fail "the sum isn't a lt"
       end  
| _ _ := fail "not enough args to mk_lt_zero_pf"

meta def get_rel_sides : expr → tactic (expr × expr)
| `(%%a < %%b) := return (a, b)
| `(%%a ≤ %%b) := return (a, b)
| `(%%a = %%b) := return (a, b)
| _ := failed

meta def term_of_ineq_prf (prf : expr) : tactic expr :=
do (lhs, _) ← infer_type prf >>= get_rel_sides,
   return lhs

meta structure linarith_config :=
(discharger : tactic unit := `[ring])
(restrict_type : option Type := none)
(restrict_type_reflect : reflected restrict_type . apply_instance)

meta def ineq_pf_tp (pf : expr) : tactic expr :=
do (_, z) ← infer_type pf >>= get_rel_sides,
   infer_type z

meta def mk_neg_one_lt_zero_pf (tp : expr) : tactic expr :=
to_expr ``((neg_neg_of_pos zero_lt_one : -1 < (0 : %%tp)))

/--
  Takes a list of proofs of propositions of the form t {<, ≤, =} 0,
  and tries to prove the goal `false`.
-/
meta def prove_false_by_linarith1 (cfg : linarith_config) : list expr → tactic unit 
| [] := fail "no args to linarith"
| l@(h::t) :=
do extp ← match cfg.restrict_type with 
          | none := do (_, z) ← infer_type h >>= get_rel_sides, infer_type z
          | some rtp := 
             do m ← mk_mvar,
                unify `(some %%m : option Type) cfg.restrict_type_reflect,
                return m
          end,
   hz ← mk_neg_one_lt_zero_pf extp, 
   l' ← if cfg.restrict_type.is_some then 
           l.mfilter (λ e, (ineq_pf_tp e >>= is_def_eq extp >> return tt) <|> return ff)
        else return l,
   struct ← mk_linarith_structure (hz::l'),
   let e : linarith_structure := (elim_all_vars.run struct).2,
   let contr := e.has_false,
   guard contr.is_some <|> fail "linarith failed to find a contradiction",
   some contr ← return $ contr,
   let coeffs := e.inputs.keys.map (λ k, (contr.src.flatten.ifind k)),
   let pfs : list expr := e.inputs.keys.map (λ k, (e.inputs.ifind k).1), 
   let zip := (coeffs.zip pfs).filter (λ pr, pr.1 ≠ 0),
   coeffs ← return $ zip.map prod.fst,
   pfs ← return $ zip.map prod.snd,
   mls ← zip.mmap (λ pr, do e ← term_of_ineq_prf pr.2, return (mul_expr pr.1 e)),
   sm ← to_expr $ add_exprs mls,
   tgt ← to_expr ``(%%sm = 0),
   (a, b) ← solve_aux tgt (cfg.discharger >> done),
   pf ← mk_lt_zero_pf coeffs pfs,
   pftp ← infer_type pf,
   (_, nep, _) ← rewrite_core b pftp,
   pf' ← mk_eq_mp nep pf,
   mk_app `lt_irrefl [pf'] >>= exact 

meta def rearr_comp (prf : expr) : expr → tactic expr 
| `(%%a ≤ 0) := return prf 
| `(%%a < 0) := return prf 
| `(%%a = 0) := return prf 
| `(%%a ≥ 0) := to_expr ``(neg_nonpos.mpr %%prf) 
| `(%%a > 0) := to_expr ``(neg_neg_of_pos %%prf)
| `(%%a ≤ %%b) := to_expr ``(sub_nonpos.mpr %%prf)
| `(%%a < %%b) := to_expr ``(sub_neg_of_lt %%prf)
| `(%%a = %%b) := to_expr ``(sub_eq_zero.mpr %%prf)
| `(%%a > %%b) := to_expr ``(sub_neg_of_lt %%prf)
| `(%%a ≥ %%b) := to_expr ``(sub_nonpos.mpr %%prf)
| _ := fail "couldn't rearrange comp"

meta def norm_hyp (h : expr) : tactic expr :=
do htp ← infer_type h,
   rearr_comp h htp

meta def get_contr_lemma_name : expr → tactic name
| `(%%a < %%b) := return `lt_of_not_ge
| `(%%a ≤ %%b) := return `le_of_not_gt
| `(%%a = %%b) := return ``eq_of_not_lt_of_not_gt
| `(%%a ≥ %%b) := return `le_of_not_gt
| `(%%a > %%b) := return `lt_of_not_ge
| _ := fail "target type not supported by linarith"

/--
  Takes a list of proofs of propositions.
  Filters out the proofs of linear (in)equalities,
  and tries to use them to prove `false`.
-/
meta def prove_false_by_linarith (cfg : linarith_config) (l : list expr) : tactic unit :=
do ls ← l.mmap (λ h, (do s ← norm_hyp h, return (some s)) <|> return none),
   prove_false_by_linarith1 cfg ls.reduce_option

end prove

end linarith

section
open tactic linarith

open lean lean.parser interactive tactic interactive.types
local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def linarith.interactive_aux (cfg : linarith_config) : 
     parse ident* → (parse (tk "using" *> pexpr_list)?) → tactic unit
| l (some pe) := pe.mmap (λ p, i_to_expr p >>= note_anon) >> linarith.interactive_aux l none
| [] none := 
  do t ← target,
     if t = `(false) then local_context >>= prove_false_by_linarith cfg
     else do nm ← get_contr_lemma_name t, seq (applyc nm) (intro1 >> linarith.interactive_aux [] none)
| ls none := (ls.mmap get_local) >>= prove_false_by_linarith cfg

/--
  If the goal is `false`, tries to prove it by linear arithmetic on hypotheses.
  If the goal is a linear (in)equality, tries to prove it by contradiction.
  `linarith` will use all relevant hypotheses in the local context.
  `linarith h1 h2 h3` will only use hypotheses h1, h2, h3.
  `linarith using [t1, t2, t3]` will add proof terms t1, t2, t3 to the local context.
-/
meta def tactic.interactive.linarith (ids : parse (many ident)) 
     (using_hyps : parse (tk "using" *> pexpr_list)?) (cfg : linarith_config := {}) : tactic unit :=
linarith.interactive_aux cfg ids using_hyps

end

#check le_antisymm