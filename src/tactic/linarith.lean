/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

A tactic for discharging linear arithmetic goals using Fourier-Motzkin elimination.

`linarith` is (in principle) complete for ℚ and ℝ. It is not complete for non-dense orders, i.e. ℤ.

@TODO: investigate storing comparisons in a list instead of a set, for possible efficiency gains
@TODO: delay proofs of denominator normalization and nat casting until after contradiction is found
-/

import tactic.ring data.nat.gcd data.list.basic meta.rb_map

meta def nat.to_pexpr : ℕ → pexpr
| 0 := ``(0)
| 1 := ``(1)
| n := if n % 2 = 0 then ``(bit0 %%(nat.to_pexpr (n/2))) else ``(bit1 %%(nat.to_pexpr (n/2)))

open native
namespace linarith

section lemmas

lemma int.coe_nat_bit0 (n : ℕ) : (↑(bit0 n : ℕ) : ℤ) = bit0 (↑n : ℤ) := by simp [bit0]
lemma int.coe_nat_bit1 (n : ℕ) : (↑(bit1 n : ℕ) : ℤ) = bit1 (↑n : ℤ) := by simp [bit1, bit0]
lemma int.coe_nat_bit0_mul (n : ℕ) (x : ℕ) : (↑(bit0 n * x) : ℤ) = (↑(bit0 n) : ℤ) * (↑x : ℤ) := by simp
lemma int.coe_nat_bit1_mul (n : ℕ) (x : ℕ) : (↑(bit1 n * x) : ℤ) = (↑(bit1 n) : ℤ) * (↑x : ℤ) := by simp
lemma int.coe_nat_one_mul (x : ℕ) : (↑(1 * x) : ℤ) = 1 * (↑x : ℤ) := by simp
lemma int.coe_nat_zero_mul (x : ℕ) : (↑(0 * x) : ℤ) = 0 * (↑x : ℤ) := by simp
lemma int.coe_nat_mul_bit0 (n : ℕ) (x : ℕ) : (↑(x * bit0 n) : ℤ) = (↑x : ℤ) * (↑(bit0 n) : ℤ) := by simp
lemma int.coe_nat_mul_bit1 (n : ℕ) (x : ℕ) : (↑(x * bit1 n) : ℤ) = (↑x : ℤ) * (↑(bit1 n) : ℤ) := by simp
lemma int.coe_nat_mul_one (x : ℕ) : (↑(x * 1) : ℤ) = (↑x : ℤ) * 1 := by simp
lemma int.coe_nat_mul_zero (x : ℕ) : (↑(x * 0) : ℤ) = (↑x : ℤ) * 0 := by simp

lemma nat_eq_subst {n1 n2 : ℕ} {z1 z2 : ℤ} (hn : n1 = n2) (h1 : ↑n1 = z1) (h2 : ↑n2 = z2) : z1 = z2 :=
by simpa [eq.symm h1, eq.symm h2, int.coe_nat_eq_coe_nat_iff]

lemma nat_le_subst {n1 n2 : ℕ} {z1 z2 : ℤ} (hn : n1 ≤ n2) (h1 : ↑n1 = z1) (h2 : ↑n2 = z2) : z1 ≤ z2 :=
by simpa [eq.symm h1, eq.symm h2, int.coe_nat_le]

lemma nat_lt_subst {n1 n2 : ℕ} {z1 z2 : ℤ} (hn : n1 < n2) (h1 : ↑n1 = z1) (h2 : ↑n2 = z2) : z1 < z2 :=
by simpa [eq.symm h1, eq.symm h2, int.coe_nat_lt]

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

lemma add_subst {α} [ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) :
      n * (e1 + e2) = t1 + t2 := by simp [left_distrib, *]

lemma sub_subst {α} [ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) :
      n * (e1 - e2) = t1 - t2 := by simp [left_distrib, *]

lemma neg_subst {α} [ring α] {n e t : α} (h1 : n * e = t) : n * (-e) = -t := by simp *

private meta def apnn : tactic unit := `[norm_num]

lemma mul_subst {α} [comm_ring α] {n1 n2 k e1 e2 t1 t2 : α} (h1 : n1 * e1 = t1) (h2 : n2 * e2 = t2)
     (h3 : n1*n2 = k . apnn) : k * (e1 * e2) = t1 * t2 :=
have h3 : n1 * n2 = k, from h3,
by rw [←h3, mul_comm n1, mul_assoc n2, ←mul_assoc n1, h1, ←mul_assoc n2, mul_comm n2, mul_assoc, h2] -- OUCH

lemma div_subst {α} [field α] {n1 n2 k e1 e2 t1 : α} (h1 : n1 * e1 = t1) (h2 : n2 / e2 = 1) (h3 : n1*n2 = k) :
      k * (e1 / e2) = t1 :=
by rw [←h3, mul_assoc, mul_div_comm, h2, ←mul_assoc, h1, mul_comm, one_mul]

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

meta instance comp_source.has_to_format : has_to_format comp_source :=
⟨λ a, comp_source.to_string a⟩

meta structure pcomp :=
(c : comp)
(src : comp_source)

meta def map_lt (m1 m2 : rb_map ℕ int) : bool :=
list.lex (prod.lex (<) (<)) m1.to_list m2.to_list

-- make more efficient
meta def comp.lt (c1 c2 : comp) : bool :=
(c1.str.is_lt c2.str) || (c1.str = c2.str) && map_lt c1.coeffs c2.coeffs

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

meta def comp.is_contr (c : comp) : bool := c.coeffs.empty ∧ c.str = ineq.lt

meta def pcomp.is_contr (p : pcomp) : bool := p.c.is_contr

meta def elim_with_set (a : ℕ) (p : pcomp) (comps : rb_set pcomp) : rb_set pcomp :=
if ¬ p.c.coeffs.contains a then mk_rb_set.insert p else
comps.fold mk_rb_set $ λ pc s,
match pelim_var p pc a with
| some pc := s.insert pc
| none := s
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

@[reducible] meta def linarith_monad :=
state_t linarith_structure (except_t pcomp id)

meta instance : monad linarith_monad := state_t.monad
meta instance : monad_except pcomp linarith_monad :=
state_t.monad_except pcomp

meta def get_vars : linarith_monad (rb_set ℕ) :=
linarith_structure.vars <$> get

meta def get_var_list : linarith_monad (list ℕ) :=
rb_set.to_list <$> get_vars

meta def get_comps : linarith_monad (rb_set pcomp) :=
linarith_structure.comps <$> get

meta def validate : linarith_monad unit :=
do ⟨_, comps⟩ ← get,
match comps.to_list.find (λ p : pcomp, p.is_contr) with
| none := return ()
| some c := throw c
end

meta def update (vars : rb_set ℕ) (comps : rb_set pcomp) : linarith_monad unit :=
state_t.put ⟨vars, comps⟩ >> validate

meta def monad.elim_var (a : ℕ) : linarith_monad unit :=
do vs ← get_vars,
   when (vs.contains a) $
do comps ← get_comps,
   let cs' := comps.fold mk_rb_set (λ p s, s.union (elim_with_set a p comps)),
   update (vs.erase a) cs'

meta def elim_all_vars : linarith_monad unit :=
get_var_list >>= list.mmap' monad.elim_var

end fm_elim

section parse

open ineq tactic

meta def map_of_expr_mul_aux (c1 c2 : rb_map ℕ ℤ) : option (rb_map ℕ ℤ) :=
match c1.keys, c2.keys with
| [0], _ := some $ c2.scale (c1.zfind 0)
| _, [0] := some $ c1.scale (c2.zfind 0)
| [], _ := some mk_rb_map
| _, [] := some mk_rb_map
| _, _ := none
end

meta def list.mfind {α} (tac : α → tactic unit) : list α → tactic α
| [] := failed
| (h::t) := tac h >> return h <|> list.mfind t

meta def rb_map.find_defeq (red : transparency) {v} (m : expr_map v) (e : expr) : tactic v :=
prod.snd <$> list.mfind (λ p, is_def_eq e p.1 red) m.to_list

/--
  Turns an expression into a map from ℕ to ℤ, for use in a comp object.
    The expr_map ℕ argument identifies which expressions have already been assigned numbers.
    Returns a new map.
-/
meta def map_of_expr (red : transparency) : expr_map ℕ → expr → tactic (expr_map ℕ × rb_map ℕ ℤ)
| m e@`(%%e1 * %%e2) :=
   (do (m', comp1) ← map_of_expr m e1,
      (m', comp2) ← map_of_expr m' e2,
      mp ← map_of_expr_mul_aux comp1 comp2,
      return (m', mp)) <|>
   (do k ← rb_map.find_defeq red m e, return (m, mk_rb_map.insert k 1)) <|>
   (let n := m.size + 1 in return (m.insert e n, mk_rb_map.insert n 1))
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
  | some z := return ⟨m, mk_rb_map.insert 0 z⟩
  | none :=
    (do k ← rb_map.find_defeq red m e, return (m, mk_rb_map.insert k 1)) <|>
    (let n := m.size + 1 in return (m.insert e n, mk_rb_map.insert n 1))
  end

meta def parse_into_comp_and_expr : expr → option (ineq × expr)
| `(%%e < 0) := (ineq.lt, e)
| `(%%e ≤ 0) := (ineq.le, e)
| `(%%e = 0) := (ineq.eq, e)
| _ := none

meta def to_comp (red : transparency) (e : expr) (m : expr_map ℕ) : tactic (comp × expr_map ℕ) :=
do (iq, e) ← parse_into_comp_and_expr e,
   (m', comp') ← map_of_expr red m e,
   return ⟨⟨iq, comp'⟩, m'⟩

meta def to_comp_fold (red : transparency) : expr_map ℕ → list expr →
      tactic (list (option comp) × expr_map ℕ)
| m [] := return ([], m)
| m (h::t) :=
  (do (c, m') ← to_comp red h m,
      (l, mp) ← to_comp_fold m' t,
      return (c::l, mp)) <|>
  (do (l, mp) ← to_comp_fold m t,
      return (none::l, mp))

/--
  Takes a list of proofs of props of the form t {<, ≤, =} 0, and creates a linarith_structure.
-/
meta def mk_linarith_structure (red : transparency) (l : list expr) : tactic (linarith_structure × rb_map ℕ (expr × expr)) :=
do pftps ← l.mmap infer_type,
  (l', map) ← to_comp_fold red mk_rb_map pftps,
  let lz := list.enum $ ((l.zip pftps).zip l').filter_map (λ ⟨a, b⟩, prod.mk a <$> b),
  let prmap := rb_map.of_list $ lz.map (λ ⟨n, x⟩, (n, x.1)),
  let vars : rb_set ℕ := rb_map.set_of_list $ list.range map.size.succ,
  let pc : rb_set pcomp := rb_map.set_of_list $
    lz.map (λ ⟨n, x⟩, ⟨x.2, comp_source.assump n⟩),
  return (⟨vars, pc⟩, prmap)

meta def linarith_monad.run (red : transparency) {α} (tac : linarith_monad α) (l : list expr) : tactic ((pcomp ⊕ α) × rb_map ℕ (expr × expr)) :=
do (struct, inputs) ← mk_linarith_structure red l,
match (state_t.run (validate >> tac) struct).run with
| (except.ok (a, _)) := return (sum.inr a, inputs)
| (except.error contr) := return (sum.inl contr, inputs)
end

end parse

section prove
open ineq tactic

meta def get_rel_sides : expr → tactic (expr × expr)
| `(%%a < %%b) := return (a, b)
| `(%%a ≤ %%b) := return (a, b)
| `(%%a = %%b) := return (a, b)
| `(%%a ≥ %%b) := return (a, b)
| `(%%a > %%b) := return (a, b)
| _ := failed

meta def mul_expr (n : ℕ) (e : expr) : pexpr :=
if n = 1 then ``(%%e) else
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

meta def mk_single_comp_zero_pf (c : ℕ) (h : expr) : tactic (ineq × expr) :=
do tp ← infer_type h,
  some (iq, e) ← return $ parse_into_comp_and_expr tp,
  if c = 0 then
    do e' ← mk_app ``zero_mul [e], return (eq, e')
  else if c = 1 then return (iq, h)
  else
    do nm ← resolve_name (ineq_const_mul_nm iq),
       tp ← (prod.snd <$> (infer_type h >>= get_rel_sides)) >>= infer_type,
       cpos ← to_expr ``((%%c.to_pexpr : %%tp) > 0),
       (_, ex) ← solve_aux cpos `[norm_num, done],
--       e' ← mk_app (ineq_const_mul_nm iq) [h, ex], -- this takes many seconds longer in some examples! why?
       e' ← to_expr ``(%%nm %%h %%ex) ff,
       return (iq, e')

meta def mk_lt_zero_pf_aux (c : ineq) (pf npf : expr) (coeff : ℕ) : tactic (ineq × expr) :=
do (iq, h') ← mk_single_comp_zero_pf coeff npf,
   let (nm, niq) := ineq_const_nm c iq,
   n ← resolve_name nm,
   e' ← to_expr ``(%%n %%pf %%h'),
   return (niq, e')

/--
  Takes a list of coefficients [c] and list of expressions, of equal length.
  Each expression is a proof of a prop of the form t {<, ≤, =} 0.
  Produces a proof that the sum of (c*t) {<, ≤, =} 0, where the comp is as strong as possible.
-/
meta def mk_lt_zero_pf : list ℕ → list expr → tactic expr
| _ [] := fail "no linear hypotheses found"
| [c] [h] := prod.snd <$> mk_single_comp_zero_pf c h
| (c::ct) (h::t) :=
  do (iq, h') ← mk_single_comp_zero_pf c h,
     prod.snd <$> (ct.zip t).mfoldl (λ pr ce, mk_lt_zero_pf_aux pr.1 pr.2 ce.2 ce.1) (iq, h')
| _ _ := fail "not enough args to mk_lt_zero_pf"

meta def term_of_ineq_prf (prf : expr) : tactic expr :=
do (lhs, _) ← infer_type prf >>= get_rel_sides,
   return lhs

meta structure linarith_config :=
(discharger : tactic unit := `[ring])
(restrict_type : option Type := none)
(restrict_type_reflect : reflected restrict_type . apply_instance)
(exfalso : bool := tt)
(transparency : transparency := reducible)

meta def ineq_pf_tp (pf : expr) : tactic expr :=
do (_, z) ← infer_type pf >>= get_rel_sides,
   infer_type z

meta def mk_neg_one_lt_zero_pf (tp : expr) : tactic expr :=
to_expr ``((neg_neg_of_pos zero_lt_one : -1 < (0 : %%tp)))

/--
  Assumes e is a proof that t = 0. Creates a proof that -t = 0.
-/
meta def mk_neg_eq_zero_pf (e : expr) : tactic expr :=
to_expr ``(neg_eq_zero.mpr %%e)

meta def add_neg_eq_pfs : list expr → tactic (list expr)
| [] := return []
| (h::t) :=
  do some (iq, tp) ← parse_into_comp_and_expr <$> infer_type h,
  match iq with
  | ineq.eq := do nep ← mk_neg_eq_zero_pf h, tl ← add_neg_eq_pfs t, return $ h::nep::tl
  | _ := list.cons h <$> add_neg_eq_pfs t
  end

/--
  Takes a list of proofs of propositions of the form t {<, ≤, =} 0,
  and tries to prove the goal `false`.
-/
meta def prove_false_by_linarith1 (cfg : linarith_config) : list expr → tactic unit
| [] := fail "no args to linarith"
| l@(h::t) :=
  do l' ← add_neg_eq_pfs l,
     hz ← ineq_pf_tp h >>= mk_neg_one_lt_zero_pf,
     (sum.inl contr, inputs) ← elim_all_vars.run cfg.transparency (hz::l')
       | fail "linarith failed to find a contradiction",
     let coeffs := inputs.keys.map (λ k, (contr.src.flatten.ifind k)),
     let pfs : list expr := inputs.keys.map (λ k, (inputs.ifind k).1),
     let zip := (coeffs.zip pfs).filter (λ pr, pr.1 ≠ 0),
     let (coeffs, pfs) := zip.unzip,
     mls ← zip.mmap (λ pr, do e ← term_of_ineq_prf pr.2, return (mul_expr pr.1 e)),
     sm ← to_expr $ add_exprs mls,
     tgt ← to_expr ``(%%sm = 0),
     (a, b) ← solve_aux tgt (cfg.discharger >> done),
     pf ← mk_lt_zero_pf coeffs pfs,
     pftp ← infer_type pf,
     (_, nep, _) ← rewrite_core b pftp,
     pf' ← mk_eq_mp nep pf,
     mk_app `lt_irrefl [pf'] >>= exact

end prove

section normalize
open tactic

set_option eqn_compiler.max_steps 50000

meta def rem_neg (prf : expr) : expr → tactic expr
| `(_ ≤ _) := to_expr ``(lt_of_not_ge %%prf)
| `(_ < _) := to_expr ``(le_of_not_gt %%prf)
| `(_ > _) := to_expr ``(le_of_not_gt %%prf)
| `(_ ≥ _) := to_expr ``(lt_of_not_ge %%prf)
| e := failed

meta def rearr_comp : expr → expr → tactic expr
| prf `(%%a ≤ 0) := return prf
| prf  `(%%a < 0) := return prf
| prf  `(%%a = 0) := return prf
| prf  `(%%a ≥ 0) := to_expr ``(neg_nonpos.mpr %%prf)
| prf  `(%%a > 0) := to_expr ``(neg_neg_of_pos %%prf)
| prf  `(0 ≥ %%a) := to_expr ``(show %%a ≤ 0, from %%prf)
| prf  `(0 > %%a) := to_expr ``(show %%a < 0, from %%prf)
| prf  `(0 = %%a) := to_expr ``(eq.symm %%prf)
| prf  `(0 ≤ %%a) := to_expr ``(neg_nonpos.mpr %%prf)
| prf  `(0 < %%a) := to_expr ``(neg_neg_of_pos %%prf)
| prf  `(%%a ≤ %%b) := to_expr ``(sub_nonpos.mpr %%prf)
| prf  `(%%a < %%b) := to_expr ``(sub_neg_of_lt %%prf)
| prf  `(%%a = %%b) := to_expr ``(sub_eq_zero.mpr %%prf)
| prf  `(%%a > %%b) := to_expr ``(sub_neg_of_lt %%prf)
| prf  `(%%a ≥ %%b) := to_expr ``(sub_nonpos.mpr %%prf)
| prf  `(¬ %%t) := do nprf ← rem_neg prf t, tp ← infer_type nprf, rearr_comp nprf tp
| prf  _ := fail "couldn't rearrange comp"


meta def is_numeric : expr → option ℚ
| `(%%e1 + %%e2) := (+) <$> is_numeric e1 <*> is_numeric e2
| `(%%e1 - %%e2) := has_sub.sub <$> is_numeric e1 <*> is_numeric e2
| `(%%e1 * %%e2) := (*) <$> is_numeric e1 <*> is_numeric e2
| `(%%e1 / %%e2) := (/) <$> is_numeric e1 <*> is_numeric e2
| `(-%%e) := rat.neg <$> is_numeric e
| e := e.to_rat

inductive {u} tree (α : Type u) : Type u
| nil {} : tree
| node : α → tree → tree → tree

def tree.repr {α} [has_repr α] : tree α → string
| tree.nil := "nil"
| (tree.node a t1 t2) := "tree.node " ++ repr a ++ " (" ++ tree.repr t1 ++ ") (" ++ tree.repr t2 ++ ")"

instance {α} [has_repr α] : has_repr (tree α) := ⟨tree.repr⟩

meta def find_cancel_factor : expr → ℕ × tree ℕ
| `(%%e1 + %%e2) :=
  let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, lcm := v1.lcm v2 in
  (lcm, tree.node lcm t1 t2)
| `(%%e1 - %%e2) :=
  let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, lcm := v1.lcm v2 in
  (lcm, tree.node lcm t1 t2)
| `(%%e1 * %%e2) :=
  match is_numeric e1, is_numeric e2 with
  | none, none := (1, tree.node 1 tree.nil tree.nil)
  | _, _ :=
    let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, pd := v1*v2 in
    (pd, tree.node pd t1 t2)
  end
| `(%%e1 / %%e2) :=
  match is_numeric e2 with
  | some q := let (v1, t1) := find_cancel_factor e1, n := v1.lcm q.num.nat_abs in
    (n, tree.node n t1 (tree.node q.num.nat_abs tree.nil tree.nil))
  | none := (1, tree.node 1 tree.nil tree.nil)
  end
| `(-%%e) := find_cancel_factor e
| _ := (1, tree.node 1 tree.nil tree.nil)

open tree

meta def mk_prod_prf : ℕ → tree ℕ → expr → tactic expr
| v (node _ lhs rhs) `(%%e1 + %%e2) :=
  do v1 ← mk_prod_prf v lhs e1, v2 ← mk_prod_prf v rhs e2, mk_app ``add_subst [v1, v2]
| v (node _ lhs rhs) `(%%e1 - %%e2) :=
  do v1 ← mk_prod_prf v lhs e1, v2 ← mk_prod_prf v rhs e2, mk_app ``sub_subst [v1, v2]
| v (node n lhs@(node ln _ _) rhs) `(%%e1 * %%e2) :=
  do tp ← infer_type e1, v1 ← mk_prod_prf ln lhs e1, v2 ← mk_prod_prf (v/ln) rhs e2,
     ln' ← tp.of_nat ln, vln' ← tp.of_nat (v/ln), v' ← tp.of_nat v,
     ntp ← to_expr ``(%%ln' * %%vln' = %%v'),
     (_, npf) ← solve_aux ntp `[norm_num, done],
     mk_app ``mul_subst [v1, v2, npf]
| v (node n lhs rhs@(node rn _ _)) `(%%e1 / %%e2) :=
  do tp ← infer_type e1, v1 ← mk_prod_prf (v/rn) lhs e1,
     rn' ← tp.of_nat rn, vrn' ← tp.of_nat (v/rn), n' ← tp.of_nat n, v' ← tp.of_nat v,
     ntp ← to_expr ``(%%rn' / %%e2 = 1),
     (_, npf) ← solve_aux ntp `[norm_num, done],
     ntp2 ← to_expr ``(%%vrn' * %%n' = %%v'),
     (_, npf2) ← solve_aux ntp2 `[norm_num, done],
     mk_app ``div_subst [v1, npf, npf2]
| v t `(-%%e) := do v' ← mk_prod_prf v t e, mk_app ``neg_subst [v']
| v _ e :=
  do tp ← infer_type e,
     v' ← tp.of_nat v,
     e' ← to_expr ``(%%v' * %%e),
     mk_app `eq.refl [e']

/--
 e is a term with rational division. produces a natural number n and a proof that n*e = e',
 where e' has no division.
-/
meta def kill_factors (e : expr) : tactic (ℕ × expr) :=
let (n, t) := find_cancel_factor e in
do e' ← mk_prod_prf n t e, return (n, e')

open expr
meta def expr_contains (n : name) : expr → bool
| (const nm _) := nm = n
| (lam _ _ _ bd) := expr_contains bd
| (pi _ _ _ bd) := expr_contains bd
| (app e1 e2) := expr_contains e1 || expr_contains e2
| _ := ff

lemma sub_into_lt {α} [ordered_semiring α] {a b : α} (he : a = b) (hl : a ≤ 0) : b ≤ 0 :=
by rwa he at hl

meta def norm_hyp_aux (h' lhs : expr) : tactic expr :=
do (v, lhs') ← kill_factors lhs,
   if v = 1 then return h' else do
   (ih, h'') ← mk_single_comp_zero_pf v h',
   (_, nep, _) ← infer_type h'' >>= rewrite_core lhs',
   mk_eq_mp nep h''

meta def norm_hyp (h : expr) : tactic expr :=
do htp ← infer_type h,
   h' ← rearr_comp h htp,
   some (c, lhs) ← parse_into_comp_and_expr <$> infer_type h',
   if expr_contains `has_div.div lhs then
     norm_hyp_aux h' lhs
   else return h'

meta def get_contr_lemma_name : expr → option name
| `(%%a < %%b) := return `lt_of_not_ge
| `(%%a ≤ %%b) := return `le_of_not_gt
| `(%%a = %%b) := return ``eq_of_not_lt_of_not_gt
| `(%%a ≥ %%b) := return `le_of_not_gt
| `(%%a > %%b) := return `lt_of_not_ge
| `(¬ %%a < %%b) := return `not.intro
| `(¬ %%a ≤ %%b) := return `not.intro
| `(¬ %%a = %%b) := return `not.intro
| `(¬ %%a ≥ %%b) := return `not.intro
| `(¬ %%a > %%b) := return `not.intro
| _ := none

-- assumes the input t is of type ℕ. Produces t' of type ℤ such that ↑t = t' and a proof of equality
meta def cast_expr (e : expr) : tactic (expr × expr) :=
do s ← [`int.coe_nat_add, `int.coe_nat_zero, `int.coe_nat_one,
        ``int.coe_nat_bit0_mul, ``int.coe_nat_bit1_mul, ``int.coe_nat_zero_mul, ``int.coe_nat_one_mul,
        ``int.coe_nat_mul_bit0, ``int.coe_nat_mul_bit1, ``int.coe_nat_mul_zero, ``int.coe_nat_mul_one,
        ``int.coe_nat_bit0, ``int.coe_nat_bit1].mfoldl simp_lemmas.add_simp simp_lemmas.mk,
   ce ← to_expr ``(↑%%e : ℤ),
   simplify s [] ce {fail_if_unchanged := ff}

meta def is_nat_int_coe : expr → option expr
| `((↑(%%n : ℕ) : ℤ)) := some n
| _ := none

meta def mk_coe_nat_nonneg_prf (e : expr) : tactic expr :=
mk_app `int.coe_nat_nonneg [e]

meta def get_nat_comps : expr → list expr
| `(%%a + %%b) := (get_nat_comps a).append (get_nat_comps b)
| `(%%a * %%b) := (get_nat_comps a).append (get_nat_comps b)
| e := match is_nat_int_coe e with
  | some e' := [e']
  | none := []
  end

meta def mk_coe_nat_nonneg_prfs (e : expr) : tactic (list expr) :=
(get_nat_comps e).mmap mk_coe_nat_nonneg_prf

meta def mk_cast_eq_and_nonneg_prfs (pf a b : expr) (ln : name) : tactic (list expr) :=
do (a', prfa) ← cast_expr a,
   (b', prfb) ← cast_expr b,
   la ← mk_coe_nat_nonneg_prfs a',
   lb ← mk_coe_nat_nonneg_prfs b',
   pf' ← mk_app ln [pf, prfa, prfb],
   return $ pf'::(la.append lb)

meta def mk_int_pfs_of_nat_pf (pf : expr) : tactic (list expr) :=
do tp ← infer_type pf,
match tp with
| `(%%a = %%b) := mk_cast_eq_and_nonneg_prfs pf a b ``nat_eq_subst
| `(%%a ≤ %%b) := mk_cast_eq_and_nonneg_prfs pf a b ``nat_le_subst
| `(%%a < %%b) := mk_cast_eq_and_nonneg_prfs pf a b ``nat_lt_subst
| `(%%a ≥ %%b) := mk_cast_eq_and_nonneg_prfs pf b a ``nat_le_subst
| `(%%a > %%b) := mk_cast_eq_and_nonneg_prfs pf b a ``nat_lt_subst
| `(¬ %%a ≤ %%b) := do pf' ← mk_app ``lt_of_not_ge [pf], mk_cast_eq_and_nonneg_prfs pf' b a ``nat_lt_subst
| `(¬ %%a < %%b) := do pf' ← mk_app ``le_of_not_gt [pf], mk_cast_eq_and_nonneg_prfs pf' b a ``nat_le_subst
| `(¬ %%a ≥ %%b) := do pf' ← mk_app ``lt_of_not_ge [pf], mk_cast_eq_and_nonneg_prfs pf' a b ``nat_lt_subst
| `(¬ %%a > %%b) := do pf' ← mk_app ``le_of_not_gt [pf], mk_cast_eq_and_nonneg_prfs pf' a b ``nat_le_subst
| _ := fail "mk_int_pfs_of_nat_pf failed: proof is not an inequality"
end

meta def mk_non_strict_int_pf_of_strict_int_pf (pf : expr) : tactic expr :=
do tp ← infer_type pf,
match tp with
| `(%%a < %%b) := to_expr ``(@cast (%%a < %%b) (%%a + 1 ≤ %%b) (by refl) %%pf)
| `(%%a > %%b) := to_expr ``(@cast (%%a > %%b) (%%a ≥ %%b + 1) (by refl) %%pf)
| `(¬ %%a ≤ %%b) := to_expr ``(@cast (%%a > %%b) (%%a ≥ %%b + 1) (by refl) (lt_of_not_ge %%pf))
| `(¬ %%a ≥ %%b) := to_expr ``(@cast (%%a < %%b) (%%a + 1 ≤ %%b) (by refl) (lt_of_not_ge %%pf))
| _ := fail "mk_non_strict_int_pf_of_strict_int_pf failed: proof is not an inequality"
end

meta def guard_is_nat_prop : expr → tactic unit
| `(%%a = _) := infer_type a >>= unify `(ℕ)
| `(%%a ≤ _) := infer_type a >>= unify `(ℕ)
| `(%%a < _) := infer_type a >>= unify `(ℕ)
| `(%%a ≥ _) := infer_type a >>= unify `(ℕ)
| `(%%a > _) := infer_type a >>= unify `(ℕ)
| `(¬ %%p) := guard_is_nat_prop p
| _ := failed

meta def guard_is_strict_int_prop : expr → tactic unit
| `(%%a < _) := infer_type a >>= unify `(ℤ)
| `(%%a > _) := infer_type a >>= unify `(ℤ)
| `(¬ %%a ≤ _) := infer_type a >>= unify `(ℤ)
| `(¬ %%a ≥ _) := infer_type a >>= unify `(ℤ)
| _ := failed

meta def replace_nat_pfs : list expr → tactic (list expr)
| [] := return []
| (h::t) :=
  (do infer_type h >>= guard_is_nat_prop,
      ls ← mk_int_pfs_of_nat_pf h,
      list.append ls <$> replace_nat_pfs t) <|> list.cons h <$> replace_nat_pfs t

meta def replace_strict_int_pfs : list expr → tactic (list expr)
| [] := return []
| (h::t) :=
  (do infer_type h >>= guard_is_strict_int_prop,
      l ← mk_non_strict_int_pf_of_strict_int_pf h,
      list.cons l <$> replace_strict_int_pfs t) <|> list.cons h <$> replace_strict_int_pfs t

meta def partition_by_type_aux : rb_lmap expr expr → list expr → tactic (rb_lmap expr expr)
| m [] := return m
| m (h::t) := do tp ← ineq_pf_tp h, partition_by_type_aux (m.insert tp h) t

meta def partition_by_type (l : list expr) : tactic (rb_lmap expr expr) :=
partition_by_type_aux mk_rb_map l

private meta def try_linarith_on_lists (cfg : linarith_config) (ls : list (list expr)) : tactic unit :=
(first $ ls.map $ prove_false_by_linarith1 cfg) <|> fail "linarith failed"

/--
  Takes a list of proofs of propositions.
  Filters out the proofs of linear (in)equalities,
  and tries to use them to prove `false`.
  If pref_type is given, starts by working over this type
-/
meta def prove_false_by_linarith (cfg : linarith_config) (pref_type : option expr) (l : list expr) : tactic unit :=
do l' ← replace_nat_pfs l,
   l'' ← replace_strict_int_pfs l',
   ls ← list.reduce_option <$> l''.mmap (λ h, (do s ← norm_hyp h, return (some s)) <|> return none)
          >>= partition_by_type,
   pref_type ← (unify pref_type.iget `(ℕ) >> return (some `(ℤ) : option expr)) <|> return pref_type,
   match cfg.restrict_type, ls.values, pref_type with
   | some rtp, _, _ :=
      do m ← mk_mvar, unify `(some %%m : option Type) cfg.restrict_type_reflect, m ← instantiate_mvars m,
         prove_false_by_linarith1 cfg (ls.ifind m)
   | none, [ls'], _ := prove_false_by_linarith1 cfg ls'
   | none, ls', none := try_linarith_on_lists cfg ls'
   | none, _, (some t) := prove_false_by_linarith1 cfg (ls.ifind t) <|> try_linarith_on_lists cfg (ls.erase t).values
   end

end normalize

end linarith

section
open tactic linarith

open lean lean.parser interactive tactic interactive.types
local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def linarith.elab_arg_list : option (list pexpr) → tactic (list expr)
| none := return []
| (some l) := l.mmap i_to_expr

meta def linarith.preferred_type_of_goal : option expr → tactic (option expr)
| none := return none
| (some e) := some <$> ineq_pf_tp e

/--
linarith.interactive_aux cfg o_goal restrict_hyps args:
 * cfg is a linarith_config object
 * o_goal : option expr is the local constant corresponding to the former goal, if there was one
 * restrict_hyps : bool is tt if `linarith only [...]` was used
 * args : option (list pexpr) is the optional list of arguments in `linarith [...]`
-/
meta def linarith.interactive_aux (cfg : linarith_config) :
  option expr → bool → option (list pexpr) → tactic unit
| none tt none := fail "linarith only called with no arguments"
| none tt (some l) := l.mmap i_to_expr >>= prove_false_by_linarith cfg none
| (some e) tt l :=
  do tp ← ineq_pf_tp e,
     list.cons e <$> linarith.elab_arg_list l >>= prove_false_by_linarith cfg (some tp)
| oe ff l :=
  do otp ← linarith.preferred_type_of_goal oe,
     list.append <$> local_context <*>
      (list.filter (λ a, bnot $ expr.is_local_constant a) <$> linarith.elab_arg_list l) >>=
     prove_false_by_linarith cfg otp

/--
  Tries to prove a goal of `false` by linear arithmetic on hypotheses.
  If the goal is a linear (in)equality, tries to prove it by contradiction.
  If the goal is not `false` or an inequality, applies `exfalso` and tries linarith on the
  hypotheses.
  `linarith` will use all relevant hypotheses in the local context.
  `linarith [t1, t2, t3]` will add proof terms t1, t2, t3 to the local context.
  `linarith only [h1, h2, h3, t1, t2, t3]` will use only the goal (if relevant), local hypotheses
    h1, h2, h3, and proofs t1, t2, t3. It will ignore the rest of the local context.
  `linarith!` will use a stronger reducibility setting to identify atoms.

  Config options:
  `linarith {exfalso := ff}` will fail on a goal that is neither an inequality nor `false`
  `linarith {restrict_type := T}` will run only on hypotheses that are inequalities over `T`
  `linarith {discharger := tac}` will use `tac` instead of `ring` for normalization.
    Options: `ring2`, `ring SOP`, `simp`
-/
meta def tactic.interactive.linarith (red : parse ((tk "!")?))
  (restr : parse ((tk "only")?)) (hyps : parse pexpr_list?)
  (cfg : linarith_config := {}) : tactic unit :=
let cfg :=
  if red.is_some then {cfg with transparency := semireducible, discharger := `[ring!]}
  else cfg in
do t ← target,
   match get_contr_lemma_name t with
   | some nm := seq (applyc nm) $
     do t ← intro1, linarith.interactive_aux cfg (some t) restr.is_some hyps
   | none := if cfg.exfalso then exfalso >> linarith.interactive_aux cfg none restr.is_some hyps
             else fail "linarith failed: target type is not an inequality."
   end

end
