import tactic.interactive
import algebra.gcd_monoid.finset
/-!  `congrm`: `congr` with pattern-matching -/

namespace tactic.interactive
open tactic interactive
setup_tactic_parser

/--  Scans three `expr`s `e, lhs, rhs` in parallel.
Currently, `equate_with_pattern` has three behaviours at each location:
produce a goal, recurse, or skip.

See the doc-string for `tactic.interactive.dap` for more details.
-/
meta def equate_with_pattern : expr → expr → expr → tactic unit
| (expr.app f e) (expr.app f0 e0) (expr.app f1 e1) := do
  match e with
  | (expr.mvar _ _ _) := do
    el ← mk_app `eq [e0, e1],
    n ← get_unused_name "h",
    assert n el,
--    swap,
--    get_local n >>= rewrite_target
    equate_with_pattern f f0 f1
  | _ := do equate_with_pattern e e0 e1 *> equate_with_pattern f f0 f1
  end
| _ _ _ := skip

meta def decomp : expr → expr → expr → tactic unit
| (expr.app f e) (expr.app f0 e0) (expr.app f1 e1) :=
  match e with
  | (expr.mvar _ _ _) := do el ← mk_app `eq [e0, e1],
       n ← get_unused_name "h",
       assert n el,
       swap,
       decomp f f0 f1,
       rotate_right 1
  | _ := do decomp f f0 f1 *> decomp e e0 e1
  end
| _ _ _ := skip


meta def refine' (e : parse texpr) : tactic unit :=
do
  tgt ← target,
  e' ← to_expr e tt ff >>= infer_type,
  decomp e' tgt e',
  unify e' tgt,
  apply e

end tactic.interactive

example (α : Type*) : finset ℕ → α :=
begin
  refine' (λ s : finset ℕ, s.sum _),
/-2 goals
α: Type ?
s: finset ℕ
⊢ add_comm_monoid α
α: Type ?
s: finset ℕ
⊢ ℕ → α
-/
end


#exit
/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import tactic.interactive
import algebra.big_operators.basic
/-!  `congrm`: `congr` with pattern-matching -/

namespace tactic.interactive
open tactic interactive
setup_tactic_parser

meta def equations_from_pattern : expr → expr → expr → tactic (list expr)
| (expr.app f e) (expr.app f0 e0) (expr.app f1 e1) := do
  match e with
  | (expr.mvar _ _ _) := do
    el ← mk_app `eq [e0, e1],
    rest ← equations_from_pattern f f0 f1,
    return ([el] ++ rest)
  | _ := do
    ne1 ← equations_from_pattern e e0 e1,
    ne2 ← equations_from_pattern f f0 f1,
    return (ne1 ++ ne2)
  end
| _ _ _ := return []

meta def generate_equalities : list expr → tactic unit
| []      := skip
| (a::as) := do n ← get_unused_name "h",
                assert n a,
                swap,
                generate_equalities as

meta def scan_with_res (arg : parse texpr) : tactic unit :=
do ta ← to_expr arg tt ff,
  tgt ← target,
  (lhs, rhs) ← match_eq tgt,
  equations_from_pattern ta lhs rhs >>= generate_equalities

--  let n := get_unused_name "h",
--  let name_fun := ((λ ee, tactic.assert (get_unused_name "h") ee) : expr → tactic unit),
  --eqs.mmap (λ ee, tactic.assert (get_unused_name "h") ee)


/--  Scans three `expr`s `e, lhs, rhs` in parallel.
Currently, `equate_with_pattern` has three behaviours at each location:
produce a goal, recurse, or skip.

See the doc-string for `tactic.interactive.dap` for more details.
-/
meta def equate_with_pattern : expr → expr → expr → tactic unit
| (expr.app f e) (expr.app f0 e0) (expr.app f1 e1) := do
  match e with
  | (expr.mvar _ _ _) := do
    el ← mk_app `eq [e0, e1],pp0 ← pp e0,pp1 ← pp e1,trace "sopra",
    trace pformat!" e0: {pp0}\n e1: {e1}\n el: {el}",target >>= trace,
    (try assumption >> try congr_core >> all_goals' (try reflexivity >> try congr)),
--    guard e.is_app,
--   clemma ← mk_specialized_congr_lemma e, infer_type clemma.type >>= trace,
--   apply_congr_core clemma

/-
meta def apply_eq_congr_core (tgt : expr) : tactic unit :=
do (lhs, rhs) ← match_eq tgt,
   guard lhs.is_app,
   clemma ← mk_specialized_congr_lemma lhs,
   apply_congr_core clemma
-/
/-
    ,
    n ← get_unused_name "h",
    assert n el,
    rotate,
    get_local n >>= rewrite_target,
-/
    equate_with_pattern f f0 f1
  | _ := do trace "mezzo",equate_with_pattern e e0 e1 *> equate_with_pattern f f0 f1
  end
| _ _ _ := trace "sotto" *> skip

/--  `rev_goals` reverses the list of goals. -/
meta def rev_goals : tactic unit :=
do gs ← get_goals,
  set_goals gs.reverse

/--  `congrm e` assumes that the goal is of the form `lhs = rhs`.  `congrm e` scans `e, lhs, rhs` in
parallel.
Assuming that the three expressions are successions of function applications, `congrm e`
uses `e` as a pattern to decide what to do in corresponding places of `lhs` and `rhs`.

If `e` has a meta-variable in a location, then the tactic produces a side-goal with
the equality of the corresponding locations in `lhs, rhs`.

Otherwise, `congrm` keeps scanning deeper into the expressions, until either the expressions finish
or there is a mismatch between their shapes.

*Note:* `congrm` does no check to make sure that the functions that it is matching are equal,
or even defeq.  For instance,
```lean
example : (nat.pred 5) * nat.succ 7 = (nat.pred 8) + nat.pred 12 :=
begin
  congrm (id _) + nat.succ _,
end
```
produces the three goals
```
⊢ 5 = 8
⊢ 7 = 12
⊢ (nat.pred 8) * nat.succ 12 = (nat.pred 8) + nat.pred 12
```
In fact, not even the types need to match:
```
example : (nat.pred 5) * nat.succ 7 = (nat.pred 8) + nat.pred 12 :=
begin
  let i₁ : ℤ → ℤ := sorry,
  let i₁' : ℤ → ℤ := sorry,
  let i₂ : ℤ → ℤ → ℤ := sorry,
  congrm i₂ (i₁ _) (i₁' _),
end
```
produces the same three goals as above
```
⊢ 5 = 8
⊢ 7 = 12
⊢ (nat.pred 8) * nat.succ 12 = (nat.pred 8) + nat.pred 12
```
-/
meta def congrm (arg : parse texpr) : tactic unit :=
do ta ← to_expr arg tt ff,
  tgt ← target,
  (lhs, rhs) ← match_eq tgt,
  equate_with_pattern ta lhs rhs,
  try refl,
  rev_goals

#check apply_eq_congr_core
meta def _root_.tactic.refine' (e : pexpr) : tactic unit :=
do
  tgt ← target,
  e' ← to_expr e tt ff >>= infer_type,
  equate_with_pattern e' tgt e',
  unify e' tgt,
  apply e

meta def refine' (q : parse texpr) : tactic unit :=
tactic.refine' q



end tactic.interactive

open tactic

example : Σ (α : Type), finset ℕ → α :=
begin
  let α := _,
  refine' ⟨α, (λ s : finset ℕ, s.sum _ : finset ℕ → α)⟩,
  show ℕ → α, exact id,
  apply_instance,
end


example (α : Type) : finset ℕ → α :=
begin
  (do
    e ← to_expr ``(λ s : finset ℕ, s.sum _), -- works, generating a `add_comm_monoid α` goal
    exact e),
  sorry,
  sorry
end

example (α : Type) : finset ℕ → α :=
begin
  (do
    tgt ← target,
    e ← to_expr ``(λ s : finset ℕ, s.sum _ : %%tgt), -- failed to synthesize type class instance for `add_comm_monoid α`
    exact e),
end



example (α : Type*) : finset ℕ → α :=
begin
  apply (λ s : finset ℕ, s.sum _),

end


example (α : Type*) : finset ℕ → α :=
begin
  refine' (λ s : finset ℕ, s.sum _),


  apply (λ s : finset ℕ, s.sum _),




  refine' (λ s, s.sum _),
  show ℕ → α, exact id,
  apply_instance,
end
