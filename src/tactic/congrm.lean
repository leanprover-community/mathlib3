/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import tactic.interactive

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
    rotate,
    get_local n >>= rewrite_target,
    equate_with_pattern f f0 f1
  | _ := do equate_with_pattern e e0 e1 *> equate_with_pattern f f0 f1
  end
| _ _ _ := skip

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

end tactic.interactive
