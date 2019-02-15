/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

Tactic to merge identical goals.
-/

import category.fold

namespace tactic

private meta def map_unify (g : expr) : list expr → tactic unit
| []        := fail ()
| (x :: xs) := unify g x <|> map_unify xs

/- This returns either ac or ac ++ [g] depending on whether g unifies with some goal in ac -/
private meta def unify_or_add (g : expr) (ac : tactic (list expr)) : tactic (list expr) :=
do l ← ac, (map_unify g l >> return l) <|> return (l ++ [g])

meta def merge_goals : tactic unit :=
do gs ← get_goals,
   new_gs ← traversable.foldr unify_or_add (return []) gs,
   set_goals new_gs

namespace interactive

meta def merge_goals : tactic unit :=
tactic.merge_goals

end interactive

example : ((true ∧ true) ∧ (true ∧ true)) ∧ (((∀ (x y : ℕ), x + y = y + x) ∧ true) ∧ (true ∧ true)) :=
begin
  split; split; split,
  merge_goals,
  exact trivial,
  exact nat.add_comm,
end

end tactic
