/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

Tactic to merge identical goals.
-/

namespace tactic
open list

private meta def unify_or_cons : list expr → expr → tactic (list expr)
| []        g := pure [g]
| (x :: xs) g := (unify x g >> pure (x :: xs)) <|> cons x <$> unify_or_cons xs g

meta def merge_goals : tactic unit :=
do gs ← get_goals,
   new_gs ← mfoldl unify_or_cons [] gs,
   set_goals new_gs

namespace interactive

meta def merge_goals : tactic unit :=
tactic.merge_goals

end interactive

example : ((true ∧ (∀ (x y : ℕ), x + y = y + x)) ∧ (true ∧ true)) ∧
          (((∀ (x y : ℕ), x + y = y + x) ∧ true) ∧ (true ∧ true)) :=
begin
  split; split; split,
  merge_goals,
  exact trivial,
  exact nat.add_comm,
end

end tactic
