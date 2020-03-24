/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.core
import tactic.tauto

namespace tactic

/-- Run a tactic, and then return the pretty printed original goal. -/
-- This could be inlined into the interactive `show_term`,
-- but I've kept it separate so we can do silent testing.
meta def pp_term {α : Type} (t : tactic α) : tactic string :=
do
  g :: _ ← get_goals,
  t,
  to_string <$> pp g

namespace interactive

/--
`show_term { tac }` runs the tactic `tac`,
and then prints the term that was constructed.

This is useful for understanding what tactics are doing,
and how metavariables are handled.

As an example, if the goal is `ℕ × ℕ`, `show_term { split, exact 0 }` will
print `(0, ?m_1)`, and afterwards there will be one remaining goal (of type `ℕ`).
This indicates that `split, exact 0` partially filled in the original metavariable,
but created a new metavariable for the resulting sub-goal.
-/
meta def show_term (t : itactic) : itactic :=
pp_term t >>= trace

end interactive
end tactic
