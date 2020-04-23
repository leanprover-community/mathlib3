/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.doc_commands

open tactic

namespace tactic.interactive

/--
`show_term { tac }` runs the tactic `tac`,
and then prints the term that was constructed.

This is useful for understanding what tactics are doing,
and how metavariables are handled.

As an example, if the goal is `ℕ × ℕ`, `show_term { split, exact 0 }` will
print `(0, ?m_1)`, and afterwards there will be one remaining goal (of type `ℕ`).
This indicates that `split, exact 0` partially filled in the original metavariable,
but created a new metavariable for the resulting sub-goal.

As another example, in
```
example {P Q R : Prop} (h₁ : Q → P) (h₂ : R) (h₃ : R → Q) : P ∧ R :=
by show_term { tauto }
```
the term mode proof `⟨h₁ (h₃ h₂), eq.mpr rfl h₂⟩` produced by `tauto` will be printed.
-/
meta def show_term (t : itactic) : itactic :=
do
  g :: _ ← get_goals,
  t,
  trace g

add_tactic_doc
{ name := "show_term",
  category := doc_category.tactic,
  decl_names := [``show_term],
  tags := ["debugging"] }

end tactic.interactive
