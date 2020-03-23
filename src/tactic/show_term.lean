import tactic.core
import tactic.tauto

namespace tactic

/-- Run a tactic, returning the goals as they were before running the tactic. -/
meta def capture_terms {α : Type} (t : tactic α) : tactic (list expr × α) :=
do
  gs ← get_goals,
  a ← t,
  return (gs, a)

/-- Run a tactic, and then return the pretty printed original goal. -/
meta def pp_term {α : Type} (t : tactic α) : tactic string :=
do
  g :: _ ← get_goals,
  t,
  to_string <$> pp g

namespace interactive

declare_trace show_term

/--
`show_term { tac }` runs the tactic `tac`,
and then prints the term that was constructed.

This is useful for understanding what tactics are doing,
and how metavariables are handled.

As an example, if the goal is `ℕ × ℕ`, `show_term { split, exact 0 }` will
print `(0, ?m_1)`, indicating that the original goal has been partially filled in.
-/
meta def show_term (t : itactic) : itactic :=
pp_term t >>= (λ s, when_tracing `show_term (trace s))

end interactive
end tactic

set_option trace.show_term true

-- Comment this out to observe the output below:
set_option trace.show_term false

example : ℕ → ℕ :=
begin
  show_term { intro n },
  show_term { exact 0 },
end

example : ℕ × ℕ :=
begin
  show_term { split, },
  exact 0, exact 1,
end

example : ℕ × ℕ :=
begin
  -- We test the output is as expected.
  tactic.lock_tactic_state $ (do
    s ← tactic.pp_term `[split, exact 0],
    guard $ s = "(0, ?m_1)"),

  show_term { split, exact 0, },
  exact 1,
end

example (a b c : ℕ) : a + (b + c) = (a + c) + b :=
begin
  show_term { simp only [add_comm b c], },
  show_term { simp only [add_assoc], },
end

example {P Q R : Prop} (h₁ : Q → P) (h₂ : R) (h₃ : R → Q) : P ∧ R :=
begin
  -- We test the output is as expected.
  tactic.lock_tactic_state $ (do
    s ← tactic.pp_term `[tauto],
    guard $ s = "⟨h₁ (h₃ h₂), eq.mpr rfl h₂⟩"),

  show_term { tauto },
end
