import tactic.show_term

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
