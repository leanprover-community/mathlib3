import tactic.norm_cast

constant series {α} (f : ℕ → α) : α

@[norm_cast] axiom coe_series (f : ℕ → ℕ) :
  ((series (λ x, f x) : ℕ) : ℤ) = series (λ x, f x)

@[norm_cast] axiom coe_le (a b : ℕ) : (a : ℤ) ≤ b ↔ a ≤ b

run_cmd do
l ← norm_cast.make_guess ``coe_series,
guard $ l = norm_cast.label.move

example (f : ℕ → ℕ) (h : (0 : ℕ) ≤ series (λ x, f x)) : (0 : ℤ) ≤ series (λ x, f x) :=
begin
  norm_cast,
  guard_target (0 : ℕ) ≤ series (λ x, f x),
  exact h
end
