import tactic.push_neg

example (h : ∃ p: ℕ, ¬ ∀ n : ℕ, n > p) (h' : ∃ p: ℕ, ¬ ∃ n : ℕ, n < p) : ¬ ∀ n : ℕ, n = 0 :=
begin
  push_neg at *,
  guard_target_strict ∃ (n : ℕ), n ≠ 0,
  guard_hyp_strict h := ∃ (p n : ℕ), n ≤ p,
  guard_hyp_strict h' := ∃ (p : ℕ), ∀ (n : ℕ), p ≤ n,
  use 1,
end

-- In the next example, ℤ should be ℝ in maths, but I don't want to import real numbers
-- for testing only
local notation `|` x `|` := abs x

example (a : ℕ → ℤ) (l : ℤ) (h : ¬ ∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε) : true :=
begin
  push_neg at h,
  guard_hyp_strict h := ∃ (ε : ℤ), ε > 0 ∧ ∀ (N : ℕ), ∃ (n : ℕ), n ≥ N ∧ ε ≤ |a n - l|,
  trivial
end

example (f : ℤ → ℤ) (x₀ y₀) (h : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε) : true :=
begin
  push_neg at h,
  guard_hyp_strict h := ∃ (ε : ℤ), ε > 0 ∧ ∀ δ > 0, (∃ (x : ℤ), |x - x₀| ≤ δ ∧ ε < |f x - y₀| ),
  trivial
end
