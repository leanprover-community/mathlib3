import tactic.zify

example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) (h2 : (c : ℤ) < a + 3 * b) : a + 3*b > c :=
begin
  zify at h ⊢,
  guard_hyp h : ¬↑x * ↑y * ↑z < (0 : ℤ),
  guard_target ↑c < (↑a : ℤ) + 3 * ↑b,
  exact h2
end

example (a b : ℕ) (h : (a : ℤ) ≤ b) : a ≤ b :=
begin
  zify,
  guard_target (a : ℤ) ≤ b,
  exact h
end

example (a b : ℕ) (h : a = b ∧ b < a) : false :=
begin
  zify at h,
  cases h with ha hb,
  apply ne_of_lt hb,
  rw ha
end

example (a b c : ℕ) (h : a - b < c) (hab : b ≤ a) : true :=
begin
  zify [hab] at h,
  guard_hyp h : (a : ℤ) - b < c,
  trivial
end

example (a b c : ℕ) (h : a + b ≠ c) : true :=
begin
  zify at h,
  guard_hyp h : (a : ℤ) + b ≠ c,
  trivial
end
