import tactic.qify

example (a b : ℕ) : (a : ℚ) ≤ b ↔ a ≤ b := by qify ; refl
example (a b : ℕ) : (a : ℚ) < b ↔ a < b := by qify ; refl
example (a b : ℕ) : (a : ℚ) = b ↔ a = b := by qify ; refl
example (a b : ℕ) : (a : ℚ) ≠ b ↔ a ≠ b := by qify ; refl

example (a b : ℤ) : (a : ℚ) ≤ b ↔ a ≤ b := by qify ; refl
example (a b : ℤ) : (a : ℚ) < b ↔ a < b := by qify ; refl
example (a b : ℤ) : (a : ℚ) = b ↔ a = b := by qify ; refl
example (a b : ℤ) : (a : ℚ) ≠ b ↔ a ≠ b := by qify ; refl

example (a b c : ℕ) (h : a - b = c) (hab : b ≤ a) : a = c + b :=
begin
  qify [hab] at h ⊢, -- `zify` does the same thing here.
  exact sub_eq_iff_eq_add.1 h,
end

example (a b c : ℤ) (h : a / b = c) (hab : b ∣ a) (hb : b ≠ 0) : a = c * b :=
begin
  qify [hab] at h hb ⊢,
  exact (div_eq_iff hb).1 h,
end
