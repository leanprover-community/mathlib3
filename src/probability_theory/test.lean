import data.real.basic

open_locale classical

variables {α : Type*}

noncomputable
def upper_crossing (f : ℕ → α → ℝ) (a b : ℝ) : ℕ → α → ℕ
| 0 x := 0
| (n + 1) x := if h : ∃ s,
  (if h : ∃ t, upper_crossing n x < t ∧ f t x ≤ a then nat.find h else (n + 1)) < s ∧ b ≤ f s x
  then nat.find h else (n + 1)

-- lemma upper_crossing_succ {f : ℕ → α → ℝ} {a b : ℝ} (n : ℕ) (x : α) :
--   upper_crossing f a b (n + 1) x =
--     if h : ∃ s,
--       (if h : ∃ t, upper_crossing f a b n x < t ∧ f t x ≤ a then nat.find h else (n + 1)) < s ∧
--         b ≤ f s x
--     then nat.find h else (n + 1) :=
-- begin
--   refl
-- end
