import algebra.ordered_ring

-- This works fine:
example {a b : ℕ} (h : 0 < b) (w : 1 ≤ a) : b ≤ a * b :=
(le_mul_iff_one_le_left h).mpr w

example {a b : ℕ} (h : b > 0) (w : a ≥ 1) : b ≤ a * b :=
by library_search -- exact (le_mul_iff_one_le_left h).mpr w
