import tactic.ring data.real.basic

example (x y : ℕ) : x + y = y + x := by ring
example (x y : ℕ) : x + y + y = 2 * y + x := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!
example {α} [comm_ring α] (x y : α) : x + y + y - x = 2 * y := by ring
example (x y : ℚ) : x / 2 + x / 2 = x := by ring
example (x y : ℚ) : (x + y) ^ 3 = x ^ 3 + y ^ 3 + 3 * (x * y ^ 2 + x ^ 2 * y) := by ring
example (x y : ℝ) : (x + y) ^ 3 = x ^ 3 + y ^ 3 + 3 * (x * y ^ 2 + x ^ 2 * y) := by ring
example {α} [comm_semiring α] (x : α) : (x + 1) ^ 6 = (1 + x) ^ 6 := by try_for 15000 {ring}
example (a n s: ℕ) : a * (n - s) = (n - s) * a := by ring

example (x y z : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  x / (y / z) + y ⁻¹ + 1 / (y * -x) = -1/ (x * y) + (x * z + 1) / y :=
begin
  field_simp [hx, hy, hz],
  ring
end

example (a b c d x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
  a + b / x + c / x^2 + d / x^3 = a + x⁻¹ * (y * b / y + (d / x + c) / x) :=
begin
  field_simp [hx, hy],
  ring
end
