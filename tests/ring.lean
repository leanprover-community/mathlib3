import tactic.ring data.real.basic

example (x y : ℕ) : x + y = y + x := by ring
example (x y : ℕ) : x + y + y = 2 * y + x := by ring
example {α} [comm_ring α] (x y : α) : x + y + y - x = 2 * y := by ring
example (x y : ℚ) : x / 2 + x / 2 = x := by ring
example (x y : ℚ) : (x + y) ^ 3 = x ^ 3 + y ^ 3 + 3 * (x * y ^ 2 + x ^ 2 * y) := by ring
example (x y : ℝ) : (x + y) ^ 3 = x ^ 3 + y ^ 3 + 3 * (x * y ^ 2 + x ^ 2 * y) := by ring
example {α} [comm_semiring α] (x : α) : (x + 1) ^ 6 = (1 + x) ^ 6 := by try_for 15000 {ring}

