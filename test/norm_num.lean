/-
Copyright (c) 2017 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Mario Carneiro

Tests for norm_num
-/

import data.real.basic tactic.norm_num

example : 374 + (32 - (2 * 8123) : ℤ) - 61 * 50 = 86 + 32 * 32 - 4 * 5000
      ∧ 43 ≤ 74 + (33 : ℤ) := by norm_num

example : ¬ (7-2)/(2*3) ≥ (1:ℝ) + 2/(3^2) := by norm_num
example : (6:real) + 9 = 15 := by norm_num
example : (2:real)/4 + 4 = 3*3/2 := by norm_num
example : (((3:real)/4)-12)<6 := by norm_num
example : (5:real) ≠ 8 := by norm_num
example : (10:real) > 7 := by norm_num
example : (2:real) * 2 + 3 = 7 := by norm_num
example : (6:real) < 10 := by norm_num
example : (7:real)/2 > 3 := by norm_num
example : (4:real)⁻¹ < 1 := by norm_num
example : 2 ^ 17 - 1 = 131071 := by norm_num

example : (5 / 2:ℕ) = 2 := by norm_num
example : (5 / -2:ℤ) < -1 := by norm_num
example : (0 + 1) / 2 < 0 + 1 := by norm_num

example (x : ℤ) (h : 1000 + 2000 < x) : 100 * 30 < x :=
by norm_num at *; try_for 100 {exact h}

example : (1103 : ℤ) ≤ (2102 : ℤ) := by norm_num
example : (110474 : ℤ) ≤ (210485 : ℤ) := by norm_num
example : (11047462383473829263 : ℤ) ≤ (21048574677772382462 : ℤ) := by norm_num
example : (210485742382937847263 : ℤ) ≤ (1104857462382937847262 : ℤ) := by norm_num
example : (210485987642382937847263 : ℕ) ≤ (11048512347462382937847262 : ℕ) := by norm_num
example : (210485987642382937847263 : ℚ) ≤ (11048512347462382937847262 : ℚ) := by norm_num

example (x : ℕ) : ℕ := begin
  let n : ℕ, {apply_normed (2^32 - 71)},
  exact n
end
