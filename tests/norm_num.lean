/-
Copyright (c) 2017 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Tests for norm_num
-/

import tactic.norm_num

example : 374 + (32 - (2 * 8123) : ℤ) - 61 * 50 = 86 + 32 * 32 - 4 * 5000
      ∧ 43 ≤ 74 + (33 : ℤ) :=
by { norm_sub_expr, simp }

example : (1103 : ℤ) ≤ (2102 : ℤ) :=
by { norm_sub_expr, trivial }

example : (11047462383473829263 : ℤ) ≤ (21048574677772382462 : ℤ) :=
by { norm_sub_expr, trivial }

example : (210485742382937847263 : ℤ) ≤ (1104857462382937847262 : ℤ) :=
by { norm_sub_expr, trivial }

example : (210485987642382937847263 : ℕ) ≤ (11048512347462382937847262 : ℕ) :=
by { norm_sub_expr, trivial }

example : (210485987642382937847263 : ℚ) ≤ (11048512347462382937847262 : ℚ) :=
by { norm_sub_expr, trivial }

local infix ^ := pow_nat

example (x : ℕ) : ℕ := begin
  let n : ℕ, {apply_normed (2^32 - 71)},
  exact n
end
