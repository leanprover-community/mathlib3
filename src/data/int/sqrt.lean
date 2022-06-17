/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import data.nat.sqrt

/-!
# Square root of integers

This file defines the square root function on integers. `int.sqrt z` is the greatest integer `r`
such that `r * r ≤ z`. If `z ≤ 0`, then `int.sqrt z = 0`.
-/

namespace int

/-- `sqrt z` is the square root of an integer `z`. If `z` is positive, it returns the largest
integer `r` such that `r * r ≤ n`. If it is negative, it returns `0`. For example, `sqrt (-1) = 0`,
`sqrt 1 = 1`, `sqrt 2 = 1` -/
@[pp_nodot] def sqrt (z : ℤ) : ℤ :=
nat.sqrt $ int.to_nat z

theorem sqrt_eq (n : ℤ) : sqrt (n*n) = n.nat_abs :=
by rw [sqrt, ← nat_abs_mul_self, to_nat_coe_nat, nat.sqrt_eq]

theorem exists_mul_self (x : ℤ) :
  (∃ n, n * n = x) ↔ sqrt x * sqrt x = x :=
⟨λ ⟨n, hn⟩, by rw [← hn, sqrt_eq, ← int.coe_nat_mul, nat_abs_mul_self],
λ h, ⟨sqrt x, h⟩⟩

theorem sqrt_nonneg (n : ℤ) : 0 ≤ sqrt n := coe_nat_nonneg _

end int
