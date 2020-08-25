/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import data.nat.sqrt

namespace int

/-- `sqrt n` is the square root of an integer `n`. If `n` is not a
  perfect square, and is positive, it returns the largest `k:ℤ` such
  that `k*k ≤ n`. If it is negative, it returns 0. For example,
  `sqrt 2 = 1` and `sqrt 1 = 1` and `sqrt (-1) = 0` -/
@[pp_nodot] def sqrt (n : ℤ) : ℤ :=
nat.sqrt $ int.to_nat n

theorem sqrt_eq (n : ℤ) : sqrt (n*n) = n.nat_abs :=
by rw [sqrt, ← nat_abs_mul_self, to_nat_coe_nat, nat.sqrt_eq]

theorem exists_mul_self (x : ℤ) :
  (∃ n, n * n = x) ↔ sqrt x * sqrt x = x :=
⟨λ ⟨n, hn⟩, by rw [← hn, sqrt_eq, ← int.coe_nat_mul, nat_abs_mul_self],
λ h, ⟨sqrt x, h⟩⟩

theorem sqrt_nonneg (n : ℤ) : 0 ≤ sqrt n := trivial

end int
