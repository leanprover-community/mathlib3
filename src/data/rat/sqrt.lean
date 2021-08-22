/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/

import data.rat.order
import data.int.sqrt
/-!
# Square root on rational numbers

This file defines the square root function on rational numbers `rat.sqrt`
and proves several theorems about it.

-/
namespace rat

/-- Square root function on rational numbers, defined by taking the (integer) square root of the
numerator and the square root (on natural numbers) of the denominator. -/
@[pp_nodot] def sqrt (q : ℚ) : ℚ := rat.mk (int.sqrt q.num) (nat.sqrt q.denom)

theorem sqrt_eq (q : ℚ) : rat.sqrt (q*q) = |q| :=
by rw [sqrt, mul_self_num, mul_self_denom, int.sqrt_eq, nat.sqrt_eq, abs_def]

theorem exists_mul_self (x : ℚ) : (∃ q, q * q = x) ↔ rat.sqrt x * rat.sqrt x = x :=
⟨λ ⟨n, hn⟩, by rw [← hn, sqrt_eq, abs_mul_abs_self],
λ h, ⟨rat.sqrt x, h⟩⟩

theorem sqrt_nonneg (q : ℚ) : 0 ≤ rat.sqrt q :=
nonneg_iff_zero_le.1 $ (mk_nonneg _ $ int.coe_nat_pos.2 $
nat.pos_of_ne_zero $ λ H, pos_iff_ne_zero.1 q.pos $ nat.sqrt_eq_zero.1 H).2
$ int.coe_nat_nonneg _

end rat
