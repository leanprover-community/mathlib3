/-
Copyright (c) ........ All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: .......
-/

import data.nat.basic 

def sqrt (n : ℤ) : ℤ :=
nat.sqrt $ int.to_nat n

theorem sqrt_eq (n : ℤ) : int.sqrt (n*n) = int.nat_abs n :=
by rw [int.sqrt, ← int.nat_abs_mul_self, int.to_nat_coe_nat, nat.sqrt_eq]

theorem exists_mul_self (x : ℤ) :
  (∃ n, n * n = x) ↔ int.sqrt x * int.sqrt x = x :=
⟨λ ⟨n, hn⟩, by rw [← hn, int.sqrt_eq, ← int.coe_nat_mul, int.nat_abs_mul_self],
λ h, ⟨int.sqrt x, h⟩⟩

theorem sqrt_nonneg (n : ℤ) : 0 ≤ int.sqrt n :=
trivial