/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The order relation on the integers.
-/

import init_.data.int.basic
import algebra.ordered_ring

/-
Results copied from the core library to mathlib by Johan Commelin
-/

namespace int

instance : decidable_linear_ordered_comm_ring int :=
{ add_le_add_left := @int.add_le_add_left,
  zero_ne_one     := int.zero_ne_one,
  mul_pos         := @int.mul_pos,
  zero_lt_one     := int.zero_lt_one,
  ..int.comm_ring, ..int.decidable_linear_order }

instance : decidable_linear_ordered_add_comm_group int :=
by apply_instance

theorem abs_eq_nat_abs : ∀ a : ℤ, abs a = nat_abs a
| (n : ℕ) := abs_of_nonneg $ coe_zero_le _
| -[1+ n] := abs_of_nonpos $ le_of_lt $ neg_succ_lt_zero _

theorem nat_abs_abs (a : ℤ) : nat_abs (abs a) = nat_abs a :=
by rw [abs_eq_nat_abs]; refl

theorem sign_mul_abs (a : ℤ) : sign a * abs a = a :=
by rw [abs_eq_nat_abs, sign_mul_nat_abs]

end int
