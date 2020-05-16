/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The order relation on the integers.
-/

import init_.data.int.basic init_.algebra.ordered_ring

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

end int

