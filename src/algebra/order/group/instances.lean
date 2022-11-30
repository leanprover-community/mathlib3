/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.order.group.defs
import algebra.order.monoid.order_dual

/-!
# Additional instances for ordered commutative groups.

-/

variables {α : Type*}

@[priority 100, to_additive]    -- see Note [lower instance priority]
instance ordered_comm_group.to_ordered_cancel_comm_monoid [s : ordered_comm_group α] :
  ordered_cancel_comm_monoid α :=
{ le_of_mul_le_mul_left := λ a b c, (mul_le_mul_iff_left a).mp,
  ..s }

@[to_additive] instance [ordered_comm_group α] : ordered_comm_group αᵒᵈ :=
{ .. order_dual.ordered_comm_monoid, .. order_dual.group }

@[to_additive] instance [linear_ordered_comm_group α] :
  linear_ordered_comm_group αᵒᵈ :=
{ .. order_dual.ordered_comm_group, .. order_dual.linear_order α }

@[priority 100, to_additive] -- see Note [lower instance priority]
instance linear_ordered_comm_group.to_linear_ordered_cancel_comm_monoid
  [linear_ordered_comm_group α] : linear_ordered_cancel_comm_monoid α :=
{ le_of_mul_le_mul_left := λ x y z, le_of_mul_le_mul_left',
  ..‹linear_ordered_comm_group α› }
