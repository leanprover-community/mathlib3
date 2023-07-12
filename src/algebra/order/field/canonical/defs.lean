/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import algebra.order.field.defs
import algebra.order.ring.canonical
import algebra.order.with_zero

/-!
# Canonically ordered semifields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

set_option old_structure_cmd true

variables {α : Type*}

/-- A canonically linear ordered field is a linear ordered field in which `a ≤ b` iff there exists
`c` with `b = a + c`. -/
@[protect_proj, ancestor canonically_ordered_comm_semiring linear_ordered_semifield]
class canonically_linear_ordered_semifield (α : Type*)
  extends canonically_ordered_comm_semiring α, linear_ordered_semifield α

@[priority 100] -- See note [lower instance priority]
instance canonically_linear_ordered_semifield.to_linear_ordered_comm_group_with_zero
  [canonically_linear_ordered_semifield α] : linear_ordered_comm_group_with_zero α :=
{ mul_le_mul_left := λ a b h c, mul_le_mul_of_nonneg_left h $ zero_le _,
  ..‹canonically_linear_ordered_semifield α› }

@[priority 100] -- See note [lower instance priority]
instance canonically_linear_ordered_semifield.to_canonically_linear_ordered_add_monoid
  [canonically_linear_ordered_semifield α] : canonically_linear_ordered_add_monoid α :=
{ ..‹canonically_linear_ordered_semifield α› }
