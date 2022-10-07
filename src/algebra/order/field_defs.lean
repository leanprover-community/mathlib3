/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import algebra.field.basic
import algebra.group_power.lemmas
import algebra.group_power.order
import algebra.order.ring
import order.bounds
import tactic.monotonicity.basic

/-!
# Linear ordered (semi)fields

A linear ordered (semi)field is a (semi)field equipped with a linear order such that
* addition respects the order: `a ≤ b → c + a ≤ c + b`;
* multiplication of positives is positive: `0 < a → 0 < b → 0 < a * b`;
* `0 < 1`.

## Main Definitions

* `linear_ordered_semifield`: Typeclass for linear order semifields.
* `linear_ordered_field`: Typeclass for linear ordered fields.

## Implementation details

For olean caching reasons, this file is separate to the main file, algebra.order.field.
The lemmata are instead located there.

-/

set_option old_structure_cmd true

/-- A linear ordered semifield is a field with a linear order respecting the operations. -/
@[protect_proj] class linear_ordered_semifield (α : Type*)
  extends linear_ordered_semiring α, semifield α

/-- A linear ordered field is a field with a linear order respecting the operations. -/
@[protect_proj] class linear_ordered_field (α : Type*) extends linear_ordered_comm_ring α, field α

@[priority 100] -- See note [lower instance priority]
instance linear_ordered_field.to_linear_ordered_semifield {α} [linear_ordered_field α] :
  linear_ordered_semifield α :=
{ ..linear_ordered_ring.to_linear_ordered_semiring, ..‹linear_ordered_field α› }
