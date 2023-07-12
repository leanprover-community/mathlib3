/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import algebra.field.defs
import algebra.order.ring.defs

/-!
# Linear ordered (semi)fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A linear ordered (semi)field is a (semi)field equipped with a linear order such that
* addition respects the order: `a ≤ b → c + a ≤ c + b`;
* multiplication of positives is positive: `0 < a → 0 < b → 0 < a * b`;
* `0 < 1`.

## Main Definitions

* `linear_ordered_semifield`: Typeclass for linear order semifields.
* `linear_ordered_field`: Typeclass for linear ordered fields.

## Implementation details

For olean caching reasons, this file is separate to the main file, `algebra.order.field.basic`.
The lemmata are instead located there.

-/

set_option old_structure_cmd true

variables {α : Type*}

/-- A linear ordered semifield is a field with a linear order respecting the operations. -/
@[protect_proj, ancestor linear_ordered_comm_semiring semifield]
class linear_ordered_semifield (α : Type*) extends linear_ordered_comm_semiring α, semifield α

/-- A linear ordered field is a field with a linear order respecting the operations. -/
@[protect_proj, ancestor linear_ordered_comm_ring field]
class linear_ordered_field (α : Type*) extends linear_ordered_comm_ring α, field α

@[priority 100] -- See note [lower instance priority]
instance linear_ordered_field.to_linear_ordered_semifield [linear_ordered_field α] :
  linear_ordered_semifield α :=
{ ..linear_ordered_ring.to_linear_ordered_semiring, ..‹linear_ordered_field α› }

-- Guard against import creep.
assert_not_exists monoid_hom
