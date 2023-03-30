/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.order.group.instances
import algebra.order.monoid.type_tags

/-! # Ordered group structures on `multiplicative α` and `additive α`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/

variables {α : Type*}

instance [ordered_add_comm_group α] : ordered_comm_group (multiplicative α) :=
{ ..multiplicative.comm_group,
  ..multiplicative.ordered_comm_monoid }

instance [ordered_comm_group α] : ordered_add_comm_group (additive α) :=
{ ..additive.add_comm_group,
  ..additive.ordered_add_comm_monoid }

instance [linear_ordered_add_comm_group α] : linear_ordered_comm_group (multiplicative α) :=
{ ..multiplicative.linear_order,
  ..multiplicative.ordered_comm_group }

instance [linear_ordered_comm_group α] : linear_ordered_add_comm_group (additive α) :=
{ ..additive.linear_order,
  ..additive.ordered_add_comm_group }
