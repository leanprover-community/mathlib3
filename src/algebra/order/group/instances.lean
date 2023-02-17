/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.order.group.defs
import algebra.order.monoid.order_dual

/-!
# Additional instances for ordered commutative groups.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

variables {α : Type*}

@[to_additive] instance [ordered_comm_group α] : ordered_comm_group αᵒᵈ :=
{ .. order_dual.ordered_comm_monoid, .. order_dual.group }

@[to_additive] instance [linear_ordered_comm_group α] :
  linear_ordered_comm_group αᵒᵈ :=
{ .. order_dual.ordered_comm_group, .. order_dual.linear_order α }
