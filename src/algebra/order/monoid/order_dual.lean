/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/

import algebra.group.order_synonym
import algebra.order.monoid.cancel.defs

/-! # Ordered monoid structures on the order dual.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/

universes u
variables {α : Type u}

open function

namespace order_dual

@[to_additive]
instance contravariant_class_mul_le [has_le α] [has_mul α] [c : contravariant_class α α (*) (≤)] :
  contravariant_class αᵒᵈ αᵒᵈ (*) (≤) :=
⟨c.1.flip⟩

@[to_additive]
instance covariant_class_mul_le [has_le α] [has_mul α] [c : covariant_class α α (*) (≤)] :
  covariant_class αᵒᵈ αᵒᵈ (*) (≤) :=
⟨c.1.flip⟩

@[to_additive] instance contravariant_class_swap_mul_le [has_le α] [has_mul α]
  [c : contravariant_class α α (swap (*)) (≤)] :
  contravariant_class αᵒᵈ αᵒᵈ (swap (*)) (≤) :=
⟨c.1.flip⟩

@[to_additive]
instance covariant_class_swap_mul_le [has_le α] [has_mul α]
  [c : covariant_class α α (swap (*)) (≤)] :
  covariant_class αᵒᵈ αᵒᵈ (swap (*)) (≤) :=
⟨c.1.flip⟩

@[to_additive]
instance contravariant_class_mul_lt [has_lt α] [has_mul α] [c : contravariant_class α α (*) (<)] :
  contravariant_class αᵒᵈ αᵒᵈ (*) (<) :=
⟨c.1.flip⟩

@[to_additive]
instance covariant_class_mul_lt [has_lt α] [has_mul α] [c : covariant_class α α (*) (<)] :
  covariant_class αᵒᵈ αᵒᵈ (*) (<) :=
⟨c.1.flip⟩

@[to_additive] instance contravariant_class_swap_mul_lt [has_lt α] [has_mul α]
  [c : contravariant_class α α (swap (*)) (<)] :
  contravariant_class αᵒᵈ αᵒᵈ (swap (*)) (<) :=
⟨c.1.flip⟩

@[to_additive]
instance covariant_class_swap_mul_lt [has_lt α] [has_mul α]
  [c : covariant_class α α (swap (*)) (<)] :
  covariant_class αᵒᵈ αᵒᵈ (swap (*)) (<) :=
⟨c.1.flip⟩

@[to_additive]
instance [ordered_comm_monoid α] : ordered_comm_monoid αᵒᵈ :=
{ mul_le_mul_left := λ a b h c, mul_le_mul_left' h c,
  .. order_dual.partial_order α,
  .. order_dual.comm_monoid }

@[to_additive ordered_cancel_add_comm_monoid.to_contravariant_class]
instance ordered_cancel_comm_monoid.to_contravariant_class [ordered_cancel_comm_monoid α] :
  contravariant_class αᵒᵈ αᵒᵈ has_mul.mul has_le.le :=
{ elim := λ a b c, ordered_cancel_comm_monoid.le_of_mul_le_mul_left a c b }

@[to_additive]
instance [ordered_cancel_comm_monoid α] : ordered_cancel_comm_monoid αᵒᵈ :=
{ le_of_mul_le_mul_left := λ a b c : α, le_of_mul_le_mul_left',
  .. order_dual.ordered_comm_monoid, .. order_dual.cancel_comm_monoid }

@[to_additive]
instance [linear_ordered_cancel_comm_monoid α] :
  linear_ordered_cancel_comm_monoid αᵒᵈ :=
{ .. order_dual.linear_order α,
  .. order_dual.ordered_cancel_comm_monoid }

@[to_additive]
instance [linear_ordered_comm_monoid α] :
  linear_ordered_comm_monoid αᵒᵈ :=
{ .. order_dual.linear_order α,
  .. order_dual.ordered_comm_monoid }

end order_dual
