/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.group.prod
import algebra.order.monoid.cancel.defs
import algebra.order.monoid.canonical.defs

/-! # Products of ordered monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/

namespace prod

variables {α β M N : Type*}

@[to_additive]
instance [ordered_comm_monoid α] [ordered_comm_monoid β] : ordered_comm_monoid (α × β) :=
{ mul_le_mul_left := λ a b h c, ⟨mul_le_mul_left' h.1 _, mul_le_mul_left' h.2 _⟩,
  .. prod.comm_monoid, .. prod.partial_order _ _ }

@[to_additive]
instance [ordered_cancel_comm_monoid M] [ordered_cancel_comm_monoid N] :
  ordered_cancel_comm_monoid (M × N) :=
{ le_of_mul_le_mul_left := λ a b c h, ⟨le_of_mul_le_mul_left' h.1, le_of_mul_le_mul_left' h.2⟩,
  .. prod.ordered_comm_monoid }

@[to_additive] instance [has_le α] [has_le β] [has_mul α] [has_mul β] [has_exists_mul_of_le α]
  [has_exists_mul_of_le β] : has_exists_mul_of_le (α × β) :=
⟨λ a b h, let ⟨c, hc⟩ := exists_mul_of_le h.1, ⟨d, hd⟩ := exists_mul_of_le h.2 in
  ⟨(c, d), ext hc hd⟩⟩

@[to_additive] instance [canonically_ordered_monoid α] [canonically_ordered_monoid β] :
  canonically_ordered_monoid (α × β) :=
{ le_self_mul := λ a b, ⟨le_self_mul, le_self_mul⟩,
  ..prod.ordered_comm_monoid, ..prod.order_bot _ _, ..prod.has_exists_mul_of_le }

end prod
