/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.order.monoid.defs

/-!
# Ordered cancellative monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

universe u
variables {α : Type u}

open function

set_option old_structure_cmd true

/-- An ordered cancellative additive commutative monoid
is an additive commutative monoid with a partial order,
in which addition is cancellative and monotone. -/
@[protect_proj, ancestor add_comm_monoid partial_order]
class ordered_cancel_add_comm_monoid (α : Type u) extends add_comm_monoid α, partial_order α :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c)

/-- An ordered cancellative commutative monoid
is a commutative monoid with a partial order,
in which multiplication is cancellative and monotone. -/
@[protect_proj, ancestor comm_monoid partial_order, to_additive]
class ordered_cancel_comm_monoid (α : Type u) extends comm_monoid α, partial_order α :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)
(le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c)

section ordered_cancel_comm_monoid
variables [ordered_cancel_comm_monoid α] {a b c d : α}

@[priority 200, to_additive] -- see Note [lower instance priority]
instance ordered_cancel_comm_monoid.to_contravariant_class_le_left :
  contravariant_class α α (*) (≤) :=
⟨ordered_cancel_comm_monoid.le_of_mul_le_mul_left⟩

@[to_additive]
lemma ordered_cancel_comm_monoid.lt_of_mul_lt_mul_left : ∀ a b c : α, a * b < a * c → b < c :=
λ a b c h, lt_of_le_not_le
  (ordered_cancel_comm_monoid.le_of_mul_le_mul_left a b c h.le) $
  mt (λ h, ordered_cancel_comm_monoid.mul_le_mul_left _ _ h _) (not_le_of_gt h)

@[to_additive]
instance ordered_cancel_comm_monoid.to_contravariant_class_left
  (M : Type*) [ordered_cancel_comm_monoid M] :
  contravariant_class M M (*) (<) :=
{ elim := λ a b c, ordered_cancel_comm_monoid.lt_of_mul_lt_mul_left _ _ _ }

/- This instance can be proven with `by apply_instance`.  However, by analogy with the
instance `ordered_cancel_comm_monoid.to_covariant_class_right` above, I imagine that without
this instance, some Type would not have a `contravariant_class M M (function.swap (*)) (<)`
instance. -/
@[to_additive]
instance ordered_cancel_comm_monoid.to_contravariant_class_right
  (M : Type*) [ordered_cancel_comm_monoid M] :
  contravariant_class M M (swap (*)) (<) :=
contravariant_swap_mul_lt_of_contravariant_mul_lt M

@[priority 100, to_additive]    -- see Note [lower instance priority]
instance ordered_cancel_comm_monoid.to_ordered_comm_monoid : ordered_comm_monoid α :=
{ ..‹ordered_cancel_comm_monoid α› }

@[priority 100, to_additive] -- see Note [lower instance priority]
instance ordered_cancel_comm_monoid.to_cancel_comm_monoid : cancel_comm_monoid α :=
{ mul_left_cancel := λ a b c h,
    (le_of_mul_le_mul_left' h.le).antisymm $ le_of_mul_le_mul_left' h.ge,
  ..‹ordered_cancel_comm_monoid α› }

end ordered_cancel_comm_monoid

/-- A linearly ordered cancellative additive commutative monoid
is an additive commutative monoid with a decidable linear order
in which addition is cancellative and monotone. -/
@[protect_proj, ancestor ordered_cancel_add_comm_monoid linear_ordered_add_comm_monoid]
class linear_ordered_cancel_add_comm_monoid (α : Type u)
  extends ordered_cancel_add_comm_monoid α, linear_ordered_add_comm_monoid α

/-- A linearly ordered cancellative commutative monoid
is a commutative monoid with a linear order
in which multiplication is cancellative and monotone. -/
@[protect_proj, ancestor ordered_cancel_comm_monoid linear_ordered_comm_monoid, to_additive]
class linear_ordered_cancel_comm_monoid (α : Type u)
  extends ordered_cancel_comm_monoid α, linear_ordered_comm_monoid α
