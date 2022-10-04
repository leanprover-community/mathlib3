/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.order.monoid.canonically_ordered
import algebra.order.monoid.with_top

/-! # Translating ordered monoids across `additive`/`multiplicative` -/

universes u
variables {α : Type u}

section type_tags

instance : Π [has_le α], has_le (multiplicative α) := id
instance : Π [has_le α], has_le (additive α) := id
instance : Π [has_lt α], has_lt (multiplicative α) := id
instance : Π [has_lt α], has_lt (additive α) := id
instance : Π [preorder α], preorder (multiplicative α) := id
instance : Π [preorder α], preorder (additive α) := id
instance : Π [partial_order α], partial_order (multiplicative α) := id
instance : Π [partial_order α], partial_order (additive α) := id
instance : Π [linear_order α], linear_order (multiplicative α) := id
instance : Π [linear_order α], linear_order (additive α) := id
instance [has_le α] : Π [order_bot α], order_bot (multiplicative α) := id
instance [has_le α] : Π [order_bot α], order_bot (additive α) := id
instance [has_le α] : Π [order_top α], order_top (multiplicative α) := id
instance [has_le α] : Π [order_top α], order_top (additive α) := id
instance [has_le α] : Π [bounded_order α], bounded_order (multiplicative α) := id
instance [has_le α] : Π [bounded_order α], bounded_order (additive α) := id

instance [ordered_add_comm_monoid α] : ordered_comm_monoid (multiplicative α) :=
{ mul_le_mul_left := @ordered_add_comm_monoid.add_le_add_left α _,
  ..multiplicative.partial_order,
  ..multiplicative.comm_monoid }

instance [ordered_comm_monoid α] : ordered_add_comm_monoid (additive α) :=
{ add_le_add_left := @ordered_comm_monoid.mul_le_mul_left α _,
  ..additive.partial_order,
  ..additive.add_comm_monoid }

instance [ordered_cancel_add_comm_monoid α] : ordered_cancel_comm_monoid (multiplicative α) :=
{ le_of_mul_le_mul_left := @ordered_cancel_add_comm_monoid.le_of_add_le_add_left α _,
  ..multiplicative.ordered_comm_monoid }

instance [ordered_cancel_comm_monoid α] : ordered_cancel_add_comm_monoid (additive α) :=
{ le_of_add_le_add_left := @ordered_cancel_comm_monoid.le_of_mul_le_mul_left α _,
  ..additive.ordered_add_comm_monoid }

instance [linear_ordered_add_comm_monoid α] : linear_ordered_comm_monoid (multiplicative α) :=
{ ..multiplicative.linear_order,
  ..multiplicative.ordered_comm_monoid }

instance [linear_ordered_comm_monoid α] : linear_ordered_add_comm_monoid (additive α) :=
{ ..additive.linear_order,
  ..additive.ordered_add_comm_monoid }

instance [has_add α] [has_le α] [has_exists_add_of_le α] :
  has_exists_mul_of_le (multiplicative α) :=
⟨@exists_add_of_le α _ _ _⟩

instance [has_mul α] [has_le α] [has_exists_mul_of_le α] : has_exists_add_of_le (additive α) :=
⟨@exists_mul_of_le α _ _ _⟩

instance [canonically_ordered_add_monoid α] : canonically_ordered_monoid (multiplicative α) :=
{ le_self_mul := @le_self_add α _,
  ..multiplicative.ordered_comm_monoid, ..multiplicative.order_bot,
  ..multiplicative.has_exists_mul_of_le }

instance [canonically_ordered_monoid α] : canonically_ordered_add_monoid (additive α) :=
{ le_self_add := @le_self_mul α _,
  ..additive.ordered_add_comm_monoid, ..additive.order_bot, ..additive.has_exists_add_of_le }

instance [canonically_linear_ordered_add_monoid α] :
  canonically_linear_ordered_monoid (multiplicative α) :=
{ ..multiplicative.canonically_ordered_monoid, ..multiplicative.linear_order }

instance [canonically_linear_ordered_monoid α] :
  canonically_linear_ordered_add_monoid (additive α) :=
{ ..additive.canonically_ordered_add_monoid, ..additive.linear_order }

namespace additive

variables [preorder α]

@[simp] lemma of_mul_le {a b : α} : of_mul a ≤ of_mul b ↔ a ≤ b := iff.rfl

@[simp] lemma of_mul_lt {a b : α} : of_mul a < of_mul b ↔ a < b := iff.rfl

@[simp] lemma to_mul_le {a b : additive α} : to_mul a ≤ to_mul b ↔ a ≤ b := iff.rfl

@[simp] lemma to_mul_lt {a b : additive α} : to_mul a < to_mul b ↔ a < b := iff.rfl

end additive

namespace multiplicative

variables [preorder α]

@[simp] lemma of_add_le {a b : α} : of_add a ≤ of_add b ↔ a ≤ b := iff.rfl

@[simp] lemma of_add_lt {a b : α} : of_add a < of_add b ↔ a < b := iff.rfl

@[simp] lemma to_add_le {a b : multiplicative α} : to_add a ≤ to_add b ↔ a ≤ b := iff.rfl

@[simp] lemma to_add_lt {a b : multiplicative α} : to_add a < to_add b ↔ a < b := iff.rfl

end multiplicative

end type_tags

namespace with_zero

local attribute [semireducible] with_zero
variables [has_add α]

/-- Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative. -/
def to_mul_bot : with_zero (multiplicative α) ≃* multiplicative (with_bot α) :=
by exact mul_equiv.refl _

@[simp] lemma to_mul_bot_zero :
  to_mul_bot (0 : with_zero (multiplicative α)) = multiplicative.of_add ⊥ := rfl
@[simp] lemma to_mul_bot_coe (x : multiplicative α) :
  to_mul_bot ↑x = multiplicative.of_add (x.to_add : with_bot α) := rfl
@[simp] lemma to_mul_bot_symm_bot :
  to_mul_bot.symm (multiplicative.of_add (⊥ : with_bot α)) = 0 := rfl
@[simp] lemma to_mul_bot_coe_of_add (x : α) :
  to_mul_bot.symm (multiplicative.of_add (x : with_bot α)) = multiplicative.of_add x := rfl

variables [preorder α] (a b : with_zero (multiplicative α))

lemma to_mul_bot_strict_mono : strict_mono (@to_mul_bot α _) := λ x y, id
@[simp] lemma to_mul_bot_le : to_mul_bot a ≤ to_mul_bot b ↔ a ≤ b := iff.rfl
@[simp] lemma to_mul_bot_lt : to_mul_bot a < to_mul_bot b ↔ a < b := iff.rfl

end with_zero
