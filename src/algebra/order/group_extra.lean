/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.order.monoid_extra
import order.order_dual
import algebra.abs

/-!
# Ordered groups

This file develops the basics of ordered groups.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/

open function

universe u
variable {α : Type u}

@[to_additive]
instance group.covariant_class_le.to_contravariant_class_le
  [group α] [has_le α] [covariant_class α α (*) (≤)] : contravariant_class α α (*) (≤) :=
group.covconv

@[to_additive]
instance group.swap.covariant_class_le.to_contravariant_class_le [group α] [has_le α]
  [covariant_class α α (swap (*)) (≤)] : contravariant_class α α (swap (*)) (≤) :=
{ elim := λ a b c bc, calc  b = b * a * a⁻¹ : eq_mul_inv_of_mul_eq rfl
                          ... ≤ c * a * a⁻¹ : mul_le_mul_right' bc a⁻¹
                          ... = c           : mul_inv_eq_of_eq_mul rfl }

@[to_additive]
instance group.covariant_class_lt.to_contravariant_class_lt
  [group α] [has_lt α] [covariant_class α α (*) (<)] : contravariant_class α α (*) (<) :=
{ elim := λ a b c bc, calc  b = a⁻¹ * (a * b) : eq_inv_mul_of_mul_eq rfl
                          ... < a⁻¹ * (a * c) : mul_lt_mul_left' bc a⁻¹
                          ... = c             : inv_mul_cancel_left a c }

@[to_additive]
instance group.swap.covariant_class_lt.to_contravariant_class_lt [group α] [has_lt α]
  [covariant_class α α (swap (*)) (<)] : contravariant_class α α (swap (*)) (<) :=
{ elim := λ a b c bc, calc  b = b * a * a⁻¹ : eq_mul_inv_of_mul_eq rfl
                          ... < c * a * a⁻¹ : mul_lt_mul_right' bc a⁻¹
                          ... = c           : mul_inv_eq_of_eq_mul rfl }

@[protect_proj]
class ordered_group (α : Type*) extends group α, partial_order α,
  covariant_class α α (*) (≤) :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b :=
  λ a b h c, covariant_class.elim c h)

@[protect_proj]
class ordered_add_group (α : Type*) extends add_group α, partial_order α,
  covariant_class α α (+) (≤) :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b :=
  λ a b h c, covariant_class.elim c h)

instance ordered_group.to_ordered_div_inv_monoid [h : ordered_group α] : ordered_div_inv_monoid α :=
{ ..h }

instance ordered_add_group.to_ordered_sub_neg_monoid [h : ordered_add_group α] :
  ordered_sub_neg_monoid α :=
{ ..h }

instance ordered_group.to_ordered_cancel_monoid [h : ordered_group α] : ordered_cancel_monoid α :=
{ ..h }

instance ordered_add_group.to_ordered_add_cancel_monoid [h : ordered_add_group α] :
  ordered_add_cancel_monoid α :=
{ ..h }

attribute [to_additive] ordered_group
attribute [to_additive ordered_add_group.to_ordered_sub_neg_monoid]
  ordered_group.to_ordered_div_inv_monoid
attribute [to_additive ordered_add_group.to_ordered_add_cancel_monoid]
  ordered_group.to_ordered_cancel_monoid

@[protect_proj]
class ordered_comm_group (α : Type*) extends ordered_group α :=
(mul_comm : ∀ a b : α, a * b = b * a)

@[protect_proj]
class ordered_add_comm_group (α : Type*) extends ordered_add_group α :=
(add_comm : ∀ a b : α, a + b = b + a)

instance ordered_comm_group.to_comm_group [h : ordered_comm_group α] :
  comm_group α :=
{ ..h }

instance ordered_add_comm_group.to_comm_group [h : ordered_add_comm_group α] :
  add_comm_group α :=
{ ..h }

instance ordered_comm_group.to_ordered_cancel_comm_monoid [h : ordered_comm_group α] :
  ordered_cancel_comm_monoid α :=
{ ..h }

instance ordered_add_comm_group.to_ordered_add_cancel_comm_monoid [h : ordered_add_comm_group α] :
  ordered_add_cancel_comm_monoid α :=
{ ..h }

attribute [to_additive] ordered_comm_group ordered_comm_group.to_comm_group
attribute [to_additive ordered_add_comm_group.to_ordered_add_cancel_comm_monoid]
  ordered_comm_group.to_ordered_cancel_comm_monoid
