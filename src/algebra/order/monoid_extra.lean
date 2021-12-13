/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.group.with_one
import algebra.group.type_tags
import algebra.group.prod
import algebra.order.functions
import algebra.order.monoid_lemmas
import order.bounded_lattice
import order.rel_iso

/-!
# Ordered monoids

This file develops the basics of ordered monoids.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/

open function

universe u
variable {α : Type u}

section semigroup

@[protect_proj]
class ordered_semigroup (α : Type*) extends semigroup α, partial_order α,
  covariant_class α α (*) (≤) :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b :=
  λ a b h c, covariant_class.elim c h)

@[protect_proj]
class ordered_add_semigroup (α : Type*) extends add_semigroup α, partial_order α,
  covariant_class α α (+) (≤) :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b :=
  λ a b h c, covariant_class.elim c h)

attribute [to_additive] ordered_semigroup

@[protect_proj]
class ordered_comm_semigroup (α : Type*) extends ordered_semigroup α :=
(mul_comm : ∀ a b : α, a * b = b * a)

@[protect_proj]
class ordered_add_comm_semigroup (α : Type*) extends ordered_add_semigroup α :=
(add_comm : ∀ a b : α, a + b = b + a)

instance ordered_comm_semigroup.to_comm_semigroup [h : ordered_comm_semigroup α] :
  comm_semigroup α :=
{ ..h }

instance ordered_add_comm_semigroup.to_add_comm_semigroup [h : ordered_add_comm_semigroup α] :
  add_comm_semigroup α :=
{ ..h }

attribute [to_additive] ordered_comm_semigroup ordered_comm_semigroup.to_comm_semigroup

@[protect_proj]
class ordered_left_cancel_semigroup (α : Type*) extends left_cancel_semigroup α, partial_order α,
  covariant_class α α (*) (≤) :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b :=
  λ a b h c, covariant_class.elim c h)

@[protect_proj]
class ordered_add_left_cancel_semigroup (α : Type*) extends add_left_cancel_semigroup α,
  partial_order α, covariant_class α α (+) (≤) :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b :=
  λ a b h c, covariant_class.elim c h)

instance ordered_left_cancel_semigroup.to_ordered_semigroup [h : ordered_left_cancel_semigroup α] :
  ordered_semigroup α :=
{ ..h }

instance ordered_add_left_cancel_semigroup.to_ordered_add_semigroup
  [h : ordered_add_left_cancel_semigroup α] : ordered_add_semigroup α :=
{ ..h }

attribute [to_additive] ordered_left_cancel_semigroup
attribute [to_additive ordered_add_left_cancel_semigroup.to_ordered_add_semigroup]
  ordered_left_cancel_semigroup.to_ordered_semigroup

@[protect_proj]
class ordered_right_cancel_semigroup (α : Type*) extends right_cancel_semigroup α, partial_order α,
  covariant_class α α (*) (≤) :=
(mul_le_mul_right       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b :=
  λ a b h c, covariant_class.elim c h)

@[protect_proj]
class ordered_add_right_cancel_semigroup (α : Type*) extends add_right_cancel_semigroup α,
  partial_order α, covariant_class α α (+) (≤) :=
(add_le_add_right       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b :=
  λ a b h c, covariant_class.elim c h)

instance ordered_right_cancel_semigroup.to_ordered_semigroup [h : ordered_right_cancel_semigroup α] :
  ordered_semigroup α :=
{ ..h }

instance ordered_add_right_cancel_semigroup.to_ordered_add_semigroup
  [h : ordered_add_right_cancel_semigroup α] : ordered_add_semigroup α :=
{ ..h }

attribute [to_additive] ordered_right_cancel_semigroup
attribute [to_additive ordered_add_right_cancel_semigroup.to_ordered_add_semigroup]
  ordered_right_cancel_semigroup.to_ordered_semigroup

end semigroup

@[protect_proj]
class ordered_monoid (α : Type*) extends monoid α, partial_order α,
  covariant_class α α (*) (≤) :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b :=
  λ a b h c, covariant_class.elim c h)

@[protect_proj]
class ordered_add_monoid (α : Type*) extends add_monoid α, partial_order α,
  covariant_class α α (+) (≤) :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b :=
  λ a b h c, covariant_class.elim c h)

instance ordered_monoid.to_ordered_semigroup [h : ordered_monoid α] : ordered_semigroup α :=
{ ..h }

instance ordered_add_monoid.to_ordered_add_semigroup [h : ordered_add_monoid α] :
  ordered_add_semigroup α :=
{ ..h }

attribute [to_additive] ordered_monoid ordered_monoid.to_ordered_semigroup

@[protect_proj]
class ordered_comm_monoid (α : Type*) extends ordered_monoid α :=
(mul_comm : ∀ a b : α, a * b = b * a)

@[protect_proj]
class ordered_add_comm_monoid (α : Type*) extends ordered_add_monoid α :=
(add_comm : ∀ a b : α, a + b = b + a)

instance ordered_comm_monoid.to_comm_monoid [h : ordered_comm_monoid α] :
  comm_monoid α :=
{ ..h }

instance ordered_comm_monoid.to_ordered_comm_semigroup [h : ordered_comm_monoid α] :
  ordered_comm_semigroup α :=
{ ..h }

instance ordered_add_comm_monoid.to_comm_monoid [h : ordered_add_comm_monoid α] :
  add_comm_monoid α :=
{ ..h }

instance ordered_add_comm_monoid.to_ordered_add_comm_semigroup [h : ordered_add_comm_monoid α] :
  ordered_add_comm_semigroup α :=
{ ..h }

attribute [to_additive] ordered_comm_monoid ordered_comm_monoid.to_comm_monoid
  ordered_comm_monoid.to_ordered_comm_semigroup

@[protect_proj]
class ordered_left_cancel_monoid (α : Type*) extends left_cancel_monoid α, partial_order α,
  covariant_class α α (*) (≤) :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b :=
  λ a b h c, covariant_class.elim c h)

@[protect_proj]
class ordered_add_left_cancel_monoid (α : Type*) extends add_left_cancel_monoid α,
  partial_order α, covariant_class α α (+) (≤) :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b :=
  λ a b h c, covariant_class.elim c h)

instance ordered_left_cancel_monoid.to_ordered_monoid [h : ordered_left_cancel_monoid α] :
  ordered_monoid α :=
{ ..h }

instance ordered_add_left_cancel_monoid.to_ordered_add_monoid
  [h : ordered_add_left_cancel_monoid α] : ordered_add_monoid α :=
{ ..h }

instance ordered_left_cancel_monoid.to_ordered_left_cancel_semigroup
  [h : ordered_left_cancel_monoid α] : ordered_left_cancel_semigroup α :=
{ ..h }

instance ordered_add_left_cancel_monoid.to_ordered_add_left_cancel_semigroup
  [h : ordered_add_left_cancel_monoid α] : ordered_add_left_cancel_semigroup α :=
{ ..h }

attribute [to_additive ordered_add_left_cancel_monoid] ordered_left_cancel_monoid
attribute [to_additive ordered_add_left_cancel_monoid.to_ordered_add_monoid]
  ordered_left_cancel_monoid.to_ordered_monoid
attribute [to_additive ordered_add_left_cancel_monoid.to_ordered_add_left_cancel_semigroup]
  ordered_left_cancel_monoid.to_ordered_left_cancel_semigroup

@[protect_proj]
class ordered_right_cancel_monoid (α : Type*) extends right_cancel_monoid α, partial_order α,
  covariant_class α α (*) (≤) :=
(mul_le_mul_right       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b :=
  λ a b h c, covariant_class.elim c h)

@[protect_proj]
class ordered_add_right_cancel_monoid (α : Type*) extends add_right_cancel_monoid α,
  partial_order α, covariant_class α α (+) (≤) :=
(add_le_add_right       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b :=
  λ a b h c, covariant_class.elim c h)

instance ordered_right_cancel_monoid.to_ordered_monoid [h : ordered_right_cancel_monoid α] :
  ordered_monoid α :=
{ ..h }

instance ordered_add_right_cancel_monoid.to_ordered_add_monoid
  [h : ordered_add_right_cancel_monoid α] : ordered_add_monoid α :=
{ ..h }

instance ordered_right_cancel_monoid.to_ordered_right_cancel_semigroup
  [h : ordered_right_cancel_monoid α] : ordered_right_cancel_semigroup α :=
{ ..h }

instance ordered_add_right_cancel_monoid.to_ordered_add_right_cancel_semigroup
  [h : ordered_add_right_cancel_monoid α] : ordered_add_right_cancel_semigroup α :=
{ ..h }

attribute [to_additive ordered_add_right_cancel_monoid] ordered_right_cancel_monoid
attribute [to_additive ordered_add_right_cancel_monoid.to_ordered_add_monoid]
  ordered_right_cancel_monoid.to_ordered_monoid
attribute [to_additive ordered_add_right_cancel_monoid.to_ordered_add_right_cancel_semigroup]
  ordered_right_cancel_monoid.to_ordered_right_cancel_semigroup

@[protect_proj]
class ordered_cancel_monoid (α : Type*) extends cancel_monoid α, partial_order α,
  covariant_class α α (*) (≤) :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b :=
  λ a b h c, covariant_class.elim c h)

@[protect_proj]
class ordered_add_cancel_monoid (α : Type*) extends add_cancel_monoid α,
  partial_order α, covariant_class α α (+) (≤) :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b :=
  λ a b h c, covariant_class.elim c h)

instance ordered_cancel_monoid.to_ordered_left_cancel_monoid [h : ordered_cancel_monoid α] :
  ordered_left_cancel_monoid α :=
{ ..h }

instance ordered_add_cancel_monoid.to_ordered_add_left_cancel_monoid
  [h : ordered_add_cancel_monoid α] : ordered_add_left_cancel_monoid α :=
{ ..h }

instance ordered_cancel_monoid.to_ordered_right_cancel_monoid [h : ordered_cancel_monoid α] :
  ordered_right_cancel_monoid α :=
{ ..h }

instance ordered_add_cancel_monoid.to_ordered_add_right_cancel_monoid
  [h : ordered_add_cancel_monoid α] : ordered_add_right_cancel_monoid α :=
{ ..h }

attribute [to_additive ordered_add_cancel_monoid] ordered_cancel_monoid
attribute [to_additive ordered_add_cancel_monoid.to_ordered_add_left_cancel_monoid]
  ordered_cancel_monoid.to_ordered_left_cancel_monoid
attribute [to_additive ordered_add_cancel_monoid.to_ordered_add_right_cancel_monoid]
  ordered_cancel_monoid.to_ordered_right_cancel_monoid

@[protect_proj]
class ordered_cancel_comm_monoid (α : Type*) extends ordered_cancel_monoid α :=
(mul_comm : ∀ a b : α, a * b = b * a)

@[protect_proj]
class ordered_add_cancel_comm_monoid (α : Type*) extends ordered_add_cancel_monoid α :=
(add_comm : ∀ a b : α, a + b = b + a)

instance ordered_cancel_comm_monoid.to_cancel_comm_monoid [h : ordered_cancel_comm_monoid α] :
  cancel_comm_monoid α :=
{ ..h }

instance ordered_add_cancel_comm_monoid.to_add_cancel_comm_monoid
  [h : ordered_add_cancel_comm_monoid α] : add_cancel_comm_monoid α :=
{ ..h }

attribute [to_additive ordered_add_cancel_comm_monoid] ordered_cancel_comm_monoid
attribute [to_additive ordered_add_cancel_comm_monoid.to_add_cancel_comm_monoid]
  ordered_cancel_comm_monoid.to_cancel_comm_monoid

@[protect_proj]
class ordered_div_inv_monoid (α : Type*) extends div_inv_monoid α, partial_order α,
  covariant_class α α (*) (≤) :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b :=
  λ a b h c, covariant_class.elim c h)

@[protect_proj]
class ordered_sub_neg_monoid (α : Type*) extends sub_neg_monoid α,
  partial_order α, covariant_class α α (+) (≤) :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b :=
  λ a b h c, covariant_class.elim c h)

instance ordered_div_inv_monoid.to_ordered_monoid [h : ordered_div_inv_monoid α] :
  ordered_monoid α :=
{ ..h }

instance ordered_sub_neg_monoid.to_ordered_add_monoid [h : ordered_sub_neg_monoid α] :
  ordered_add_monoid α :=
{ ..h }

attribute [to_additive] ordered_div_inv_monoid
attribute [to_additive ordered_sub_neg_monoid.to_ordered_add_monoid]
  ordered_div_inv_monoid.to_ordered_monoid
