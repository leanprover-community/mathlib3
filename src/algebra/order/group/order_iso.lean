/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.order.group.defs
import algebra.hom.equiv.units.basic

/-!
# Inverse and multiplication as order isomorphisms in ordered groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

set_option old_structure_cmd true
open function

universe u
variable {α : Type u}


section group
variables [group α]

section typeclasses_left_right_le
variables [has_le α] [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (≤)]
  {a b c d : α}

section

variable (α)

/-- `x ↦ x⁻¹` as an order-reversing equivalence. -/
@[to_additive "`x ↦ -x` as an order-reversing equivalence.", simps]
def order_iso.inv : α ≃o αᵒᵈ :=
{ to_equiv := (equiv.inv α).trans order_dual.to_dual,
  map_rel_iff' := λ a b, @inv_le_inv_iff α _ _ _ _ _ _ }

end

@[to_additive neg_le]
lemma inv_le' : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
(order_iso.inv α).symm_apply_le

alias inv_le' ↔ inv_le_of_inv_le' _
attribute [to_additive neg_le_of_neg_le] inv_le_of_inv_le'

@[to_additive le_neg]
lemma le_inv' : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
(order_iso.inv α).le_symm_apply

end typeclasses_left_right_le

end group

alias le_inv' ↔ le_inv_of_le_inv _
attribute [to_additive] le_inv_of_le_inv

section group
variables [group α] [has_le α]

section right
variables [covariant_class α α (swap (*)) (≤)] {a b c d : α}

/-- `equiv.mul_right` as an `order_iso`. See also `order_embedding.mul_right`. -/
@[to_additive "`equiv.add_right` as an `order_iso`. See also `order_embedding.add_right`.",
  simps to_equiv apply {simp_rhs := tt}]
def order_iso.mul_right (a : α) : α ≃o α :=
{ map_rel_iff' := λ _ _, mul_le_mul_iff_right a, to_equiv := equiv.mul_right a }

@[simp, to_additive] lemma order_iso.mul_right_symm (a : α) :
  (order_iso.mul_right a).symm = order_iso.mul_right a⁻¹ :=
by { ext x, refl }

end right

section left
variables [covariant_class α α (*) (≤)]

/-- `equiv.mul_left` as an `order_iso`. See also `order_embedding.mul_left`. -/
@[to_additive "`equiv.add_left` as an `order_iso`. See also `order_embedding.add_left`.",
  simps to_equiv apply  {simp_rhs := tt}]
def order_iso.mul_left (a : α) : α ≃o α :=
{ map_rel_iff' := λ _ _, mul_le_mul_iff_left a, to_equiv := equiv.mul_left a }

@[simp, to_additive] lemma order_iso.mul_left_symm (a : α) :
  (order_iso.mul_left a).symm = order_iso.mul_left a⁻¹ :=
by { ext x, refl }

end left

end group
