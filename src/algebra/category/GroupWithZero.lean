/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import category_theory.category.Bipointed
import algebra.category.Mon.basic

/-!
# The category of groups with zero

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `GroupWithZero`, the category of groups with zero.
-/

universes u

open category_theory order

/-- The category of groups with zero. -/
def GroupWithZero := bundled group_with_zero

namespace GroupWithZero

instance : has_coe_to_sort GroupWithZero Type* := bundled.has_coe_to_sort
instance (X : GroupWithZero) : group_with_zero X := X.str

/-- Construct a bundled `GroupWithZero` from a `group_with_zero`. -/
def of (α : Type*) [group_with_zero α] : GroupWithZero := bundled.of α

instance : inhabited GroupWithZero := ⟨of (with_zero punit)⟩

instance : large_category.{u} GroupWithZero :=
{ hom := λ X Y, monoid_with_zero_hom X Y,
  id := λ X, monoid_with_zero_hom.id X,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, monoid_with_zero_hom.comp_id,
  comp_id' := λ X Y, monoid_with_zero_hom.id_comp,
  assoc' := λ W X Y Z _ _ _, monoid_with_zero_hom.comp_assoc _ _ _ }

instance : concrete_category GroupWithZero :=
{ forget := ⟨coe_sort, λ X Y, coe_fn, λ X, rfl, λ X Y Z f g, rfl⟩,
  forget_faithful := ⟨λ X Y f g h, fun_like.coe_injective h⟩ }

instance has_forget_to_Bipointed : has_forget₂ GroupWithZero Bipointed :=
{ forget₂ := { obj := λ X, ⟨X, 0, 1⟩, map := λ X Y f, ⟨f, f.map_zero', f.map_one'⟩ } }

instance has_forget_to_Mon : has_forget₂ GroupWithZero Mon :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y, monoid_with_zero_hom.to_monoid_hom } }

/-- Constructs an isomorphism of groups with zero from a group isomorphism between them. -/
@[simps] def iso.mk {α β : GroupWithZero.{u}} (e : α ≃* β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

end GroupWithZero
