/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.PartialOrder
import order.hom.lattice

/-!
# The category of lattices

This defines `Lattice`, the category of distributive lattices.
-/

universes u v

open category_theory

/-- The category of lattices. -/
def Lattice := bundled lattice

namespace Lattice

instance : inhabited Lattice := ⟨⟨bool⟩⟩
instance : has_coe_to_sort Lattice Type* := bundled.has_coe_to_sort
instance (X : Lattice) : lattice X := X.str

/-- Construct a bundled `Lattice` from a `lattice`. -/
def of (α : Type*) [lattice α] : Lattice := bundled.of α

instance : bundled_hom @lattice_hom :=
{ to_fun := λ _ _ _ _, coe_fn,
  id := @lattice_hom.id,
  comp := @lattice_hom.comp,
  hom_ext := λ X Y _ _, by exactI fun_like.coe_injective }
instance : large_category.{u} Lattice := category_theory.bundled_hom.category lattice_hom
instance : concrete_category Lattice := category_theory.bundled_hom.concrete_category lattice_hom

instance has_forget_to_PartialOrder : has_forget₂ Lattice PartialOrder :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y f, f },
  forget_comp := rfl }

end Lattice
