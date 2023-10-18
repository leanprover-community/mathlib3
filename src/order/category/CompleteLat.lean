/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.BddLat
import order.hom.complete_lattice

/-!
# The category of complete lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `CompleteLat`, the category of complete lattices.
-/

universes u

open category_theory

/-- The category of complete lattices. -/
def CompleteLat := bundled complete_lattice

namespace CompleteLat

instance : has_coe_to_sort CompleteLat Type* := bundled.has_coe_to_sort
instance (X : CompleteLat) : complete_lattice X := X.str

/-- Construct a bundled `CompleteLat` from a `complete_lattice`. -/
def of (α : Type*) [complete_lattice α] : CompleteLat := bundled.of α

@[simp] lemma coe_of (α : Type*) [complete_lattice α] : ↥(of α) = α := rfl

instance : inhabited CompleteLat := ⟨of punit⟩

instance : bundled_hom @complete_lattice_hom :=
{ to_fun := λ _ _ _ _, coe_fn,
  id := @complete_lattice_hom.id,
  comp := @complete_lattice_hom.comp,
  hom_ext := λ X Y _ _, by exactI fun_like.coe_injective }
instance : large_category.{u} CompleteLat := bundled_hom.category complete_lattice_hom
instance : concrete_category CompleteLat := bundled_hom.concrete_category complete_lattice_hom

instance has_forget_to_BddLat : has_forget₂ CompleteLat BddLat :=
{ forget₂ := { obj := λ X, BddLat.of X,
               map := λ X Y, complete_lattice_hom.to_bounded_lattice_hom },
  forget_comp := rfl }

/-- Constructs an isomorphism of complete lattices from an order isomorphism between them. -/
@[simps] def iso.mk {α β : CompleteLat.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : CompleteLat ⥤ CompleteLat :=
{ obj := λ X, of Xᵒᵈ, map := λ X Y, complete_lattice_hom.dual }

/-- The equivalence between `CompleteLat` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : CompleteLat ≌ CompleteLat :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end CompleteLat

lemma CompleteLat_dual_comp_forget_to_BddLat :
  CompleteLat.dual ⋙ forget₂ CompleteLat BddLat =
    forget₂ CompleteLat BddLat ⋙ BddLat.dual := rfl
