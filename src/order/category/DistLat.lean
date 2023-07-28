/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.Lat

/-!
# The category of distributive lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `DistLat`, the category of distributive lattices.

Note that [`DistLat`](https://ncatlab.org/nlab/show/DistLat) in the literature doesn't always
correspond to `DistLat` as we don't require bottom or top elements. Instead, this `DistLat`
corresponds to `BddDistLat`.
-/

universes u

open category_theory

/-- The category of distributive lattices. -/
def DistLat := bundled distrib_lattice

namespace DistLat

instance : has_coe_to_sort DistLat Type* := bundled.has_coe_to_sort
instance (X : DistLat) : distrib_lattice X := X.str

/-- Construct a bundled `DistLat` from a `distrib_lattice` underlying type and typeclass. -/
def of (α : Type*) [distrib_lattice α] : DistLat := bundled.of α

@[simp] lemma coe_of (α : Type*) [distrib_lattice α] : ↥(of α) = α := rfl

instance : inhabited DistLat := ⟨of punit⟩

instance : bundled_hom.parent_projection @distrib_lattice.to_lattice := ⟨⟩

attribute [derive [large_category, concrete_category]] DistLat

instance has_forget_to_Lat : has_forget₂ DistLat Lat := bundled_hom.forget₂ _ _

/-- Constructs an equivalence between distributive lattices from an order isomorphism between them.
-/
@[simps] def iso.mk {α β : DistLat.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : DistLat ⥤ DistLat :=
{ obj := λ X, of Xᵒᵈ, map := λ X Y, lattice_hom.dual }

/-- The equivalence between `DistLat` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : DistLat ≌ DistLat :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end DistLat

lemma DistLat_dual_comp_forget_to_Lat :
  DistLat.dual ⋙ forget₂ DistLat Lat =
    forget₂ DistLat Lat ⋙ Lat.dual := rfl
