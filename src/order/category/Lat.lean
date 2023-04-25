/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.PartOrd
import order.hom.lattice

/-!
# The category of lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `Lat`, the category of lattices.

Note that `Lat` doesn't correspond to the literature definition of [`Lat`]
(https://ncatlab.org/nlab/show/Lat) as we don't require bottom or top elements. Instead, `Lat`
corresponds to `BddLat`.

## TODO

The free functor from `Lat` to `BddLat` is `X → with_top (with_bot X)`.
-/

universes u

open category_theory

/-- The category of lattices. -/
def Lat := bundled lattice

namespace Lat

instance : has_coe_to_sort Lat Type* := bundled.has_coe_to_sort
instance (X : Lat) : lattice X := X.str

/-- Construct a bundled `Lat` from a `lattice`. -/
def of (α : Type*) [lattice α] : Lat := bundled.of α

@[simp] lemma coe_of (α : Type*) [lattice α] : ↥(of α) = α := rfl

instance : inhabited Lat := ⟨of bool⟩

instance : bundled_hom @lattice_hom :=
{ to_fun := λ _ _ _ _, coe_fn,
  id := @lattice_hom.id,
  comp := @lattice_hom.comp,
  hom_ext := λ X Y _ _, by exactI fun_like.coe_injective }

instance : large_category.{u} Lat := bundled_hom.category lattice_hom
instance : concrete_category Lat := bundled_hom.concrete_category lattice_hom

instance has_forget_to_PartOrd : has_forget₂ Lat PartOrd :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y f, f },
  forget_comp := rfl }

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps] def iso.mk {α β : Lat.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : Lat ⥤ Lat := { obj := λ X, of Xᵒᵈ, map := λ X Y, lattice_hom.dual }

/-- The equivalence between `Lat` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : Lat ≌ Lat :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end Lat

lemma Lat_dual_comp_forget_to_PartOrd :
  Lat.dual ⋙ forget₂ Lat PartOrd =
    forget₂ Lat PartOrd ⋙ PartOrd.dual := rfl
