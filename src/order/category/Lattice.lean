/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.PartialOrder
import order.hom.lattice

/-!
# The category of lattices

This defines `Lattice`, the category of lattices.

Note that `Lattice` doesn't correspond to the literature definition of [`Lat`]
(https://ncatlab.org/nlab/show/Lat) as we don't require bottom or top elements. Instead, `Lat`
corresponds to `BoundedLattice` (not yet in mathlib).

## TODO

The free functor from `Lattice` to `BoundedLattice` is `X → with_top (with_bot X)`.
-/

universes u

open category_theory

/-- The category of lattices. -/
def Lattice := bundled lattice

namespace Lattice

instance : has_coe_to_sort Lattice Type* := bundled.has_coe_to_sort
instance (X : Lattice) : lattice X := X.str

/-- Construct a bundled `Lattice` from a `lattice`. -/
def of (α : Type*) [lattice α] : Lattice := bundled.of α

@[simp] lemma coe_of (α : Type*) [lattice α] : ↥(of α) = α := rfl

instance : inhabited Lattice := ⟨of bool⟩

instance : bundled_hom @lattice_hom :=
{ to_fun := λ _ _ _ _, coe_fn,
  id := @lattice_hom.id,
  comp := @lattice_hom.comp,
  hom_ext := λ X Y _ _, by exactI fun_like.coe_injective }

instance : large_category.{u} Lattice := bundled_hom.category lattice_hom
instance : concrete_category Lattice := bundled_hom.concrete_category lattice_hom

instance has_forget_to_PartialOrder : has_forget₂ Lattice PartialOrder :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y f, f },
  forget_comp := rfl }

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps] def iso.mk {α β : Lattice.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : Lattice ⥤ Lattice :=
{ obj := λ X, of (order_dual X), map := λ X Y, lattice_hom.dual }

/-- The equivalence between `Lattice` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : Lattice ≌ Lattice :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end Lattice

lemma Lattice_dual_comp_forget_to_PartialOrder :
  Lattice.dual ⋙ forget₂ Lattice PartialOrder =
    forget₂ Lattice PartialOrder ⋙ PartialOrder.dual := rfl
