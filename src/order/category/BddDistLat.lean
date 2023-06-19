/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.BddLat
import order.category.DistLat

/-!
# The category of bounded distributive lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `BddDistLat`, the category of bounded distributive lattices.

Note that this category is sometimes called [`DistLat`](https://ncatlab.org/nlab/show/DistLat) when
being a lattice is understood to entail having a bottom and a top element.
-/

universes u

open category_theory

/-- The category of bounded distributive lattices with bounded lattice morphisms. -/
structure BddDistLat :=
(to_DistLat : DistLat)
[is_bounded_order : bounded_order to_DistLat]

namespace BddDistLat

instance : has_coe_to_sort BddDistLat Type* := ⟨λ X, X.to_DistLat⟩
instance (X : BddDistLat) : distrib_lattice X := X.to_DistLat.str

attribute [instance] BddDistLat.is_bounded_order

/-- Construct a bundled `BddDistLat` from a `bounded_order` `distrib_lattice`. -/
def of (α : Type*) [distrib_lattice α] [bounded_order α] : BddDistLat := ⟨⟨α⟩⟩

@[simp] lemma coe_of (α : Type*) [distrib_lattice α] [bounded_order α] : ↥(of α) = α := rfl

instance : inhabited BddDistLat := ⟨of punit⟩

/-- Turn a `BddDistLat` into a `BddLat` by forgetting it is distributive. -/
def to_BddLat (X : BddDistLat) : BddLat := BddLat.of X

@[simp] lemma coe_to_BddLat (X : BddDistLat) : ↥X.to_BddLat = ↥X := rfl

instance : large_category.{u} BddDistLat := induced_category.category to_BddLat

instance : concrete_category BddDistLat :=
induced_category.concrete_category to_BddLat

instance has_forget_to_DistLat : has_forget₂ BddDistLat DistLat :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y, bounded_lattice_hom.to_lattice_hom } }

instance has_forget_to_BddLat : has_forget₂ BddDistLat BddLat :=
induced_category.has_forget₂ to_BddLat

lemma forget_BddLat_Lat_eq_forget_DistLat_Lat :
  forget₂ BddDistLat BddLat ⋙ forget₂ BddLat Lat =
    forget₂ BddDistLat DistLat ⋙ forget₂ DistLat Lat := rfl

/-- Constructs an equivalence between bounded distributive lattices from an order isomorphism
between them. -/
@[simps] def iso.mk {α β : BddDistLat.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := (e : bounded_lattice_hom α β),
  inv := (e.symm : bounded_lattice_hom β α),
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : BddDistLat ⥤ BddDistLat :=
{ obj := λ X, of Xᵒᵈ, map := λ X Y, bounded_lattice_hom.dual }

/-- The equivalence between `BddDistLat` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : BddDistLat ≌ BddDistLat :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end BddDistLat

lemma BddDistLat_dual_comp_forget_to_DistLat :
  BddDistLat.dual ⋙ forget₂ BddDistLat DistLat =
    forget₂ BddDistLat DistLat ⋙ DistLat.dual := rfl
