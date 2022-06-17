/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.BoundedLattice
import order.category.DistribLattice

/-!
# The category of bounded distributive lattices

This defines `BoundedDistribLattice`, the category of bounded distributive lattices.

Note that this category is sometimes called [`DistLat`](https://ncatlab.org/nlab/show/DistLat) when
being a lattice is understood to entail having a bottom and a top element.
-/

universes u

open category_theory

/-- The category of bounded distributive lattices with bounded lattice morphisms. -/
structure BoundedDistribLattice :=
(to_DistribLattice : DistribLattice)
[is_bounded_order : bounded_order to_DistribLattice]

namespace BoundedDistribLattice

instance : has_coe_to_sort BoundedDistribLattice Type* := ⟨λ X, X.to_DistribLattice⟩
instance (X : BoundedDistribLattice) : distrib_lattice X := X.to_DistribLattice.str

attribute [instance] BoundedDistribLattice.is_bounded_order

/-- Construct a bundled `BoundedDistribLattice` from a `bounded_order` `distrib_lattice`. -/
def of (α : Type*) [distrib_lattice α] [bounded_order α] : BoundedDistribLattice := ⟨⟨α⟩⟩

@[simp] lemma coe_of (α : Type*) [distrib_lattice α] [bounded_order α] : ↥(of α) = α := rfl

instance : inhabited BoundedDistribLattice := ⟨of punit⟩

/-- Turn a `BoundedDistribLattice` into a `BoundedLattice` by forgetting it is distributive. -/
def to_BoundedLattice (X : BoundedDistribLattice) : BoundedLattice := BoundedLattice.of X

@[simp] lemma coe_to_BoundedLattice (X : BoundedDistribLattice) : ↥X.to_BoundedLattice = ↥X := rfl

instance : large_category.{u} BoundedDistribLattice := induced_category.category to_BoundedLattice

instance : concrete_category BoundedDistribLattice :=
induced_category.concrete_category to_BoundedLattice

instance has_forget_to_DistribLattice : has_forget₂ BoundedDistribLattice DistribLattice :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y, bounded_lattice_hom.to_lattice_hom } }

instance has_forget_to_BoundedLattice : has_forget₂ BoundedDistribLattice BoundedLattice :=
induced_category.has_forget₂ to_BoundedLattice

lemma forget_BoundedLattice_Lattice_eq_forget_DistribLattice_Lattice :
  forget₂ BoundedDistribLattice BoundedLattice ⋙ forget₂ BoundedLattice Lattice =
    forget₂ BoundedDistribLattice DistribLattice ⋙ forget₂ DistribLattice Lattice := rfl

/-- Constructs an equivalence between bounded distributive lattices from an order isomorphism
between them. -/
@[simps] def iso.mk {α β : BoundedDistribLattice.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := (e : bounded_lattice_hom α β),
  inv := (e.symm : bounded_lattice_hom β α),
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : BoundedDistribLattice ⥤ BoundedDistribLattice :=
{ obj := λ X, of Xᵒᵈ, map := λ X Y, bounded_lattice_hom.dual }

/-- The equivalence between `BoundedDistribLattice` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : BoundedDistribLattice ≌ BoundedDistribLattice :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end BoundedDistribLattice

lemma BoundedDistribLattice_dual_comp_forget_to_DistribLattice :
  BoundedDistribLattice.dual ⋙ forget₂ BoundedDistribLattice DistribLattice =
    forget₂ BoundedDistribLattice DistribLattice ⋙ DistribLattice.dual := rfl
