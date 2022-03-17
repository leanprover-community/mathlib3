/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.BoundedDistribLattice

/-!
# The category of boolean algebras

This defines `BoolAlg`, the category of boolean algebras.
-/

open order_dual opposite set

universes u

open category_theory

/-- The category of boolean algebras. -/
def BoolAlg := bundled boolean_algebra

namespace BoolAlg

instance : has_coe_to_sort BoolAlg Type* := bundled.has_coe_to_sort
instance (X : BoolAlg) : boolean_algebra X := X.str

/-- Construct a bundled `BoolAlg` from a `boolean_algebra`. -/
def of (α : Type*) [boolean_algebra α] : BoolAlg := bundled.of α

@[simp] lemma coe_of (α : Type*) [boolean_algebra α] : ↥(of α) = α := rfl

instance : inhabited BoolAlg := ⟨of punit⟩

/-- Turn a `BoolAlg` into a `BoundedDistribLattice` by forgetting its complement operation. -/
def to_BoundedDistribLattice (X : BoolAlg) : BoundedDistribLattice := BoundedDistribLattice.of X

instance : large_category.{u} BoolAlg := induced_category.category to_BoundedDistribLattice
instance : concrete_category BoolAlg := induced_category.concrete_category to_BoundedDistribLattice

instance has_forget_to_BoundedDistribLattice : has_forget₂ BoolAlg BoundedDistribLattice :=
induced_category.has_forget₂ to_BoundedDistribLattice

/-- Constructs an equivalence between boolean algebras from an order isomorphism
between them. -/
@[simps] def iso.mk {α β : BoolAlg.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := (e : bounded_lattice_hom α β),
  inv := (e.symm : bounded_lattice_hom β α),
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

/-- `order_dual` as a functor. -/
@[simps] def dual : BoolAlg ⥤ BoolAlg :=
{ obj := λ X, of (order_dual X), map := λ X Y, bounded_lattice_hom.dual }

/-- The equivalence between `BoolAlg` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : BoolAlg ≌ BoolAlg :=
equivalence.mk dual dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end BoolAlg

lemma BoolAlg_dual_comp_forget_to_BoundedDistribLattice :
  BoolAlg.dual ⋙ forget₂ BoolAlg BoundedDistribLattice =
    forget₂ BoolAlg BoundedDistribLattice ⋙ BoundedDistribLattice.dual := rfl
