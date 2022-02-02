/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.Lattice

/-!
# The category of distributive lattices

This defines `DistribLattice`, the category of distributive lattices.
-/

universes u v

open category_theory

/-- The category of distributive lattices. -/
def DistribLattice := bundled distrib_lattice

namespace DistribLattice

instance : inhabited DistribLattice := ⟨⟨bool⟩⟩
instance : has_coe_to_sort DistribLattice Type* := bundled.has_coe_to_sort
instance (X : DistribLattice) : distrib_lattice X := X.str

/-- Construct a bundled `DistribLattice` from a `distrib_lattice` underlying type and typeclass. -/
def of (α : Type*) [distrib_lattice α] : DistribLattice := bundled.of α

instance : bundled_hom.parent_projection @distrib_lattice.to_lattice := ⟨⟩

attribute [derive [large_category, concrete_category]] DistribLattice

instance has_forget_to_Lattice : has_forget₂ DistribLattice Lattice := bundled_hom.forget₂ _ _

/-- Constructs an equivalence between distributive lattices from an order isomorphism between them.
-/
@[simps] def iso.mk {α β : DistribLattice.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply x },
  inv_hom_id' := by { ext, exact e.apply_symm_apply x } }

/-- `order_dual` as a functor. -/
@[simps] def to_dual : DistribLattice ⥤ DistribLattice :=
{ obj := λ X, of (order_dual X), map := λ X Y, order_hom.dual }

/-- The equivalence between `DistribLattice` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : DistribLattice ≌ DistribLattice :=
equivalence.mk to_dual to_dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end DistribLattice

lemma DistribLattice_to_dual_comp_forget_to_Lattice :
  DistribLattice.to_dual ⋙ forget₂ DistribLattice Lattice =
    forget₂ DistribLattice Lattice ⋙ Lattice.to_dual := rfl
