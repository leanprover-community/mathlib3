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

end DistribLattice
