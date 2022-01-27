/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.fintype.order
import order.category.BoundedDistribLattice

/-!
# The category of boolean algebras

This defines `BoolAlg`, the category of boolean algebras.
-/

universes u v

open category_theory

/-- The category of boolean algebras. -/
def BoolAlg := bundled boolean_algebra

namespace BoolAlg

instance : has_coe_to_sort BoolAlg Type* := bundled.has_coe_to_sort
instance (X : BoolAlg) : boolean_algebra X := X.str

/-- Construct a bundled `BoolAlg` from a `boolean_algebra`. -/
def of (α : Type*) [boolean_algebra α] : BoolAlg := bundled.of α

instance : inhabited BoolAlg := ⟨of punit⟩

-- instance boolean_algebra.to_distrib_lattice.bundled_hom.parent_projection :
--   bundled_hom.parent_projection (λ α _,by exactI boolean_algebra.core.to_distrib_lattice _ :
--     Π α, boolean_algebra α → distrib_lattice α) := ⟨⟩

-- attribute [derive [large_category, concrete_category]] BoolAlg

instance : large_category.{u} BoolAlg :=
{ hom := λ X Y, bounded_lattice_hom X Y,
  id := λ X, bounded_lattice_hom.id X,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, bounded_lattice_hom.comp_id,
  comp_id' := λ X Y, bounded_lattice_hom.id_comp,
  assoc' := λ W X Y Z _ _ _, bounded_lattice_hom.comp_assoc _ _ _ }

instance : concrete_category BoolAlg :=
{ forget := ⟨coe_sort, λ X Y, coe_fn, λ X, rfl, λ X Y Z f g, rfl⟩,
  forget_faithful := ⟨λ X Y, by convert fun_like.coe_injective⟩ }

instance has_forget_to_BoundedDistribLattice : has_forget₂ BoolAlg BoundedDistribLattice :=
{ forget₂ := { obj := λ X, BoundedDistribLattice.of X, map := λ X Y f, f },
  forget_comp := rfl }

end BoolAlg
