/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.DistribLattice

/-!
# The category of bounded distributive lattices

This defines `BoundedDistribLattice`, the category of bounded distributive lattices.
-/

universes u v

open category_theory

/-- The category of bounded distributive lattices with bounded lattice morphisms. -/
structure BoundedDistribLattice :=
(X : Type u)
[is_distrib_lattice : distrib_lattice X]
[is_bounded_order : bounded_order X]

namespace BoundedDistribLattice

instance : inhabited BoundedDistribLattice := ⟨⟨bool⟩⟩
instance : has_coe_to_sort BoundedDistribLattice Type* := ⟨BoundedDistribLattice.X⟩

attribute [instance] BoundedDistribLattice.is_distrib_lattice BoundedDistribLattice.is_bounded_order

/-- Construct a bundled `BoundedDistribLattice` from a `bounded_order` `distrib_lattice`. -/
def of (α : Type*) [distrib_lattice α] [bounded_order α] : BoundedDistribLattice := ⟨α⟩

instance : large_category.{u} BoundedDistribLattice :=
{ hom := λ X Y, bounded_lattice_hom X Y,
  id := λ X, bounded_lattice_hom.id X,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, bounded_lattice_hom.comp_id,
  comp_id' := λ X Y, bounded_lattice_hom.id_comp,
  assoc' := λ W X Y Z _ _ _, bounded_lattice_hom.comp_assoc _ _ _ }

instance : concrete_category BoundedDistribLattice :=
{ forget := ⟨coe_sort, λ X Y, coe_fn, λ X, rfl, λ X Y Z f g, rfl⟩,
  forget_faithful := ⟨λ X Y, by convert fun_like.coe_injective⟩ }

instance has_forget_to_DistribLattice : has_forget₂ BoundedDistribLattice DistribLattice :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y, bounded_lattice_hom.to_lattice_hom },
  forget_comp := rfl }

end BoundedDistribLattice
