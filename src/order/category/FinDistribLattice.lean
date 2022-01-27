/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.fintype.order
import order.category.BoundedDistribLattice
import order.category.FinPartialOrder

/-!
# The category of finite distributive lattices

This defines `FinDistribLattice`, the category of finite distributive lattices.
-/

universes u v

open category_theory

instance : distrib_lattice bool := linear_order.to_distrib_lattice

/-- The category of finite distributive lattices with bounded lattice morphisms. -/
structure FinDistribLattice :=
(to_BoundedDistribLattice : BoundedDistribLattice)
[is_fintype : fintype to_BoundedDistribLattice]

namespace FinDistribLattice

instance : has_coe_to_sort FinDistribLattice Type* := ⟨λ X, X.to_BoundedDistribLattice⟩
instance (X : FinDistribLattice) : distrib_lattice X :=
X.to_BoundedDistribLattice.to_DistribLattice.str
instance (X : FinDistribLattice) : bounded_order X := X.to_BoundedDistribLattice.is_bounded_order

attribute [instance]  FinDistribLattice.is_fintype

/-- Construct a bundled `FinDistribLattice` from a `fintype` `bounded_order` `distrib_lattice`. -/
def of (α : Type*) [distrib_lattice α] [bounded_order α] [fintype α] : FinDistribLattice := ⟨⟨⟨α⟩⟩⟩

/-- Construct a bundled `FinDistribLattice` from a `nonempty` `bounded_order` `distrib_lattice`. -/
def of' (α : Type*) [distrib_lattice α] [fintype α] [nonempty α] : FinDistribLattice :=
by { haveI := fintype.to_bounded_order α, exact ⟨⟨⟨α⟩⟩⟩ }

instance : inhabited FinDistribLattice := ⟨of bool⟩

instance : large_category.{u} FinDistribLattice :=
{ hom := λ X Y, bounded_lattice_hom X Y,
  id := λ X, bounded_lattice_hom.id X,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, bounded_lattice_hom.comp_id,
  comp_id' := λ X Y, bounded_lattice_hom.id_comp,
  assoc' := λ W X Y Z _ _ _, bounded_lattice_hom.comp_assoc _ _ _ }

instance : concrete_category FinDistribLattice :=
{ forget := ⟨coe_sort, λ X Y, coe_fn, λ X, rfl, λ X Y Z f g, rfl⟩,
  forget_faithful := ⟨λ X Y, by convert fun_like.coe_injective⟩ }

instance has_forget_to_BoundedDistribLattice :
  has_forget₂ FinDistribLattice BoundedDistribLattice :=
{ forget₂ := { obj := λ X, BoundedDistribLattice.of X, map := λ X Y, id },
  forget_comp := rfl }

instance has_forget_to_FinPartialOrder : has_forget₂ FinDistribLattice FinPartialOrder :=
{ forget₂ := { obj := λ X, ⟨⟨X⟩⟩, map := λ X Y f, f },
  forget_comp := rfl }

end FinDistribLattice
