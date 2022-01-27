/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.BoolAlg
import order.category.FinDistribLattice

/-!
# The category of finite boolean algebras

This defines `FinBoolAlg`, the category of finite boolean algebras.
-/

universes u v

open category_theory

/-- The category of finite boolean algebras with bounded lattice morphisms. -/
structure FinBoolAlg :=
(to_BoolAlg : BoolAlg)
[is_fintype : fintype to_BoolAlg]

namespace FinBoolAlg
instance : has_coe_to_sort FinBoolAlg Type* := ⟨λ X, X.to_BoolAlg⟩
instance (X : FinBoolAlg) : boolean_algebra X := X.to_BoolAlg.str

attribute [instance]  FinBoolAlg.is_fintype

/-- Construct a bundled `FinBoolAlg` from a `bounded_order` `distrib_lattice`. -/
def of (α : Type*) [boolean_algebra α] [fintype α] : FinBoolAlg := ⟨⟨α⟩⟩

instance : inhabited FinBoolAlg := ⟨of bool⟩

instance : large_category.{u} FinBoolAlg :=
{ hom := λ X Y, bounded_lattice_hom X Y,
  id := λ X, bounded_lattice_hom.id X,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, bounded_lattice_hom.comp_id,
  comp_id' := λ X Y, bounded_lattice_hom.id_comp,
  assoc' := λ W X Y Z _ _ _, bounded_lattice_hom.comp_assoc _ _ _ }

instance : concrete_category FinBoolAlg :=
{ forget := ⟨coe_sort, λ X Y, coe_fn, λ X, rfl, λ X Y Z f g, rfl⟩,
  forget_faithful := ⟨λ X Y, by convert fun_like.coe_injective⟩ }

instance has_forget_to_BoundedDistribLattice : has_forget₂ FinBoolAlg BoundedDistribLattice :=
{ forget₂ := { obj := λ X, ⟨⟨X⟩⟩, map := λ X Y, id },
  forget_comp := rfl }

instance has_forget_to_FinPartialOrder : has_forget₂ FinBoolAlg FinPartialOrder :=
{ forget₂ := { obj := λ X, ⟨⟨X⟩⟩, map := λ X Y f, f },
  forget_comp := rfl }

end FinBoolAlg
