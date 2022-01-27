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

instance large_category : large_category FinBoolAlg :=
induced_category.category FinBoolAlg.to_BoolAlg

instance concrete_category : concrete_category FinBoolAlg :=
induced_category.concrete_category FinBoolAlg.to_BoolAlg

instance has_forget_to_BoolAlg : has_forget₂ FinBoolAlg BoolAlg :=
induced_category.has_forget₂ FinBoolAlg.to_BoolAlg

instance has_forget_to_FinPartialOrder : has_forget₂ FinBoolAlg FinPartialOrder :=
{ forget₂ := { obj := λ X, ⟨⟨X⟩⟩, map := λ X Y f, f },
  forget_comp := rfl }

end FinBoolAlg
