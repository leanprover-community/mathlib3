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

instance has_forget_to_FinDistribLattice : has_forget₂ FinBoolAlg FinDistribLattice :=
{ forget₂ := { obj := λ X, FinDistribLattice.of X, map := λ X Y f, f },
  forget_comp := rfl }

/-- Constructs an equivalence between finite Boolean algebras from an order isomorphism between
them. -/
@[simps] def iso.mk {α β : FinBoolAlg.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply x },
  inv_hom_id' := by { ext, exact e.apply_symm_apply x } }

/-- `order_dual` as a functor. -/
@[simps] def to_dual : FinBoolAlg ⥤ FinBoolAlg :=
{ obj := λ X, of (order_dual X), map := λ X Y, order_hom.dual }

/-- The equivalence between `FinBoolAlg` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : FinBoolAlg ≌ FinBoolAlg :=
equivalence.mk to_dual to_dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end FinBoolAlg

lemma FinBoolAlg_to_dual_comp_forget_to_FinDistribLattice :
  FinBoolAlg.to_dual ⋙ forget₂ FinBoolAlg FinDistribLattice =
    forget₂ FinBoolAlg FinDistribLattice ⋙ FinDistribLattice.to_dual := rfl
