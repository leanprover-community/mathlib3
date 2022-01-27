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

universes u v

open category_theory

/-- The category of boolean algebras. -/
def BoolAlg := bundled boolean_algebra

@[simp] lemma bool.band_bnot_self : ∀ x, x && !x = ff := dec_trivial
@[simp] lemma bool.bnot_band_self : ∀ x, !x && x = ff := dec_trivial
@[simp] lemma bool.bor_bnot_self : ∀ x, x || !x = tt := dec_trivial
@[simp] lemma bool.bnot_bor_self : ∀ x, !x || x = tt := dec_trivial

instance : boolean_algebra bool := boolean_algebra.of_core
{ sup := bor,
  le_sup_left := bool.left_le_bor,
  le_sup_right := bool.right_le_bor,
  sup_le := λ _ _ _, bool.bor_le,
  inf := band,
  inf_le_left := bool.band_le_left,
  inf_le_right := bool.band_le_right,
  le_inf := λ _ _ _, bool.le_band,
  le_sup_inf := dec_trivial,
  compl := bnot,
  inf_compl_le_bot := λ a, a.band_bnot_self.le,
  top_le_sup_compl := λ a, a.bor_bnot_self.ge,
  ..bool.linear_order,
  ..bool.bounded_order }

instance : complete_boolean_algebra bool := sorry

namespace BoolAlg

instance : has_coe_to_sort BoolAlg Type* := bundled.has_coe_to_sort
instance (X : BoolAlg) : boolean_algebra X := X.str

/-- Construct a bundled `BoolAlg` from a `boolean_algebra`. -/
def of (α : Type*) [boolean_algebra α] : BoolAlg := bundled.of α

instance : inhabited BoolAlg := ⟨of bool⟩

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
