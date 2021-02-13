/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import category_theory.simplicial_object
import algebra.category.Module.basic
import algebra.homology.chain_complex

universes v u

noncomputable theory

open category_theory category_theory.limits
open opposite

section
variables (C : Type*) [category C] [has_zero_object C] [has_zero_morphisms C]
local attribute [instance] has_zero_object.has_zero

@[derive category]
def connective_chain_complex := { X : chain_complex C // ∀ i : ℤ, i < 0 → X.X i = 0 }
end

variables {R : Type*} [ring R] -- We could probably do this for an arbitrary abelian category?

local notation `sModule `R := simplicial_object (Module R)

/-! The definitions in this namespace are all auxilliary definitions for `normalized_Moore_complex`
and should usually only be accessed via that. -/
namespace normalized_Moore_complex

def obj_X_apply_submodule (X : sModule R) : Π i : ℕ, submodule R (X.obj (op i))
| 0 := ⊤
| (i+1) :=
{ carrier :=
  { x : X.obj (op (i+1 : ℕ)) | ∀ j : fin (i+2), 0 < j → X.δ j x = 0 },
  zero_mem' := by simp,
  add_mem' := λ x y hx hy j wj, by simp [(X.δ j).map_add, hx j wj, hy j wj],
  smul_mem' := λ r x hx j wj, by simp [(X.δ j).map_smul, hx j wj], }

def obj_X_apply (X : sModule R) (i : ℕ) : Module R := Module.of R (obj_X_apply_submodule X i)

def obj_X_apply_ℤ (X : sModule R) : ℤ → Module R
| (int.of_nat i) := obj_X_apply X i
| _ := 0

def obj_X_apply_ℤ_eq_to_iso (X : sModule R) (n m : ℤ) (h : n = m) :
  obj_X_apply_ℤ X n ≅ obj_X_apply_ℤ X m :=
begin
  induction h,
  apply iso.refl,
end

def obj_d_ℤ (X : sModule R) (i : ℤ) : obj_X_apply_ℤ X i ⟶ obj_X_apply_ℤ X (i-1) :=
begin
  cases i,
  { cases i,
    { exact 0, },
    { refine _ ≫ (obj_X_apply_ℤ_eq_to_iso X i _ _).hom,
      change obj_X_apply X (i+1) ⟶ obj_X_apply X i,
      sorry, }, },
  { exact 0, },
end

def obj (X : sModule R) : connective_chain_complex (Module R) :=
{ val :=
  { X := obj_X_apply_ℤ X,
    d := obj_d_ℤ X, },
  property := sorry, }

end normalized_Moore_complex

variables (R)

def normalized_Moore_complex : (sModule R) ⥤ connective_chain_complex (Module R) :=
{ obj := λ X, sorry,
  map := sorry, }
