/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.simplicial_object
import category_theory.abelian.basic
import algebra.homology.connective_chain_complex

universes v u

noncomputable theory

open category_theory category_theory.limits
open opposite

variables (C : Type*) [category C] [abelian C]

/-! The definitions in this namespace are all auxilliary definitions for `normalized_Moore_complex`
and should usually only be accessed via that. -/
namespace normalized_Moore_complex

def obj (X : simplicial_object C) : connective_chain_complex C :=
{ X := obj_X_apply_ℤ X,
  d := sorry, }

end normalized_Moore_complex

variables (R)

def normalized_Moore_complex : (simplicial_object C) ⥤ connective_chain_complex C :=
{ obj := λ X, sorry,
  map := sorry, }
