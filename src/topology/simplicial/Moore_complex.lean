/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.simplicial_object
import category_theory.abelian.basic
import category_theory.subobject
import algebra.homology.connective_chain_complex

universes v u

noncomputable theory

open category_theory category_theory.limits
open opposite

def fin.rest (n : ℕ) : finset (fin (n+1)) := finset.univ.image (fin.succ : fin n → fin (n+1))

variables {C : Type*} [category C] [abelian C]
local attribute [instance] abelian.has_pullbacks

/-! The definitions in this namespace are all auxilliary definitions for `normalized_Moore_complex`
and should usually only be accessed via that. -/
namespace normalized_Moore_complex
variables (X : simplicial_object C)

def obj_X : Π n : ℕ, subobject (X.obj (op n))
| 0 := ⊤
| (n+1) := finset.univ.inf (λ k : fin (n+1), kernel_subobject (X.δ k.succ))

def obj_d : Π n : ℕ, obj_X X (n+1) ⟶ obj_X X n
| 0 := sorry
| (n+1) := sorry

def obj : connective_chain_complex C :=
{ X := obj_X X,
  d := obj_d X,
  d_squared' := sorry, }

end normalized_Moore_complex

variables (C)

def normalized_Moore_complex : (simplicial_object C) ⥤ connective_chain_complex C :=
{ obj := λ X, sorry,
  map := sorry, }
