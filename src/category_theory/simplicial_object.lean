/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import category_theory.simplex_category

/-!
# Simplicial objects in a category.

A simplical object in a category `C` is a `C`-valued presheaf on `simplex_category`.
-/

open opposite
open category_theory

universes v u

namespace category_theory

variables (C : Type u) [category.{v} C]

/-- The category of simplicial objects valued in a category `C`.
This is the category of contravariant functors from
`NonemptyFinLinOrd` to `C`. -/
@[derive category]
def simplicial_object := simplex_categoryᵒᵖ ⥤ C

namespace simplicial_object
variable {C}

/-- Face maps for a simplicial object. -/
def δ (X : simplicial_object C) {n} (i : fin (n+2)) :
  X.obj (op (n+1 : ℕ)) ⟶ X.obj (op n) :=
X.map (simplex_category.δ i).op

/-- Degeneracy maps for a simplicial object. -/
def σ (X : simplicial_object C) {n} (i : fin (n+1)) :
  X.obj (op n) ⟶ X.obj (op (n+1 : ℕ)) :=
X.map (simplex_category.σ i).op

-- PROJECT: transfer the simplicial identities over to simplicial objects.

end simplicial_object

end category_theory
