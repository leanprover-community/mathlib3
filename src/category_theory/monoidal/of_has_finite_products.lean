/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Simon Hudon
-/
import category_theory.monoidal.category
import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.terminal
import category_theory.limits.types

open category_theory.limits

universes v u

namespace category_theory

section
variables (C : Type u) [𝒞 : category.{v+1} C]
include 𝒞

local attribute [tidy] tactic.case_bash

def monoidal_of_has_finite_products [has_finite_products.{v} C] : monoidal_category C :=
{ tensor_unit  := terminal C,
  tensor_obj   := λ X Y, limits.prod X Y,
  tensor_hom   := λ _ _ _ _ f g, limits.prod.map f g,
  associator   := prod.associator,
  left_unitor  := prod.left_unitor,
  right_unitor := prod.right_unitor }

def monoidal_of_has_finite_coproducts [has_finite_coproducts.{v} C] : monoidal_category C :=
{ tensor_unit  := initial C,
  tensor_obj   := λ X Y, limits.coprod X Y,
  tensor_hom   := λ _ _ _ _ f g, limits.coprod.map f g,
  associator   := coprod.associator,
  left_unitor  := coprod.left_unitor,
  right_unitor := coprod.right_unitor }

end

end category_theory

-- TODO in fact, a category with finite products is braided, and symmetric,
-- and we should say that here.
