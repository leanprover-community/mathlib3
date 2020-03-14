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

/-!
# The natural monoidal structure on any category with finite (co)products.

A category with a monoidal structure provided in this way is sometimes called a (co)cartesian category,
although this is also sometimes used to mean a finitely complete category.
(See <https://ncatlab.org/nlab/show/cartesian+category>.)

As this works with either products or coproducts, we don't set up either construct as an instance.
-/

universes v u

namespace category_theory
open category_theory.limits

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

section
local attribute [tidy] tactic.case_bash

/-- A category with a terminal object and binary products has a natural monoidal structure. -/
def monoidal_of_has_finite_products [has_terminal.{v} C] [has_binary_products.{v} C] : monoidal_category C :=
{ tensor_unit  := ⊤_ C,
  tensor_obj   := λ X Y, X ⨯ Y,
  tensor_hom   := λ _ _ _ _ f g, limits.prod.map f g,
  associator   := prod.associator,
  left_unitor  := prod.left_unitor,
  right_unitor := prod.right_unitor,
  pentagon'    := prod.pentagon,
  triangle'    := prod.triangle,
  associator_naturality' := @prod.associator_naturality _ _ _, }
end

namespace monoidal_of_has_finite_products
variables [has_terminal.{v} C] [has_binary_products.{v} C]
local attribute [instance] monoidal_of_has_finite_products

@[simp]
lemma left_unitor_hom (X : C) : (λ_ X).hom = limits.prod.snd := rfl
@[simp]
lemma right_unitor_hom (X : C) : (ρ_ X).hom = limits.prod.fst := rfl
@[simp]
lemma associator_hom (X Y Z : C) :
  (α_ X Y Z).hom =
  prod.lift
    (limits.prod.fst ≫ limits.prod.fst)
    (prod.lift (limits.prod.fst ≫ limits.prod.snd) limits.prod.snd) := rfl

end monoidal_of_has_finite_products

section
local attribute [tidy] tactic.case_bash

/-- A category with an initial object and binary coproducts has a natural monoidal structure. -/
def monoidal_of_has_finite_coproducts [has_initial.{v} C] [has_binary_coproducts.{v} C] : monoidal_category C :=
{ tensor_unit  := ⊥_ C,
  tensor_obj   := λ X Y, X ⨿ Y,
  tensor_hom   := λ _ _ _ _ f g, limits.coprod.map f g,
  associator   := coprod.associator,
  left_unitor  := coprod.left_unitor,
  right_unitor := coprod.right_unitor,
  pentagon'    := coprod.pentagon,
  triangle'    := coprod.triangle,
  associator_naturality' := @coprod.associator_naturality _ _ _, }
end

end category_theory

-- TODO in fact, a category with finite products is braided, and symmetric,
-- and we should say that here.
