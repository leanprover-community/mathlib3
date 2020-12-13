/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.category
import category_theory.adjunction.basic

/-!
# Closed monoidal categories

Define (right) closed objects and (right) closed monoidal categories.

## TODO
Some of the theorems proved about cartesian closed categories
should be generalised and moved to this file.
-/
universes v u u₂

namespace category_theory

open category monoidal_category

/-- An object `X` is (right) closed if `(X ⊗ -)` is a left adjoint. -/
class closed {C : Type u} [category.{v} C] [monoidal_category.{v} C] (X : C) :=
(is_adj : is_left_adjoint (tensor_left X))

/-- A monoidal category `C` is (right) monoidal closed if every object is (right) closed. -/
class monoidal_closed (C : Type u) [category.{v} C] [monoidal_category.{v} C] :=
(closed : Π (X : C), closed X)

attribute [instance, priority 100] monoidal_closed.closed

/--
The unit object is always closed.
This isn't an instance because most of the time we'll prove closedness for all objects at once,
rather than just for this one.
-/
def unit_closed {C : Type u} [category.{v} C] [monoidal_category.{v} C] : closed (𝟙_ C) :=
{ is_adj :=
  { right := 𝟭 C,
    adj := adjunction.mk_of_hom_equiv
    { hom_equiv := λ X _,
      { to_fun := λ a, (left_unitor X).inv ≫ a,
        inv_fun := λ a, (left_unitor X).hom ≫ a,
        left_inv := by tidy,
        right_inv := by tidy },
      hom_equiv_naturality_left_symm' := λ X' X Y f g,
      by { dsimp, rw left_unitor_naturality_assoc } } } }

end category_theory
