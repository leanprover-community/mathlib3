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
-/
universes v u u₂

namespace category_theory

open category monoidal_category

/-- An object `X` is (right) closed if `(X ⊗ -)` is a left adjoint. -/
class closed {C : Type u} [category.{v} C] [monoidal_category.{v} C] (X : C) :=
(is_adj : is_left_adjoint (tensor_left X))

/-- A monoidal category `C` is (right) closed if every object is exponentiable, and it has finite products. -/
class is_closed (C : Type u) [category.{v} C] [monoidal_category.{v} C] :=
(closed : Π (X : C), closed X)

attribute [instance, priority 100] is_closed.closed

end category_theory
