/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison
-/
import category_theory.monoidal.of_chosen_finite_products.symmetric
import category_theory.monoidal.types.basic

/-!
# The category of types is a symmetric monoidal category
-/

open category_theory
open category_theory.limits

universes v u

namespace category_theory

instance types_symmetric : symmetric_category.{u} (Type u) :=
symmetric_of_chosen_finite_products (types.terminal_limit_cone) (types.binary_product_limit_cone)

@[simp] lemma braiding_hom_apply {X Y : Type u} {x : X} {y : Y} :
  ((β_ X Y).hom : X ⊗ Y → Y ⊗ X) (x, y) = (y, x) := rfl
@[simp] lemma braiding_inv_apply {X Y : Type u} {x : X} {y : Y} :
  ((β_ X Y).inv : Y ⊗ X → X ⊗ Y) (y, x) = (x, y) := rfl

end category_theory
