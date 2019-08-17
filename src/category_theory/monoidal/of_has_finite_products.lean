/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.category
import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.initial

open category_theory.limits

universes v u

namespace category_theory

variables (C : Type u) [𝒞 : category.{v+1} C]
include 𝒞

instance [has_finite_products.{v} C] : monoidal_category C :=
{ tensor_unit := initial C,
  tensor_obj := λ X Y, prod X Y }

end category_theory
