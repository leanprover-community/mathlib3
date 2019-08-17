/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.finite_products
import category_theory.pempty

universes v u

open category_theory

namespace category_theory.limits

variables (C : Type u) [𝒞 : category.{v+1} C]
include 𝒞

abbreviation initial [has_limit (functor.empty C)] : C := limit (functor.empty C)
abbreviation terminal [has_colimit (functor.empty C)] : C := colimit (functor.empty C)

class has_initial :=
(has_limits_of_shape : has_limits_of_shape.{v} pempty C)
class has_terminal :=
(has_colimits_of_shape : has_colimits_of_shape.{v} pempty C)

attribute [instance] has_initial.has_limits_of_shape has_terminal.has_colimits_of_shape

instance [has_finite_products.{v} C] : has_initial.{v} C :=
{ has_limits_of_shape :=
  { has_limit := λ F, has_limit_of_equivalence_comp ((functor.empty (discrete pempty)).as_equivalence.symm) } }
instance [has_finite_coproducts.{v} C] : has_terminal.{v} C :=
{ has_colimits_of_shape :=
  { has_colimit := λ F, has_colimit_of_equivalence_comp ((functor.empty (discrete pempty)).as_equivalence.symm) } }


end category_theory.limits
