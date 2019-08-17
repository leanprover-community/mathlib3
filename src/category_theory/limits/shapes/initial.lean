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
{ has_limits_of_shape := sorry } -- needs to use the equivalence between `pempty` and `discrete pempty`!
instance [has_finite_coproducts.{v} C] : has_terminal.{v} C :=
{ has_colimits_of_shape := sorry }


end category_theory.limits
