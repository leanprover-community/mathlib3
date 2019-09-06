/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.products
import category_theory.discrete_category
import data.fintype

universes v u

open category_theory
namespace category_theory.limits

variables (C : Type u) [𝒞 : category.{v+1} C]
include 𝒞

class has_finite_limits :=
(has_limits_of_shape : Π (J : Type v) [𝒥 : small_category J] [fintype J], has_limits_of_shape.{v} J C)
class has_finite_colimits :=
(has_colimits_of_shape : Π (J : Type v) [𝒥 : small_category J] [fintype J], has_colimits_of_shape.{v} J C)

attribute [instance] has_finite_limits.has_limits_of_shape has_finite_colimits.has_colimits_of_shape

instance [has_limits.{v} C] : has_finite_limits.{v} C :=
{ has_limits_of_shape := λ J _, by { resetI, apply_instance } }
instance [has_colimits.{v} C] : has_finite_colimits.{v} C :=
{ has_colimits_of_shape := λ J _, by { resetI, apply_instance } }

end category_theory.limits
