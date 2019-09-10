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

/-- A category with a `fintype` of objects, and a `fintype` for each morphism space. -/
class fin_category (J : Type v) extends category.{v+1} J, fintype J :=
(decidable_eq_obj : decidable_eq J . tactic.apply_instance)
(decidable_eq_hom : Π (j j' : J), decidable_eq (j ⟶ j') . tactic.apply_instance)
(fintype_hom : Π (j j' : J), fintype (j ⟶ j') . tactic.apply_instance)

attribute [instance] fin_category.decidable_eq_obj fin_category.decidable_eq_hom fin_category.fintype_hom

-- We need a `decidable_eq` instance here to construct `fintype` on the morphism spaces.
instance fin_category_discrete_of_decidable_fintype (J : Type v) [decidable_eq J] [fintype J] :
  fin_category (discrete J) :=
{ }

variables (C : Type u) [𝒞 : category.{v+1} C]
include 𝒞

class has_finite_limits :=
(has_limits_of_shape : Π (J : Type v) [𝒥 : fin_category J], has_limits_of_shape.{v} J C)
class has_finite_colimits :=
(has_colimits_of_shape : Π (J : Type v) [𝒥 : fin_category J], has_colimits_of_shape.{v} J C)

attribute [instance] has_finite_limits.has_limits_of_shape has_finite_colimits.has_colimits_of_shape

instance [has_limits.{v} C] : has_finite_limits.{v} C :=
{ has_limits_of_shape := λ J _, by { resetI, apply_instance } }
instance [has_colimits.{v} C] : has_finite_colimits.{v} C :=
{ has_colimits_of_shape := λ J _, by { resetI, apply_instance } }

end category_theory.limits
