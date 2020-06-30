/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.products

universes v u

open category_theory
namespace category_theory.limits

/-- A category with a `fintype` of objects, and a `fintype` for each morphism space. -/
class fin_category (J : Type v) [small_category J] :=
(decidable_eq_obj : decidable_eq J . tactic.apply_instance)
(fintype_obj : fintype J . tactic.apply_instance)
(decidable_eq_hom : Π (j j' : J), decidable_eq (j ⟶ j') . tactic.apply_instance)
(fintype_hom : Π (j j' : J), fintype (j ⟶ j') . tactic.apply_instance)

attribute [instance] fin_category.decidable_eq_obj fin_category.fintype_obj
                     fin_category.decidable_eq_hom fin_category.fintype_hom

-- We need a `decidable_eq` instance here to construct `fintype` on the morphism spaces.
instance fin_category_discrete_of_decidable_fintype (J : Type v) [fintype J] [decidable_eq J] :
  fin_category (discrete J) :=
{ }

variables (C : Type u) [category.{v} C]

class has_finite_limits :=
(has_limits_of_shape : Π (J : Type v) [small_category J] [fin_category J], has_limits_of_shape J C)
class has_finite_colimits :=
(has_colimits_of_shape : Π (J : Type v) [small_category J] [fin_category J], has_colimits_of_shape J C)

attribute [instance, priority 100] -- see Note [lower instance priority]
  has_finite_limits.has_limits_of_shape
  has_finite_colimits.has_colimits_of_shape

@[priority 100] -- see Note [lower instance priority]
instance [has_limits C] : has_finite_limits C :=
{ has_limits_of_shape := λ J _ _, by { resetI, apply_instance } }
@[priority 100] -- see Note [lower instance priority]
instance [has_colimits C] : has_finite_colimits C :=
{ has_colimits_of_shape := λ J _ _, by { resetI, apply_instance } }

end category_theory.limits
