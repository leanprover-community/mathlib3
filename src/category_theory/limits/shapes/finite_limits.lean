/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.products
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.pullbacks

universes v u

namespace category_theory

instance discrete_fintype {α : Type*} [fintype α] : fintype (discrete α) :=
by { dsimp [discrete], apply_instance }

instance discrete_hom_fintype {α : Type*} [decidable_eq α] (X Y : discrete α) : fintype (X ⟶ Y) :=
by { apply ulift.fintype }

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

end category_theory

open category_theory

namespace category_theory.limits

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

instance : fin_category walking_parallel_pair := { }

/-- Equalizers are finite limits, so if `C` has all finite limits, it also has all equalizers -/
def has_equalizers_of_has_finite_limits [has_finite_limits C] : has_equalizers C :=
{ has_limits_of_shape := infer_instance }

/-- Coequalizers are finite colimits, of if `C` has all finite colimits, it also has all
    coequalizers -/
def has_coequalizers_of_has_finite_colimits [has_finite_colimits C] : has_coequalizers C :=
{ has_colimits_of_shape := infer_instance }

variables {J : Type v}

instance fin_category_wide_pullback [fintype J] [decidable_eq J] : fin_category (wide_pullback_shape J) :=
{ fintype_hom := wide_pullback_shape.fintype_hom }

instance fin_category_wide_pushout [fintype J] [decidable_eq J] : fin_category (wide_pushout_shape J) :=
{ fintype_hom := wide_pushout_shape.fintype_hom }

/-- Finite wide pullbacks are finite limits, so if `C` has all finite limits, it also has finite wide pullbacks -/
def has_finite_wide_pullbacks_of_has_finite_limits [has_finite_limits C] : has_finite_wide_pullbacks C :=
{ has_limits_of_shape := λ J _ _, by exactI (has_finite_limits.has_limits_of_shape _) }

/-- Finite wide pushouts are finite colimits, so if `C` has all finite colimits, it also has finite wide pushouts -/
def has_finite_wide_pushouts_of_has_finite_limits [has_finite_colimits C] : has_finite_wide_pushouts C :=
{ has_colimits_of_shape := λ J _ _, by exactI (has_finite_colimits.has_colimits_of_shape _) }

instance fintype_walking_pair : fintype walking_pair :=
{ elems := {walking_pair.left, walking_pair.right},
  complete := λ x, by { cases x; simp } }

/-- Pullbacks are finite limits, so if `C` has all finite limits, it also has all pullbacks -/
def has_pullbacks_of_has_finite_limits [has_finite_wide_pullbacks C] : has_pullbacks C :=
{ has_limits_of_shape := has_finite_wide_pullbacks.has_limits_of_shape walking_pair }

/-- Pushouts are finite colimits, so if `C` has all finite colimits, it also has all pushouts -/
def has_pushouts_of_has_finite_colimits [has_finite_wide_pushouts C] : has_pushouts C :=
{ has_colimits_of_shape := has_finite_wide_pushouts.has_colimits_of_shape walking_pair }

end category_theory.limits
