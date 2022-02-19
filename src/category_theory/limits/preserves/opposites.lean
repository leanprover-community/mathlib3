/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.limits.opposites
import category_theory.limits.preserves.finite

/-!
# Limit preservation properties of `functor.op` and related constructions

-/

universes w w' v₁ v₂ u₁ u₂

noncomputable theory

open category_theory

namespace category_theory.limits
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]
variables {J : Type w} [category.{w'} J]

def preserves_limit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [preserves_colimit K.left_op F] :
  preserves_limit K F.op :=
{ preserves := λ c hc, is_limit_cone_right_op_of_cocone _
    (is_colimit_of_preserves F (is_colimit_cocone_left_op_of_cone _ hc)) }

def preserves_limit_left_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [preserves_colimit K.left_op F] :
  preserves_limit K F.left_op :=
{ preserves := λ c hc, is_limit_cone_unop_of_cocone _
    (is_colimit_of_preserves F (is_colimit_cocone_left_op_of_cone _ hc)) }

def preserves_limit_right_op (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [preserves_colimit K.op F] :
  preserves_limit K F.right_op :=
{ preserves := λ c hc, is_limit_cone_right_op_of_cocone _
    (is_colimit_of_preserves F (is_colimit_cone_op _ hc)) }

def preserves_limit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [preserves_colimit K.op F] :
  preserves_limit K F.unop :=
{ preserves := λ c hc, is_limit_cone_unop_of_cocone _
    (is_colimit_of_preserves F (is_colimit_cone_op _ hc)) }

def preserves_colimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [preserves_limit K.left_op F] :
  preserves_colimit K F.op :=
{ preserves := λ c hc, is_colimit_cocone_right_op_of_cone _
    (is_limit_of_preserves F (is_limit_cone_left_op_of_cocone _ hc)) }

def preserves_colimit_left_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [preserves_limit K.left_op F] :
  preserves_colimit K F.left_op :=
{ preserves := λ c hc, is_colimit_cocone_unop_of_cone _
    (is_limit_of_preserves F (is_limit_cone_left_op_of_cocone _ hc)) }

def preserves_colimit_right_op (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [preserves_limit K.op F] :
  preserves_colimit K F.right_op :=
{ preserves := λ c hc, is_colimit_cocone_right_op_of_cone _
    (is_limit_of_preserves F (is_limit_cocone_op _ hc)) }

def preserves_colimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [preserves_limit K.op F] :
  preserves_colimit K F.unop :=
{ preserves := λ c hc, is_colimit_cocone_unop_of_cone _
    (is_limit_of_preserves F (is_limit_cocone_op _ hc)) }

section
variables (J)

def preserves_limits_of_shape_op (F : C ⥤ D) [preserves_colimits_of_shape Jᵒᵖ F] :
  preserves_limits_of_shape J F.op :=
{ preserves_limit := λ K, preserves_limit_op K F }

def preserves_limits_of_shape_left_op (F : C ⥤ Dᵒᵖ) [preserves_colimits_of_shape Jᵒᵖ F] :
  preserves_limits_of_shape J F.left_op :=
{ preserves_limit := λ K, preserves_limit_left_op K F }

def preserves_limits_of_shape_right_op (F : Cᵒᵖ ⥤ D) [preserves_colimits_of_shape Jᵒᵖ F] :
  preserves_limits_of_shape J F.right_op :=
{ preserves_limit := λ K, preserves_limit_right_op K F }

def preserves_limits_of_shape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [preserves_colimits_of_shape Jᵒᵖ F] :
  preserves_limits_of_shape J F.unop :=
{ preserves_limit := λ K, preserves_limit_unop K F }

def preserves_colimits_of_shape_op (F : C ⥤ D) [preserves_limits_of_shape Jᵒᵖ F] :
  preserves_colimits_of_shape J F.op :=
{ preserves_colimit := λ K, preserves_colimit_op K F }

def preserves_colimits_of_shape_left_op (F : C ⥤ Dᵒᵖ) [preserves_limits_of_shape Jᵒᵖ F] :
  preserves_colimits_of_shape J F.left_op :=
{ preserves_colimit := λ K, preserves_colimit_left_op K F }

def preserves_colimits_of_shape_right_op (F : Cᵒᵖ ⥤ D) [preserves_limits_of_shape Jᵒᵖ F] :
  preserves_colimits_of_shape J F.right_op :=
{ preserves_colimit := λ K, preserves_colimit_right_op K F }

def preserves_colimits_of_shape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [preserves_limits_of_shape Jᵒᵖ F] :
  preserves_colimits_of_shape J F.unop :=
{ preserves_colimit := λ K, preserves_colimit_unop K F }

end

def preserves_limits_op (F : C ⥤ D) [preserves_colimits F] : preserves_limits F.op :=
{ preserves_limits_of_shape := λ J _, by exactI preserves_limits_of_shape_op J F }

def preserves_limits_left_op (F : C ⥤ Dᵒᵖ) [preserves_colimits F] : preserves_limits F.left_op :=
{ preserves_limits_of_shape := λ J _, by exactI preserves_limits_of_shape_left_op J F }

def preserves_limits_right_op (F : Cᵒᵖ ⥤ D) [preserves_colimits F] : preserves_limits F.right_op :=
{ preserves_limits_of_shape := λ J _, by exactI preserves_limits_of_shape_right_op J F }

def preserves_limits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [preserves_colimits F] : preserves_limits F.unop :=
{ preserves_limits_of_shape := λ J _, by exactI preserves_limits_of_shape_unop J F }

def perserves_colimits_op (F : C ⥤ D) [preserves_limits F] : preserves_colimits F.op :=
{ preserves_colimits_of_shape := λ J _, by exactI preserves_colimits_of_shape_op J F }

def preserves_colimits_left_op (F : C ⥤ Dᵒᵖ) [preserves_limits F] : preserves_colimits F.left_op :=
{ preserves_colimits_of_shape := λ J _, by exactI preserves_colimits_of_shape_left_op J F }

def preserves_colimits_right_op (F : Cᵒᵖ ⥤ D) [preserves_limits F] :
  preserves_colimits F.right_op :=
{ preserves_colimits_of_shape := λ J _, by exactI preserves_colimits_of_shape_right_op J F }

def preserves_colimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [preserves_limits F] : preserves_colimits F.unop :=
{ preserves_colimits_of_shape := λ J _, by exactI preserves_colimits_of_shape_unop J F }

def preserves_finite_limits_op (F : C ⥤ D) [preserves_finite_colimits.{w} F] :
  preserves_finite_limits.{w} F.op :=
{ preserves_finite_limits := λ J _ _, by exactI preserves_limits_of_shape_op J F }

def preserves_finite_limits_left_op (F : C ⥤ Dᵒᵖ) [preserves_finite_colimits.{w} F] :
  preserves_finite_limits.{w} F.left_op :=
{ preserves_finite_limits := λ J _ _, by exactI preserves_limits_of_shape_left_op J F }

def preserves_finite_limits_right_op (F : Cᵒᵖ ⥤ D) [preserves_finite_colimits.{w} F] :
  preserves_finite_limits.{w} F.right_op :=
{ preserves_finite_limits := λ J _ _, by exactI preserves_limits_of_shape_right_op J F }

def preserves_finite_limits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [preserves_finite_colimits.{w} F] :
  preserves_finite_limits.{w} F.unop :=
{ preserves_finite_limits := λ J _ _, by exactI preserves_limits_of_shape_unop J F }

def preserves_finite_colimits_op (F : C ⥤ D) [preserves_finite_limits.{w} F] :
  preserves_finite_colimits.{w} F.op :=
{ preserves_finite_colimits := λ J _ _, by exactI preserves_colimits_of_shape_op J F }

def preserves_finite_colimits_left_op (F : C ⥤ Dᵒᵖ) [preserves_finite_limits.{w} F] :
  preserves_finite_colimits.{w} F.left_op :=
{ preserves_finite_colimits := λ J _ _, by exactI preserves_colimits_of_shape_left_op J F }

def preserves_finite_colimits_right_op (F : Cᵒᵖ ⥤ D) [preserves_finite_limits.{w} F] :
  preserves_finite_colimits.{w} F.right_op :=
{ preserves_finite_colimits := λ J _ _, by exactI preserves_colimits_of_shape_right_op J F }

def preserves_finite_colimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [preserves_finite_limits.{w} F] :
  preserves_finite_colimits.{w} F.unop :=
{ preserves_finite_colimits := λ J _ _, by exactI preserves_colimits_of_shape_unop J F }

end category_theory.limits
