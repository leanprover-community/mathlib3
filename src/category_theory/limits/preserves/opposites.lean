/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.limits.opposites
import category_theory.limits.preserves.finite

/-!
# Limit preservation properties of `functor.op` and related constructions

We formulate conditions about `F` which imply that `F.op`, `F.unop`, `F.left_op` and `F.right_op`
preserve certain (co)limits.

## Future work

* Dually, it is possible to formulate conditions about `F.op` ec. for `F` to preserve certain
(co)limits.

-/

universes w w' v₁ v₂ u₁ u₂

noncomputable theory

open category_theory

namespace category_theory.limits

section
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]
variables {J : Type w} [category.{w'} J]

/-- If `F : C ⥤ D` preserves colimits of `K.left_op : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves
    limits of `K : J ⥤ Cᵒᵖ`. -/
def preserves_limit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [preserves_colimit K.left_op F] :
  preserves_limit K F.op :=
{ preserves := λ c hc, is_limit_cone_right_op_of_cocone _
    (is_colimit_of_preserves F (is_colimit_cocone_left_op_of_cone _ hc)) }

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits of `K.left_op : Jᵒᵖ ⥤ C`, then `F.left_op : Cᵒᵖ ⥤ D`
    preserves limits of `K : J ⥤ Cᵒᵖ`. -/
def preserves_limit_left_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [preserves_colimit K.left_op F] :
  preserves_limit K F.left_op :=
{ preserves := λ c hc, is_limit_cone_unop_of_cocone _
    (is_colimit_of_preserves F (is_colimit_cocone_left_op_of_cone _ hc)) }

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.right_op : C ⥤ Dᵒᵖ` preserves
    limits of `K : J ⥤ C`. -/
def preserves_limit_right_op (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [preserves_colimit K.op F] :
  preserves_limit K F.right_op :=
{ preserves := λ c hc, is_limit_cone_right_op_of_cocone _
    (is_colimit_of_preserves F (is_colimit_cone_op _ hc)) }

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` preserves
    limits of `K : J ⥤ C`. -/
def preserves_limit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [preserves_colimit K.op F] :
  preserves_limit K F.unop :=
{ preserves := λ c hc, is_limit_cone_unop_of_cocone _
    (is_colimit_of_preserves F (is_colimit_cone_op _ hc)) }

/-- If `F : C ⥤ D` preserves limits of `K.left_op : Jᵒᵖ ⥤ C`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves
    colimits of `K : J ⥤ Cᵒᵖ`. -/
def preserves_colimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [preserves_limit K.left_op F] :
  preserves_colimit K F.op :=
{ preserves := λ c hc, is_colimit_cocone_right_op_of_cone _
    (is_limit_of_preserves F (is_limit_cone_left_op_of_cocone _ hc)) }

/-- If `F : C ⥤ Dᵒᵖ` preserves limits of `K.left_op : Jᵒᵖ ⥤ C`, then `F.left_op : Cᵒᵖ ⥤ D` preserves
    colimits of `K : J ⥤ Cᵒᵖ`. -/
def preserves_colimit_left_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [preserves_limit K.left_op F] :
  preserves_colimit K F.left_op :=
{ preserves := λ c hc, is_colimit_cocone_unop_of_cone _
    (is_limit_of_preserves F (is_limit_cone_left_op_of_cocone _ hc)) }

/-- If `F : Cᵒᵖ ⥤ D` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.right_op : C ⥤ Dᵒᵖ` preserves
    colimits of `K : J ⥤ C`. -/
def preserves_colimit_right_op (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [preserves_limit K.op F] :
  preserves_colimit K F.right_op :=
{ preserves := λ c hc, is_colimit_cocone_right_op_of_cone _
    (is_limit_of_preserves F (is_limit_cocone_op _ hc)) }

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of `K.op : Jᵒᵖ ⥤ Cᵒᵖ`, then `F.unop : C ⥤ D` preserves
    colimits of `K : J ⥤ C`. -/
def preserves_colimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [preserves_limit K.op F] :
  preserves_colimit K F.unop :=
{ preserves := λ c hc, is_colimit_cocone_unop_of_cone _
    (is_limit_of_preserves F (is_limit_cocone_op _ hc)) }

section
variables (J)

/-- If `F : C ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of
    shape `J`. -/
def preserves_limits_of_shape_op (F : C ⥤ D) [preserves_colimits_of_shape Jᵒᵖ F] :
  preserves_limits_of_shape J F.op :=
{ preserves_limit := λ K, preserves_limit_op K F }

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F.left_op : Cᵒᵖ ⥤ D` preserves limits
    of shape `J`. -/
def preserves_limits_of_shape_left_op (F : C ⥤ Dᵒᵖ) [preserves_colimits_of_shape Jᵒᵖ F] :
  preserves_limits_of_shape J F.left_op :=
{ preserves_limit := λ K, preserves_limit_left_op K F }

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits of shape `Jᵒᵖ`, then `F.right_op : C ⥤ Dᵒᵖ` preserves limits
    of shape `J`. -/
def preserves_limits_of_shape_right_op (F : Cᵒᵖ ⥤ D) [preserves_colimits_of_shape Jᵒᵖ F] :
  preserves_limits_of_shape J F.right_op :=
{ preserves_limit := λ K, preserves_limit_right_op K F }

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` preserves limits of
    shape `J`. -/
def preserves_limits_of_shape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [preserves_colimits_of_shape Jᵒᵖ F] :
  preserves_limits_of_shape J F.unop :=
{ preserves_limit := λ K, preserves_limit_unop K F }

/-- If `F : C ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits of
    shape `J`. -/
def preserves_colimits_of_shape_op (F : C ⥤ D) [preserves_limits_of_shape Jᵒᵖ F] :
  preserves_colimits_of_shape J F.op :=
{ preserves_colimit := λ K, preserves_colimit_op K F }

/-- If `F : C ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F.left_op : Cᵒᵖ ⥤ D` preserves colimits
    of shape `J`. -/
def preserves_colimits_of_shape_left_op (F : C ⥤ Dᵒᵖ) [preserves_limits_of_shape Jᵒᵖ F] :
  preserves_colimits_of_shape J F.left_op :=
{ preserves_colimit := λ K, preserves_colimit_left_op K F }

/-- If `F : Cᵒᵖ ⥤ D` preserves limits of shape `Jᵒᵖ`, then `F.right_op : C ⥤ Dᵒᵖ` preserves colimits
    of shape `J`. -/
def preserves_colimits_of_shape_right_op (F : Cᵒᵖ ⥤ D) [preserves_limits_of_shape Jᵒᵖ F] :
  preserves_colimits_of_shape J F.right_op :=
{ preserves_colimit := λ K, preserves_colimit_right_op K F }

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits of shape `Jᵒᵖ`, then `F.unop : C ⥤ D` preserves colimits
    of shape `J`. -/
def preserves_colimits_of_shape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [preserves_limits_of_shape Jᵒᵖ F] :
  preserves_colimits_of_shape J F.unop :=
{ preserves_colimit := λ K, preserves_colimit_unop K F }

end

/-- If `F : C ⥤ D` preserves colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits. -/
def preserves_limits_op (F : C ⥤ D) [preserves_colimits F] : preserves_limits F.op :=
{ preserves_limits_of_shape := λ J _, by exactI preserves_limits_of_shape_op J F }

/-- If `F : C ⥤ Dᵒᵖ` preserves colimits, then `F.left_op : Cᵒᵖ ⥤ D` preserves limits. -/
def preserves_limits_left_op (F : C ⥤ Dᵒᵖ) [preserves_colimits F] : preserves_limits F.left_op :=
{ preserves_limits_of_shape := λ J _, by exactI preserves_limits_of_shape_left_op J F }

/-- If `F : Cᵒᵖ ⥤ D` preserves colimits, then `F.right_op : C ⥤ Dᵒᵖ` preserves limits. -/
def preserves_limits_right_op (F : Cᵒᵖ ⥤ D) [preserves_colimits F] : preserves_limits F.right_op :=
{ preserves_limits_of_shape := λ J _, by exactI preserves_limits_of_shape_right_op J F }

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits, then `F.unop : C ⥤ D` preserves limits. -/
def preserves_limits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [preserves_colimits F] : preserves_limits F.unop :=
{ preserves_limits_of_shape := λ J _, by exactI preserves_limits_of_shape_unop J F }

/-- If `F : C ⥤ D` preserves limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves colimits. -/
def perserves_colimits_op (F : C ⥤ D) [preserves_limits F] : preserves_colimits F.op :=
{ preserves_colimits_of_shape := λ J _, by exactI preserves_colimits_of_shape_op J F }

/-- If `F : C ⥤ Dᵒᵖ` preserves limits, then `F.left_op : Cᵒᵖ ⥤ D` preserves colimits. -/
def preserves_colimits_left_op (F : C ⥤ Dᵒᵖ) [preserves_limits F] : preserves_colimits F.left_op :=
{ preserves_colimits_of_shape := λ J _, by exactI preserves_colimits_of_shape_left_op J F }

/-- If `F : Cᵒᵖ ⥤ D` preserves limits, then `F.right_op : C ⥤ Dᵒᵖ` preserves colimits. -/
def preserves_colimits_right_op (F : Cᵒᵖ ⥤ D) [preserves_limits F] :
  preserves_colimits F.right_op :=
{ preserves_colimits_of_shape := λ J _, by exactI preserves_colimits_of_shape_right_op J F }

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves limits, then `F.unop : C ⥤ D` preserves colimits. -/
def preserves_colimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [preserves_limits F] : preserves_colimits F.unop :=
{ preserves_colimits_of_shape := λ J _, by exactI preserves_colimits_of_shape_unop J F }

end

section
-- Preservation of finite (colimits) is only defined when the morphisms of C and D live in the same
-- universe.
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₁} D]

/-- If `F : C ⥤ D` preserves finite colimits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
    limits. -/
def preserves_finite_limits_op (F : C ⥤ D) [preserves_finite_colimits F] :
  preserves_finite_limits F.op :=
{ preserves_finite_limits := λ J _ _, by exactI preserves_limits_of_shape_op J F }

/-- If `F : C ⥤ Dᵒᵖ` preserves finite colimits, then `F.left_op : Cᵒᵖ ⥤ D` preserves finite
    limits. -/
def preserves_finite_limits_left_op (F : C ⥤ Dᵒᵖ) [preserves_finite_colimits F] :
  preserves_finite_limits F.left_op :=
{ preserves_finite_limits := λ J _ _, by exactI preserves_limits_of_shape_left_op J F }

/-- If `F : Cᵒᵖ ⥤ D` preserves finite colimits, then `F.right_op : C ⥤ Dᵒᵖ` preserves finite
    limits. -/
def preserves_finite_limits_right_op (F : Cᵒᵖ ⥤ D) [preserves_finite_colimits F] :
  preserves_finite_limits F.right_op :=
{ preserves_finite_limits := λ J _ _, by exactI preserves_limits_of_shape_right_op J F }

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite colimits, then `F.unop : C ⥤ D` preserves finite
    limits. -/
def preserves_finite_limits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [preserves_finite_colimits F] :
  preserves_finite_limits F.unop :=
{ preserves_finite_limits := λ J _ _, by exactI preserves_limits_of_shape_unop J F }

/-- If `F : C ⥤ D` preserves finite limits, then `F.op : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite
    colimits. -/
def preserves_finite_colimits_op (F : C ⥤ D) [preserves_finite_limits F] :
  preserves_finite_colimits F.op :=
{ preserves_finite_colimits := λ J _ _, by exactI preserves_colimits_of_shape_op J F }

/-- If `F : C ⥤ Dᵒᵖ` preserves finite limits, then `F.left_op : Cᵒᵖ ⥤ D` preserves finite
    colimits. -/
def preserves_finite_colimits_left_op (F : C ⥤ Dᵒᵖ) [preserves_finite_limits F] :
  preserves_finite_colimits F.left_op :=
{ preserves_finite_colimits := λ J _ _, by exactI preserves_colimits_of_shape_left_op J F }

/-- If `F : Cᵒᵖ ⥤ D` preserves finite limits, then `F.right_op : C ⥤ Dᵒᵖ` preserves finite
    colimits. -/
def preserves_finite_colimits_right_op (F : Cᵒᵖ ⥤ D) [preserves_finite_limits F] :
  preserves_finite_colimits F.right_op :=
{ preserves_finite_colimits := λ J _ _, by exactI preserves_colimits_of_shape_right_op J F }

/-- If `F : Cᵒᵖ ⥤ Dᵒᵖ` preserves finite limits, then `F.unop : C ⥤ D` preserves finite
    colimits. -/
def preserves_finite_colimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [preserves_finite_limits F] :
  preserves_finite_colimits F.unop :=
{ preserves_finite_colimits := λ J _ _, by exactI preserves_colimits_of_shape_unop J F }

end

end category_theory.limits
