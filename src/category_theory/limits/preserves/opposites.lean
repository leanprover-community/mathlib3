/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.limits.opposites
import category_theory.limits.preserves.basic

/-!
# Limit preservation properties of `functor.op` and related constructions

-/

universes w w' v₁ v₂ u₁ u₂

noncomputable theory

open category_theory

namespace category_theory.limits
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]
variables {J : Type w} [category.{w'} J]

def preserves_colimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [preserves_limit K.left_op F] :
  preserves_colimit K F.op :=
sorry

def preserves_colimit_left_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [preserves_limit K.left_op F] :
  preserves_colimit K F.left_op :=
sorry

def preserves_colimit_right_op (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [preserves_limit K.op F] :
  preserves_colimit K F.right_op :=
sorry

def preserves_colimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [preserves_limit K.op F] :
  preserves_colimit K F.unop :=
sorry


end category_theory.limits
