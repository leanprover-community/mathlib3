/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.category.Group.Z_Module_equivalence
import algebra.category.Group.limits
import algebra.category.Group.colimits
import algebra.category.Module.abelian
import category_theory.abelian.basic

/-!
# The category of abelian groups is abelian

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open category_theory
open category_theory.limits

universe u

noncomputable theory

namespace AddCommGroup

section
variables {X Y : AddCommGroup.{u}} (f : X ⟶ Y)

/-- In the category of abelian groups, every monomorphism is normal. -/
def normal_mono (hf : mono f) : normal_mono f :=
equivalence_reflects_normal_mono (forget₂ (Module.{u} ℤ) AddCommGroup.{u}).inv $
  Module.normal_mono _ infer_instance

/-- In the category of abelian groups, every epimorphism is normal. -/
def normal_epi (hf : epi f) : normal_epi f :=
equivalence_reflects_normal_epi (forget₂ (Module.{u} ℤ) AddCommGroup.{u}).inv $
  Module.normal_epi _ infer_instance

end

/-- The category of abelian groups is abelian. -/
instance : abelian AddCommGroup.{u} :=
{ has_finite_products := ⟨by apply_instance⟩,
  normal_mono_of_mono := λ X Y, normal_mono,
  normal_epi_of_epi := λ X Y, normal_epi,
  add_comp' := by { intros, simp only [preadditive.add_comp] },
  comp_add' := by { intros, simp only [preadditive.comp_add] } }

end AddCommGroup
