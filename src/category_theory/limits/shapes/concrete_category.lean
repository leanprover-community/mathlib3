/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.kernels
import category_theory.concrete_category.basic

/-!
# Facts about limits of functors into concrete categories

This file doesn't yet attempt to be exhaustive;
it just contains lemmas that are useful
while comparing categorical limits with existing constructions in concrete categories.
-/

universes u

open category_theory

namespace category_theory.limits

variables {C : Type (u+1)} [large_category C] [concrete_category C]

local attribute [instance] concrete_category.has_coe_to_sort
local attribute [instance] concrete_category.has_coe_to_fun

section kernels

variables [has_zero_morphisms C]

variables {X Y : C} (f : X ⟶ Y)

@[simp]
lemma kernel_condition_apply [has_kernel f] (x : kernel f) :
  f (kernel.ι f x) = (0 : kernel f ⟶ Y) x :=
begin
  have h := congr_arg (λ k : kernel f ⟶ Y, (k : kernel f → Y) x) (kernel.condition f),
  dsimp at h,
  rw coe_comp at h,
  exact h
end

@[simp]
lemma cokernel_condition_apply [has_cokernel f] (x : X) :
  cokernel.π f (f x) = (0 : X ⟶ cokernel f) x :=
begin
  have h := congr_arg (λ k : X ⟶ cokernel f, (k : X → cokernel f) x) (cokernel.condition f),
  dsimp at h,
  rw coe_comp at h,
  exact h
end

end kernels

end category_theory.limits
