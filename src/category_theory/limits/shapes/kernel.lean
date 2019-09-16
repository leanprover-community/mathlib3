/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.zero
import category_theory.limits.shapes.equalizers

universes v u

open category_theory

namespace category_theory.limits

variables (C : Type u) [𝒞 : category.{v+1} C] [has_zero_object.{v} C]
include 𝒞

abbreviation kernel [has_equalizers.{v} C] {X Y : C} (f : X ⟶ Y) := equalizer f 0
abbreviation cokernel [has_coequalizers.{v} C] {X Y : C} (f : X ⟶ Y) := coequalizer f 0

-- TODO more API to come

end category_theory.limits
