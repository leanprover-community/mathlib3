/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.preserves.basic
import category_theory.filtered
import category_theory.limits.types

/-!
# Preservation of filtered colimits.
Typically forgetful functors from algebraic categories preserve filtered colimits
(although not general colimits).
-/

open category_theory
open category_theory.functor

namespace category_theory.limits

universes v u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]

variables {J : Type v} [small_category J] {K : J ⥤ C}

class preserves_filtered_colimits (F : C ⥤ D) : Type (max u₁ u₂ (v+1)) :=
(preserves_filtered_colimits : Π (J : Type v) [small_category J] [is_filtered J],
  preserves_colimits_of_shape J F)

attribute [instance, priority 100] preserves_filtered_colimits.preserves_filtered_colimits

end category_theory.limits
