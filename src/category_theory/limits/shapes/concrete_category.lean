/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.kernels
import category_theory.concrete_category.basic
import tactic.elementwise

/-!
# Facts about limits of functors into concrete categories

This file doesn't yet attempt to be exhaustive;
it just contains lemmas that are useful
while comparing categorical limits with existing constructions in concrete categories.
-/

universes u

open category_theory


namespace category_theory.limits

attribute [elementwise] kernel.condition cokernel.condition

end category_theory.limits
