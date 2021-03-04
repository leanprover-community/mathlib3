/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
import category_theory.limits.constructions.pullbacks
import category_theory.limits.shapes.biproducts
import category_theory.limits.shapes.images
import category_theory.abelian.non_preadditive
import category_theory.shift

/-!
# Additive Categories

This file contains the definition of additive categories.

-/

noncomputable theory

open category_theory
open category_theory.preadditive
open category_theory.limits

universes v v₀ v₁ v₂ u u₀ u₁ u₂

namespace category_theory

variables (C : Type u) [category C]


/--
A preadditive category `C` is called additive if it has all finite biproducts.
See https://stacks.math.columbia.edu/tag/0104.
-/
class additive_category extends preadditive C, has_finite_biproducts C

end category_theory
