/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison
-/
import category_theory.monoidal.of_has_finite_products
import category_theory.limits.shapes.finite_products
import category_theory.limits.types

open category_theory
open category_theory.limits
open tactic

universes u

namespace category_theory.monoidal

local attribute [instance] monoidal_of_has_finite_products symmetric_monoidal_of_has_finite_products

instance types_monoidal : monoidal_category.{u} (Type u) := by apply_instance
instance types_symmetric : symmetric_monoidal_category.{u} (Type u) := by apply_instance

end category_theory.monoidal
