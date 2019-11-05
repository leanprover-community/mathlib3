/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison
-/
import category_theory.types
import category_theory.limits.types
import category_theory.monoidal.of_has_finite_products

open category_theory
open tactic

universes u v

namespace category_theory.monoidal

local attribute [instance] monoidal_of_has_finite_products
instance types : monoidal_category.{u} (Type u) := by apply_instance

-- TODO Once we add braided/symmetric categories, include the braiding/symmetry.

end category_theory.monoidal
