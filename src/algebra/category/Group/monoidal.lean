/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group.colimits
import category_theory.monoidal.of_has_finite_products

universe v

namespace category_theory

-- TODO construct a terminal object and binary coproducts directly, rather than using the ones
-- from general colimits, so they are more usable!

instance : monoidal_category AddCommGroup.{v} :=
monoidal_of_has_finite_coproducts AddCommGroup

end category_theory
