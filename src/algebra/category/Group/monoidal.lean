/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group.limits
import category_theory.monoidal.of_has_finite_products

universe v

namespace category_theory

-- TODO construct a initial object and binary products directly, rather than using the ones
-- from general limits, so they are more usable!

-- TODO really, we ought to explain that the monoidal structures from products and from coproducts
-- are the same

instance : monoidal_category AddCommGroup.{v} :=
monoidal_of_has_finite_products AddCommGroup

end category_theory
