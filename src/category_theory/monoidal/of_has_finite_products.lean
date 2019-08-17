/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.category
import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.terminal

open category_theory.limits

universes v u

namespace category_theory

variables (C : Type u) [𝒞 : category.{v+1} C]
include 𝒞

section
local attribute [tidy] tactic.case_bash

instance [has_finite_products.{v} C] : monoidal_category C :=
{ tensor_unit  := terminal C,
  tensor_obj   := λ X Y, prod X Y,
  tensor_hom   := λ W X Y Z f g, limits.prod.map f g,
  associator   := prod.associator,
  left_unitor  := prod.left_unitor,
  right_unitor := prod.right_unitor }
end

end category_theory

-- -- TODO extract the rewrite proofs obviously produces below.

-- def monoidal_of_has_products : monoidal_category.{v} C :=
-- { tensor_obj := λ X Y, limits.prod X Y,
--   tensor_hom := λ _ _ _ _ f g, limits.prod.map f g,
--   tensor_unit := terminal C,
--   associator := binary_product.associativity,
--   left_unitor := binary_product.left_unitor,
--   right_unitor := binary_product.right_unitor,

--   tensor_map_id' := sorry, -- works `by obviously`
--   tensor_map_comp' := sorry, -- works `by obviously`
--   associator_naturality' := sorry, -- works `by obviously`
--   left_unitor_naturality' := sorry, -- works `by obviously
--   right_unitor_naturality' := sorry, -- works `by obviously
--   pentagon' := sorry, -- works `by obviously`, but slow,
--   triangle' := sorry, -- works `by obviously`
-- }

-- def braided_monoidal_of_has_products : braided_monoidal_category.{v} C :=
-- { braiding := binary_product.braiding,
--   braiding_naturality' := sorry, -- works `by obviously`
--   hexagon_forward' := sorry, -- works `by obviously`, but slow,
--   hexagon_reverse' := sorry, -- works `by obviously`, but slow
--   .. monoidal_of_has_products C
-- }

-- def symmetric_monoidal_of_has_products : symmetric_monoidal_category.{v} C :=
-- { symmetry' := binary_product.symmetry,
--   .. braided_monoidal_of_has_products C }

-- end category_theory.monoidal

-- open category_theory.monoidal

-- instance Type_symmetric : symmetric_monoidal_category.{u+1 u} (Type u) :=
-- symmetric_monoidal_of_has_products (Type u)
