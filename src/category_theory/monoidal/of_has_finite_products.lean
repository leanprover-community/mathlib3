/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.category
import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.initial

open category_theory.limits

universes v u

namespace category_theory

variables (C : Type u) [𝒞 : category.{v+1} C]
include 𝒞

instance [has_finite_products.{v} C] : monoidal_category C :=
{ tensor_unit := initial C,
  tensor_obj := λ X Y, prod X Y,
  tensor_hom := λ W X Y Z f g, sorry }

end category_theory

-- has_binary_products etc is still missing from mathlib :-(

-- -- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- -- Released under Apache 2.0 license as described in the file LICENSE.
-- -- Authors: Scott Morrison

-- import category_theory.limits.binary_products
-- import category_theory.limits.terminal
-- import category_theory.limits.types
-- import ..braided_monoidal_category

-- open category_theory
-- open category_theory.monoidal

-- universes u v

-- @[obviously] meta def obviously_products := tactic.tidy { tactics := extended_tidy_tactics }

-- namespace category_theory.limits

-- attribute [search] prod.lift_fst prod.lift_snd prod.map_fst prod.map_snd

-- variables {C : Type u} [𝒞 : category.{v} C]
--           [has_binary_products.{u v} C] [has_terminal.{u v} C]
-- include 𝒞

-- @[simp] def binary_product.braiding (P Q : C) : limits.prod P Q ≅ limits.prod Q P :=
-- { hom := prod.lift (prod.snd P Q) (prod.fst P Q),
--   inv := prod.lift (prod.snd Q P) (prod.fst Q P) }

-- def binary_product.symmetry (P Q : C) :
--   (binary_product.braiding P Q).hom ≫ (binary_product.braiding Q P).hom = 𝟙 _ :=
-- by tidy

-- @[simp] def binary_product.associativity
--   (P Q R : C) : (limits.prod (limits.prod P Q) R) ≅ (limits.prod P (limits.prod Q R)) :=
-- { hom :=
--   prod.lift
--     (prod.fst _ _ ≫ prod.fst _ _)
--     (prod.lift (prod.fst _ _ ≫ prod.snd _ _) (prod.snd _ _)),
--   inv :=
--   prod.lift
--     (prod.lift (prod.fst _ _) (prod.snd _ _ ≫ prod.fst _ _))
--     (prod.snd _ _ ≫ prod.snd _ _) }

-- @[simp] def binary_product.left_unitor
--   (P : C) : (limits.prod (terminal.{u v} C) P) ≅ P :=
-- { hom := prod.snd _ _,
--   inv := prod.lift (terminal.from P) (𝟙 _) }

-- @[simp] def binary_product.right_unitor
--   (P : C) : (limits.prod P (terminal.{u v} C)) ≅ P :=
-- { hom := prod.fst _ _,
--   inv := prod.lift (𝟙 _) (terminal.from P) }

-- end category_theory.limits

-- open category_theory.limits

-- namespace category_theory.monoidal

-- variables (C : Type u) [𝒞 : category.{v} C] [has_products.{u v} C]
-- include 𝒞

-- instance : has_binary_products.{u v} C := has_binary_products_of_has_products
-- instance : has_terminal.{u v} C := has_terminal_of_has_products C

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
