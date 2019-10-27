-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import category_theory.enriched.functor

universes v u

open category_theory
open category_theory.monoidal
open category_theory.enriched_category

namespace category_theory

variables (V : Type (v+1)) [large_category V] [𝒱 : monoidal_category.{v} V]
include 𝒱

variables {C : Type u} [𝒞 : enriched_category V C]
variables {D : Type u} [𝒟 : enriched_category V D]
include 𝒞 𝒟

variables (F G : enriched_functor V C D)

-- We need at least a braiding on V before we can talk about natural transformations!

-- There is not always a V-object of natural transformations from F to G.
-- We can characterise the type of V-homs `α ⟶ (enriched_nat_trans F G)`.

-- structure enriched_nat_trans_yoneda (α : Vᵒᵖ) :=
-- (p : Π X : C, (unop α) ⟶ (F.obj X ⟶[V] G.obj X))
-- (h : Π X Y : C)

-- def enriched_nat_trans : Vᵒᵖ ⥤ Sort v :=
-- { obj := }

end category_theory
