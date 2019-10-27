-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import category_theory.enriched.category

universes v u

open category_theory
open category_theory.monoidal
open category_theory.enriched_category

namespace category_theory

variables (V : Type (v+1)) [large_category V] [𝒱 : monoidal_category.{v} V]
include 𝒱

section
variables (C : Type u) [𝒞 : enriched_category V C]
variables (D : Type u) [𝒟 : enriched_category V D]
include 𝒞 𝒟

structure enriched_functor :=
(obj : C → D)
(map : Π X Y : C, (X ⟶[V] Y) ⟶ (obj X ⟶[V] obj Y))
(map_id' : Π X : C, (𝟙[V] X) ≫ map X X = 𝟙[V] (obj X) . obviously)
(map_comp' : Π X Y Z : C, comp _ X Y Z ≫ map X Z = (map X Y ⊗ map Y Z) ≫ comp _ _ _ _ . obviously)

restate_axiom enriched_functor.map_id'
restate_axiom enriched_functor.map_comp'
attribute [simp, reassoc] enriched_functor.map_id enriched_functor.map_comp
end

namespace enriched_functor

variables (C : Type u) [𝒞 : enriched_category V C]
include 𝒞

def id : enriched_functor V C C :=
{ obj := id,
  map := λ X Y, 𝟙 (X ⟶[V] Y) }

variables {C}
variables {D : Type u} [𝒟 : enriched_category V D]
variables {E : Type u} [ℰ : enriched_category V E]
include 𝒟 ℰ

def comp (F : enriched_functor V C D) (G : enriched_functor V D E) : enriched_functor V C E :=
{ obj := λ X, G.obj (F.obj X),
  map := λ X Y, F.map _ _ ≫ G.map _ _  }

end enriched_functor

end category_theory
