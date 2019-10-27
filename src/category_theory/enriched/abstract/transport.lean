-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import category_theory.enriched.category

universes v u

open category_theory
open category_theory.monoidal
open opposite

namespace category_theory

open category_theory.monoidal_category
open category_theory.enriched_category

variables {V : Type (v+1)} [large_category V] [𝒱 : monoidal_category.{v} V]
variables {W : Type (v+1)} [large_category W] [𝒲 : monoidal_category.{v} W]
include 𝒱 𝒲
variables (Λ : lax_monoidal_functor.{v v} V W)

/--
We can transport enrichment along a lax monoidal functor.
-/
def transport_enrichment (Λ : lax_monoidal_functor.{v v} V W) (C : Type u) := C

variables {C : Type u} [𝒞 : enriched_category V C]
include 𝒞

instance : enriched_category W (transport_enrichment Λ C) :=
{ hom := λ X Y : C, Λ.obj (X ⟶[V] Y),
  id := λ X : C, Λ.ε ≫ Λ.map (𝟙[V] X),
  comp := λ X Y Z : C, Λ.μ (X ⟶[V] Y) (Y ⟶[V] Z) ≫ Λ.map (comp V X Y Z),
  id_comp' := λ X Y,
  begin
    sorry, -- this needs paper, or rewrite_search
  end,
  comp_id' := sorry,
  assoc' := sorry }

end category_theory
