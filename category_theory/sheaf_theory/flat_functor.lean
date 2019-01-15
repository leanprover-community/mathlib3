-- Copyright (c) 2018 Johan Commelin. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Johan Commelin

import category_theory.limits.cones
import category_theory.sheaf_theory.sieve

universes v v₁ v₂ u u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory
open category_theory category_theory.limits

namespace functor
variables {C : Type u₁} [𝒞 : category.{v₁} C] {X : Type u₂} [𝒳 : site.{v₁} X]
include 𝒞 𝒳

def is_flat.aux (F : C ⥤ X) {J : Type v₁} [small_category J] (D : J ⥤ C) (T : cone (D ⋙ F)) :
sieve T.X :=
{ val := λ Y h, ∃ (T' : cone D), nonempty ((T.extend h) ⟶ (map_cone F T')),
  property := λ Ui fi H V g,
  begin
    rcases H with ⟨T',⟨α⟩⟩,
    use T',
    refine ⟨_ ≫ α⟩,
    exact { hom := g }
  end }

def is_flat (F : C ⥤ X) : Prop :=
∀ {J} [small_category J], by resetI; exact ∀ (D : J ⥤ C) (T : cone (D ⋙ F)),
sieve.is_covering (is_flat.aux F D T)

end functor

namespace functor
open site

variables {X : Type u} [𝒳 : site.{v} X]
variables {Y : Type u} [𝒴 : site.{v} Y]
include 𝒳 𝒴

def preserves_covers (F : X ⥤ Y) : Prop :=
∀ {U} {c} (hc : c ∈ covers U), covering_family.map F c ∈ (covers $ F.obj U)

def is_morphism_of_sites (F : X ⥤ Y) : Prop :=
is_flat F ∧ preserves_covers F

end functor

end category_theory