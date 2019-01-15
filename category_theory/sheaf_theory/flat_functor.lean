-- Copyright (c) 2018 Johan Commelin. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Johan Commelin

import category_theory.limits.cones
import category_theory.sheaf_theory.sieve

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory
open category_theory category_theory.limits

variables {C : Type u₁} [𝒞 : category.{v₁} C] {X : Type u₂} [𝒳 : site.{v₁} X]
include 𝒞 𝒳

namespace functor

def is_flat.aux (F : C ⥤ X) {J : Type v₁} [small_category J] (D : J ⥤ C) (T : cone (D ⋙ F)) :
sieve T.X :=
{ val := λ Y h, ∃ (T' : cone D), nonempty ((T.extend h) ⟶ (cones.functoriality F).obj T'),
  property := λ Ui fi H V g, _ }

#print is_flat.aux

def is_flat (F : C ⥤ X) : Prop :=
∀ {J : Type} [small_category J] (D : J ⥤ C) (T : cone (D ⋙ F))

end functor

end category_theory