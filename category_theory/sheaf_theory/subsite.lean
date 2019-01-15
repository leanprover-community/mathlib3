-- Copyright (c) 2019 Johan Commelin. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Johan Commelin

import category_theory.sheaf_theory.flat_functor

universes v v₁ v₂ u u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation


namespace category_theory
open category_theory site

variables {C : Type u₁} [𝒞 : category.{v} C] {X : Type u₂} [𝒳 : site.{v} X]
include 𝒞 𝒳

def coverage.induced (F : C ⥤ X) : coverage C :=
{ covers := λ U c, sieve.is_covering (covering_family.map F c).generate_sieve,
  property :=
  begin
    intros U V g f H,
    tidy {trace_result := tt},
  end }

end category_theory