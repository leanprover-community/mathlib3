-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.functor

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory

instance pempty_category : small_category pempty :=
{ hom  := λ X Y, pempty,
  id   := by obviously,
  comp := by obviously }

namespace functor
variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

def empty : pempty ⥤ C := by tidy

end functor

end category_theory
