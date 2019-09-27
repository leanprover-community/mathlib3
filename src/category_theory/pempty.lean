/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.discrete_category
import category_theory.equivalence

/-!
# The empty category

Defines a category structure on `pempty`, and the unique functor `pempty ⥤ C` for any category `C`.
-/

universes v u w -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory

/-- The empty category -/
instance pempty_category : small_category.{w} pempty.{w+1} :=
{ hom  := λ X Y, pempty,
  id   := by obviously,
  comp := by obviously }

namespace functor
variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

/-- The unique functor from the empty category to any target category. -/
def empty : pempty.{v+1} ⥤ C := by tidy

end functor

/-- The category `pempty` is equivalent to the category `discrete pempty`. -/
instance pempty_equiv_discrete_pempty : is_equivalence (functor.empty.{v} (discrete pempty.{v+1})) :=
by obviously

end category_theory
