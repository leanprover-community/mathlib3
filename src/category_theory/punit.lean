/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.const

universes v w u -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory

instance punit_category : small_category punit :=
{ hom  := λ X Y, punit,
  id   := λ _, punit.star,
  comp := λ _ _ _ _ _, punit.star }

namespace functor
variables {C : Type u} [category.{v} C]

def star : C ⥤ punit.{w+1} := (const C).obj punit.star
@[simp] lemma star_obj (X : C) : star.obj X = punit.star := rfl
@[simp] lemma star_map {X Y : C} (f : X ⟶ Y) : star.map f = 𝟙 _ := rfl

end functor

end category_theory
