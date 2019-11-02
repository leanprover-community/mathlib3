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
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

/-- The constant functor. For `X : C`, `of.obj X` is the functor `punit ⥤ C`
  that maps `punit.star` to `X`. -/
def of : C ⥤ (punit.{w+1} ⥤ C) := const punit

namespace of
@[simp] lemma obj_obj (X : C) : (of.obj X).obj = λ _, X := rfl
@[simp] lemma obj_map (X : C) : (of.obj X).map = λ _ _ _, 𝟙 X := rfl
@[simp] lemma map_app {X Y : C} (f : X ⟶ Y) : (of.map f).app = λ _, f := rfl
end of

def star : C ⥤ punit.{w+1} := (const C).obj punit.star
@[simp] lemma star_obj (X : C) : star.obj X = punit.star := rfl
@[simp] lemma star_map {X Y : C} (f : X ⟶ Y) : star.map f = 𝟙 _ := rfl

end functor

end category_theory
