-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.functor

universes u v

namespace category_theory

instance punit_category : small_category punit :=
{ hom  := λ X Y, punit,
  id   := λ _, punit.star,
  comp := λ _ _ _ _ _, punit.star }

namespace functor
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def of_obj (X : C) : punit ⥤ C :=
{ obj := λ _, X,
  map := λ _ _ _, 𝟙 X }

@[simp] lemma of_obj_obj (X : C) (a : punit) : (of_obj X).obj a = X := rfl

end functor

end category_theory
