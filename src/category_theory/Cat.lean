/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

# Category of categories

This file contains definition of category `Cat` of all categories.  In
this category objects are categories and morphisms are functors
between these categories.

## Implementation notes

Though `Cat` is not a concrete category, we use `bundled` to define
its carrier type.
-/
import category_theory.concrete_category

universes v u

namespace category_theory

/-- Category of categories. -/
def Cat := bundled category.{v u}

/-- Category structure on `Cat` -/
instance Cat.category : category.{(max u v)+1 (max v (u+1))} Cat.{v u} :=
{ hom := λ C D, @functor C.α C.str D.α D.str,
  id := λ C, @functor.id C.α C.str,
  comp := λ C D E, @functor.comp C.α C.str D.α D.str E.α E.str,
  id_comp' := λ C D f, @functor.id_comp C.α C.str D.α D.str f,
  comp_id' := λ C D f, @functor.comp_id C.α C.str D.α D.str f }

/-- Functor that gets the set of objects of a category. It is not
called `forget`, because it is not a faithful functor. -/
def Cat.objects : Cat.{v u} ⥤ Type u :=
{ obj := bundled.α,
  map := λ C D, @functor.obj C.α C.str D.α D.str }

end category_theory

