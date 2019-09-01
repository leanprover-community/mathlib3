import category_theory.concrete_category

/-!
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

universes v u

namespace category_theory

/-- Category of categories. -/
def Cat := bundled category.{v u}

namespace Cat

instance str (C : Cat.{v u}) : category.{v u} C.α := C.str

def of (C : Type u) [category.{v} C] : Cat.{v u} := bundled.of C

/-- Category structure on `Cat` -/
instance category : category.{(max u v)+1 (max v (u+1))} Cat.{v u} :=
{ hom := λ C D, C.α ⥤ D.α,
  id := λ C, 𝟭 C.α,
  comp := λ C D E F G, F ⋙ G,
  id_comp' := λ C D F, by cases F; refl,
  comp_id' := λ C D F, by cases F; refl,
  assoc' := by intros; refl }

/-- Functor that gets the set of objects of a category. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Cat.{v u} ⥤ Type u :=
{ obj := bundled.α,
  map := λ C D F, F.obj }

end Cat

end category_theory
