/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import category_theory.single_obj

/-!
# Category of groupoids

This file contains the definition of the category `Groupoid` of all groupoids.
In this category objects are groupoids and morphisms are functors
between these groupoids.

We also provide two “forgetting” functors: `objects : Groupoid ⥤ Type`
and `forget_to_Cat : Groupoid ⥤ Cat`.

## Implementation notes

Though `Groupoid` is not a concrete category, we use `bundled` to define
its carrier type.
-/

universes v u

namespace category_theory

/-- Category of groupoids -/
@[nolint check_univs] -- intended to be used with explicit universe parameters
def Groupoid := bundled groupoid.{v u}

namespace Groupoid

instance : inhabited Groupoid := ⟨bundled.of (single_obj punit)⟩

instance str (C : Groupoid.{v u}) : groupoid.{v u} C.α := C.str

/-- Construct a bundled `Groupoid` from the underlying type and the typeclass. -/
def of (C : Type u) [groupoid.{v} C] : Groupoid.{v u} := bundled.of C

/-- Category structure on `Groupoid` -/
instance category : large_category.{max v u} Groupoid.{v u} :=
{ hom := λ C D, C.α ⥤ D.α,
  id := λ C, 𝟭 C.α,
  comp := λ C D E F G, F ⋙ G,
  id_comp' := λ C D F, by cases F; refl,
  comp_id' := λ C D F, by cases F; refl,
  assoc' := by intros; refl }

/-- Functor that gets the set of objects of a groupoid. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Groupoid.{v u} ⥤ Type u :=
{ obj := bundled.α,
  map := λ C D F, F.obj }

/-- Forgetting functor to `Cat` -/
def forget_to_Cat : Groupoid.{v u} ⥤ Cat.{v u} :=
{ obj := λ C, Cat.of C.α,
  map := λ C D, id }

instance forget_to_Cat_full : full forget_to_Cat :=
{ preimage := λ C D, id }

instance forget_to_Cat_faithful : faithful forget_to_Cat := { }

end Groupoid

end category_theory
