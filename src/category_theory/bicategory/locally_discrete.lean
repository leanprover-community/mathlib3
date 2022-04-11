/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.discrete_category
import category_theory.bicategory.functor
import category_theory.bicategory.strict

/-!
# Locally discrete bicategories

A category `C` can be promoted to a strict bicategory `locally_discrete C`. The objects and the
1-morphisms in `locally_discrete C` are the same as the objects and the morphisms, respectively,
in `C`, and the 2-morphisms in `locally_discrete C` are the equalities between 1-morphisms. In
other words, the category consisting of the 1-morphisms between each pair of objects `X` and `Y`
in `locally_discrete C` is defined as the discrete category associated with the type `X ⟶ Y`.
-/

namespace category_theory

open bicategory discrete
open_locale bicategory

universes w₂ v v₁ v₂ u u₁ u₂

variables (C : Type u)

/--
A type alias for promoting any category to a bicategory,
with the only 2-morphisms being equalities.
-/
def locally_discrete := C

namespace locally_discrete

instance : Π [inhabited C], inhabited (locally_discrete C) := id

instance : Π [category_struct.{v} C], category_struct (locally_discrete C) := id

variables {C} [category_struct.{v} C]

@[priority 900]
instance hom_small_category (X Y : locally_discrete C) : small_category (X ⟶ Y) :=
category_theory.discrete_category (X ⟶ Y)

end locally_discrete

variables (C) [category.{v} C]

/--
The locally discrete bicategory on a category is a bicategory in which the objects and the
1-morphisms are the same as those in the underlying category, and the 2-morphisms are the
equalities between 1-morphisms.
-/
instance locally_discrete_bicategory : bicategory (locally_discrete C) :=
{ whisker_left  := λ X Y Z f g h η, eq_to_hom (congr_arg2 (≫) rfl (eq_of_hom η)),
  whisker_right := λ X Y Z f g η h, eq_to_hom (congr_arg2 (≫) (eq_of_hom η) rfl),
  associator := λ W X Y Z f g h, eq_to_iso (category.assoc f g h),
  left_unitor  := λ X Y f, eq_to_iso (category.id_comp f),
  right_unitor := λ X Y f, eq_to_iso (category.comp_id f) }

/-- A locally discrete bicategory is strict. -/
instance locally_discrete_bicategory.strict : strict (locally_discrete C) := { }

variables {I : Type u₁} [category.{v₁} I] {B : Type u₂} [bicategory.{w₂ v₂} B] [strict B]

/--
If `B` is a strict bicategory and `I` is a (1-)category, any functor (of 1-categories) `I ⥤ B` can
be promoted to an oplax functor from `locally_discrete I` to `B`.
-/
@[simps]
def functor.to_oplax_functor (F : I ⥤ B) : oplax_functor (locally_discrete I) B :=
{ map₂ := λ i j f g η, eq_to_hom (congr_arg _ (eq_of_hom η)),
  map_id := λ i, eq_to_hom (F.map_id i),
  map_comp := λ i j k f g, eq_to_hom (F.map_comp f g),
  .. F }

end category_theory
