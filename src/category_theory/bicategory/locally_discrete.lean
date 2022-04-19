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
def locally_discrete := discrete C

namespace locally_discrete

instance [inhabited C] : inhabited (locally_discrete C) :=
by { dsimp [locally_discrete], apply_instance, }

instance [category_struct.{v} C] : category_struct (locally_discrete C) :=
by { dsimp [locally_discrete], apply_instance, }

variables {C} [category_struct.{v} C]

@[priority 900]
instance hom_small_category (X Y : locally_discrete C) : small_category (X ⟶ Y) :=
{ hom  := λ f g, ulift (plift (f = g)),
  id   := λ f, ulift.up (plift.up rfl),
  comp := λ f g h θ η, by { cases f, cases g, cases g, rcases θ with ⟨⟨⟨⟩⟩⟩, exact η } }

/-- Extract the equation from a 2-morphism in a locally discrete 2-category. -/
lemma eq_of_hom {X Y : locally_discrete C} {f g : X ⟶ Y} (η : f ⟶ g) : f = g := η.down.down

end locally_discrete

variables (C) [category.{v} C]

/--
The locally discrete bicategory on a category is a bicategory in which the objects and the
1-morphisms are the same as those in the underlying category, and the 2-morphisms are the
equalities between 1-morphisms.
-/
instance locally_discrete_bicategory : bicategory (locally_discrete C) :=
{ whisker_left  := λ X Y Z f g h η, eq_to_hom (congr_arg2 (≫) rfl (locally_discrete.eq_of_hom η)),
  whisker_right := λ X Y Z f g η h, eq_to_hom (congr_arg2 (≫) (locally_discrete.eq_of_hom η) rfl),
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
{ obj := λ X, F.obj X.as,
  map := λ X Y f, F.map (eq_to_hom (eq_of_hom f)),
  map₂ := λ i j f g η, eq_to_hom (congr_arg _ rfl),
  map_id := λ i, eq_to_hom (F.map_id i.as),
  map_comp := λ i j k f g,
    eq_to_hom (by { cases i, cases j, cases k, convert F.map_comp _ _, simp, }),
  .. F }

end category_theory
