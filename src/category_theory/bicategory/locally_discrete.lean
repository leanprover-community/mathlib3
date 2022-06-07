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

variables {C : Type u}

/--
A type synonym for promoting any type to a category,
with the only morphisms being equalities.
-/
def locally_discrete (C : Type u) := C

namespace locally_discrete

instance : Π [inhabited C], inhabited (locally_discrete C) := id

instance [category_struct.{v} C] : category_struct (locally_discrete C) :=
{ hom := λ (X Y : C), discrete (X ⟶ Y),
  id := λ X : C, ⟨𝟙 X⟩,
  comp := λ X Y Z f g, ⟨f.as ≫ g.as⟩ }

variables {C} [category_struct.{v} C]

@[priority 900]
instance hom_small_category (X Y : locally_discrete C) : small_category (X ⟶ Y) :=
category_theory.discrete_category (X ⟶ Y)

/-- Extract the equation from a 2-morphism in a locally discrete 2-category. -/
lemma eq_of_hom {X Y : locally_discrete C} {f g : X ⟶ Y} (η : f ⟶ g) : f = g :=
begin
  have : discrete.mk (f.as) = discrete.mk (g.as) := congr_arg discrete.mk (eq_of_hom η),
  simpa using this
end

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
  associator := λ W X Y Z f g h, eq_to_iso $ by { unfold_projs, simp only [category.assoc] },
  left_unitor  := λ X Y f, eq_to_iso $ by { unfold_projs, simp only [category.id_comp, mk_as] },
  right_unitor := λ X Y f, eq_to_iso $ by { unfold_projs, simp only [category.comp_id, mk_as] } }

/-- A locally discrete bicategory is strict. -/
instance locally_discrete_bicategory.strict : strict (locally_discrete C) :=
{ id_comp' := by { intros, ext1, unfold_projs, apply category.id_comp },
  comp_id' := by { intros, ext1, unfold_projs, apply category.comp_id },
  assoc' := by { intros, ext1, unfold_projs, apply category.assoc } }

variables {I : Type u₁} [category.{v₁} I] {B : Type u₂} [bicategory.{w₂ v₂} B] [strict B]

/--
If `B` is a strict bicategory and `I` is a (1-)category, any functor (of 1-categories) `I ⥤ B` can
be promoted to an oplax functor from `locally_discrete I` to `B`.
-/
@[simps]
def functor.to_oplax_functor (F : I ⥤ B) : oplax_functor (locally_discrete I) B :=
{ obj := F.obj,
  map := λ X Y f, F.map f.as,
  map₂ := λ i j f g η, eq_to_hom (congr_arg _ (eq_of_hom η)),
  map_id := λ i, eq_to_hom (F.map_id i),
  map_comp := λ i j k f g, eq_to_hom (F.map_comp f.as g.as) }

end category_theory
