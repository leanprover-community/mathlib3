/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.sites.compatible_plus
import category_theory.sites.sheafification

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.


In this file, we prove that sheafification is compatible with functors which
preserve the correct limits and colimits.

-/

namespace category_theory.grothendieck_topology

open category_theory
open category_theory.limits
open opposite

universes w₁ w₂ v u
variables {C : Type u} [category.{v} C] (J : grothendieck_topology C)
variables {D : Type w₁} [category.{max v u} D]
variables {E : Type w₂} [category.{max v u} E]
variables (F : D ⥤ E)

noncomputable theory

variables [∀ (α β : Type (max v u)) (fst snd : β → α),
  has_limits_of_shape (walking_multicospan fst snd) D]
variables [∀ (α β : Type (max v u)) (fst snd : β → α),
  has_limits_of_shape (walking_multicospan fst snd) E]
variables [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]
variables [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ E]
variables [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ F]
variables [∀ (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D), preserves_limit (W.index P).multicospan F]

variables (P : Cᵒᵖ ⥤ D)

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`.

Use the lemmas `whisker_right_to_sheafify_sheafify_comp_iso_hom`,
`to_sheafify_comp_sheafify_comp_iso_inv` and `sheafify_comp_iso_inv_eq_sheafify_lift` to reduce
the components of this isomorphisms to a state that can be handled using the universal property
of sheafification. -/
def sheafify_comp_iso : J.sheafify P ⋙ F ≅ J.sheafify (P ⋙ F) :=
J.plus_comp_iso _ _ ≪≫ (J.plus_functor _).map_iso (J.plus_comp_iso _ _)

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `F`. -/
def sheafification_whisker_left_iso (P : Cᵒᵖ ⥤ D)
  [∀ (F : D ⥤ E) (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ F]
  [∀ (F : D ⥤ E) (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D),
    preserves_limit (W.index P).multicospan F] :
  (whiskering_left _ _ E).obj (J.sheafify P) ≅
  (whiskering_left _ _ _).obj P ⋙ J.sheafification E :=
begin
  refine J.plus_functor_whisker_left_iso _ ≪≫ _ ≪≫ functor.associator _ _ _,
  refine iso_whisker_right _ _,
  refine J.plus_functor_whisker_left_iso _,
end

@[simp]
lemma sheafification_whisker_left_iso_hom_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
  [∀ (F : D ⥤ E) (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ F]
  [∀ (F : D ⥤ E) (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D),
    preserves_limit (W.index P).multicospan F] :
  (sheafification_whisker_left_iso J P).hom.app F = (J.sheafify_comp_iso F P).hom :=
begin
  dsimp [sheafification_whisker_left_iso, sheafify_comp_iso],
  rw category.comp_id,
end

@[simp]
lemma sheafification_whisker_left_iso_inv_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
  [∀ (F : D ⥤ E) (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ F]
  [∀ (F : D ⥤ E) (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D),
    preserves_limit (W.index P).multicospan F] :
  (sheafification_whisker_left_iso J P).inv.app F = (J.sheafify_comp_iso F P).inv :=
begin
  dsimp [sheafification_whisker_left_iso, sheafify_comp_iso],
  erw category.id_comp,
end

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `P`. -/
def sheafification_whisker_right_iso :
  J.sheafification D ⋙ (whiskering_right _ _ _).obj F ≅
  (whiskering_right _ _ _).obj F ⋙ J.sheafification E :=
begin
  refine functor.associator _ _ _ ≪≫ _,
  refine iso_whisker_left (J.plus_functor D) (J.plus_functor_whisker_right_iso _) ≪≫ _,
  refine _ ≪≫ functor.associator _ _ _,
  refine (functor.associator _ _ _).symm ≪≫ _,
  exact iso_whisker_right (J.plus_functor_whisker_right_iso _) (J.plus_functor E),
end

@[simp]
lemma sheafification_whisker_right_iso_hom_app :
  (J.sheafification_whisker_right_iso F).hom.app P = (J.sheafify_comp_iso F P).hom :=
begin
  dsimp [sheafification_whisker_right_iso, sheafify_comp_iso],
  simp only [category.id_comp, category.comp_id],
  erw category.id_comp,
end

@[simp]
lemma sheafification_whisker_right_iso_inv_app :
  (J.sheafification_whisker_right_iso F).inv.app P = (J.sheafify_comp_iso F P).inv :=
begin
  dsimp [sheafification_whisker_right_iso, sheafify_comp_iso],
  simp only [category.id_comp, category.comp_id],
  erw category.id_comp,
end

@[simp, reassoc]
lemma whisker_right_to_sheafify_sheafify_comp_iso_hom :
  whisker_right (J.to_sheafify _) _ ≫ (J.sheafify_comp_iso F P).hom = J.to_sheafify _ :=
begin
  dsimp [sheafify_comp_iso],
  erw [whisker_right_comp, category.assoc],
  slice_lhs 2 3 { rw plus_comp_iso_whisker_right },
  rw [category.assoc, ← J.plus_map_comp,
    whisker_right_to_plus_comp_plus_comp_iso_hom, ← category.assoc,
    whisker_right_to_plus_comp_plus_comp_iso_hom],
  refl,
end

@[simp, reassoc]
lemma to_sheafify_comp_sheafify_comp_iso_inv :
  J.to_sheafify _ ≫ (J.sheafify_comp_iso F P).inv = whisker_right (J.to_sheafify _) _ :=
by { rw iso.comp_inv_eq, simp }

section

-- We will sheafify `D`-valued presheaves in this section.
variables
  [concrete_category.{max v u} D]
  [preserves_limits (forget D)]
  [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]
  [reflects_isomorphisms (forget D)]

@[simp]
lemma sheafify_comp_iso_inv_eq_sheafify_lift : (J.sheafify_comp_iso F P).inv =
  J.sheafify_lift (whisker_right (J.to_sheafify _) _) ((J.sheafify_is_sheaf _).comp _) :=
begin
  apply J.sheafify_lift_unique,
  rw iso.comp_inv_eq,
  simp,
end

end

end category_theory.grothendieck_topology
