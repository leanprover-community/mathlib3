-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.functor_category

namespace category_theory

universes u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C]
          (D : Type u₂) [𝒟 : category.{u₂ v₂} D]
          (E : Type u₃) [ℰ : category.{u₃ v₃} E]
include 𝒞 𝒟 ℰ

def whiskering_left : (C ⥤ D) ⥤ ((D ⥤ E) ⥤ (C ⥤ E)) :=
{ obj := λ F,
  { obj := λ G, F ⋙ G,
    map := λ G H α,
    { app := λ c, α.app (F.obj c),
      naturality' := by intros X Y f; rw [functor.comp_map, functor.comp_map, α.naturality] } },
  map := λ F G τ,
  { app := λ H,
    { app := λ c, H.map (τ.app c),
      naturality' := begin intros X Y f, dsimp at *, rw [←H.map_comp, ←H.map_comp, ←τ.naturality] end },
    naturality' := begin intros X Y f, ext1, dsimp at *, rw [←nat_trans.naturality] end } }

def whiskering_right : (D ⥤ E) ⥤ ((C ⥤ D) ⥤ (C ⥤ E)) :=
{ obj := λ H,
  { obj := λ F, F ⋙ H,
    map := λ _ _ α,
    { app := λ c, H.map (α.app c),
      naturality' := by intros X Y f;
        rw [functor.comp_map, functor.comp_map, ←H.map_comp, ←H.map_comp, α.naturality] } },
  map := λ G H τ,
  { app := λ F,
    { app := λ c, τ.app (F.obj c),
      naturality' := begin intros X Y f, dsimp at *, rw [τ.naturality] end },
    naturality' := begin intros X Y f, ext1, dsimp at *, rw [←nat_trans.naturality] end } }

variables {C} {D} {E}

def whisker_left (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟹ H) : (F ⋙ G) ⟹ (F ⋙ H) :=
((whiskering_left C D E).obj F).map α

@[simp] lemma whisker_left.app (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟹ H) (X : C) :
  (whisker_left F α).app X = α.app (F.obj X) :=
rfl

def whisker_right {G H : C ⥤ D} (α : G ⟹ H) (F : D ⥤ E) : (G ⋙ F) ⟹ (H ⋙ F) :=
((whiskering_right C D E).obj F).map α

@[simp] lemma whisker_right.app {G H : C ⥤ D} (α : G ⟹ H) (F : D ⥤ E) (X : C) :
   (whisker_right α F).app X = F.map (α.app X) :=
rfl

@[simp] lemma whisker_left_id (F : C ⥤ D) {G : D ⥤ E} :
  whisker_left F (nat_trans.id G) = nat_trans.id (F.comp G) :=
rfl

@[simp] lemma whisker_right_id {G : C ⥤ D} (F : D ⥤ E) :
  whisker_right (nat_trans.id G) F = nat_trans.id (G.comp F) :=
((whiskering_right C D E).obj F).map_id _

@[simp] lemma whisker_left_vcomp (F : C ⥤ D) {G H K : D ⥤ E} (α : G ⟹ H) (β : H ⟹ K) :
  whisker_left F (α ⊟ β) = (whisker_left F α) ⊟ (whisker_left F β) :=
rfl

@[simp] lemma whisker_right_vcomp {G H K : C ⥤ D} (α : G ⟹ H) (β : H ⟹ K) (F : D ⥤ E)  :
  whisker_right (α ⊟ β) F = (whisker_right α F) ⊟ (whisker_right β F) :=
((whiskering_right C D E).obj F).map_comp α β

variables {B : Type u₄} [ℬ : category.{u₄ v₄} B]
include ℬ

local attribute [elab_simple] whisker_left whisker_right

@[simp] lemma whisker_left_twice (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ⟹ K) :
  whisker_left F (whisker_left G α) = whisker_left (F ⋙ G) α :=
rfl

@[simp] lemma whisker_right_twice {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟹ K) :
  whisker_right (whisker_right α F) G = whisker_right α (F ⋙ G) :=
rfl

lemma whisker_right_left (F : B ⥤ C) {G H : C ⥤ D} (α : G ⟹ H) (K : D ⥤ E) :
  whisker_right (whisker_left F α) K = whisker_left F (whisker_right α K) :=
rfl

end category_theory
