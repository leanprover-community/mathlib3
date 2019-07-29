/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.natural_isomorphism

namespace category_theory

universes u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

section
variables (C : Type u₁) [𝒞 : category.{v₁} C]
          (D : Type u₂) [𝒟 : category.{v₂} D]
          (E : Type u₃) [ℰ : category.{v₃} E]
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
      naturality' := λ X Y f, begin dsimp, rw [←H.map_comp, ←H.map_comp, ←τ.naturality] end },
    naturality' := λ X Y f, begin ext1, dsimp, rw [f.naturality] end } }

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
      naturality' := λ X Y f, begin dsimp, rw [τ.naturality] end },
    naturality' := λ X Y f, begin ext1, dsimp, rw [←nat_trans.naturality] end } }

variables {C} {D} {E}

def whisker_left (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) : (F ⋙ G) ⟶ (F ⋙ H) :=
((whiskering_left C D E).obj F).map α

@[simp] lemma whiskering_left_obj_obj (F : C ⥤ D) (G : D ⥤ E) :
  ((whiskering_left C D E).obj F).obj G = F ⋙ G :=
rfl
@[simp] lemma whiskering_left_obj_map (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) :
  ((whiskering_left C D E).obj F).map α = whisker_left F α :=
rfl
@[simp] lemma whiskering_left_map_app_app {F G : C ⥤ D} (τ : F ⟶ G) (H : D ⥤ E) (c) :
  (((whiskering_left C D E).map τ).app H).app c = H.map (τ.app c) :=
rfl

@[simp] lemma whisker_left.app (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) (X : C) :
  (whisker_left F α).app X = α.app (F.obj X) :=
rfl

def whisker_right {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) : (G ⋙ F) ⟶ (H ⋙ F) :=
((whiskering_right C D E).obj F).map α

@[simp] lemma whiskering_right_obj_obj (G : C ⥤ D) (F : D ⥤ E) :
  ((whiskering_right C D E).obj F).obj G = G ⋙ F :=
rfl
@[simp] lemma whiskering_right_obj_map {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) :
  ((whiskering_right C D E).obj F).map α = whisker_right α F :=
rfl
@[simp] lemma whiskering_right_map_app_app (F : C ⥤ D) {G H : D ⥤ E} (τ : G ⟶ H) (c) :
  (((whiskering_right C D E).map τ).app F).app c = τ.app (F.obj c) :=
rfl

@[simp] lemma whisker_right.app {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) (X : C) :
   (whisker_right α F).app X = F.map (α.app X) :=
rfl

@[simp] lemma whisker_left_id (F : C ⥤ D) {G : D ⥤ E} :
  whisker_left F (nat_trans.id G) = nat_trans.id (F.comp G) :=
rfl
@[simp] lemma whisker_left_id' (F : C ⥤ D) {G : D ⥤ E} :
  whisker_left F (𝟙 G) = 𝟙 (F.comp G) :=
rfl

@[simp] lemma whisker_right_id {G : C ⥤ D} (F : D ⥤ E) :
  whisker_right (nat_trans.id G) F = nat_trans.id (G.comp F) :=
((whiskering_right C D E).obj F).map_id _
@[simp] lemma whisker_right_id' {G : C ⥤ D} (F : D ⥤ E) :
  whisker_right (𝟙 G) F = 𝟙 (G.comp F) :=
((whiskering_right C D E).obj F).map_id _

@[simp] lemma whisker_left_comp (F : C ⥤ D) {G H K : D ⥤ E} (α : G ⟶ H) (β : H ⟶ K) :
  whisker_left F (α ≫ β) = (whisker_left F α) ≫ (whisker_left F β) :=
rfl

@[simp] lemma whisker_right_comp {G H K : C ⥤ D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E)  :
  whisker_right (α ≫ β) F = (whisker_right α F) ≫ (whisker_right β F) :=
((whiskering_right C D E).obj F).map_comp α β

def iso_whisker_left (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) : (F ⋙ G) ≅ (F ⋙ H) :=
((whiskering_left C D E).obj F).map_iso α
@[simp] lemma iso_whisker_left_hom (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
  (iso_whisker_left F α).hom = whisker_left F α.hom :=
rfl
@[simp] lemma iso_whisker_left_inv (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
  (iso_whisker_left F α).inv = whisker_left F α.inv :=
rfl

def iso_whisker_right {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) : (G ⋙ F) ≅ (H ⋙ F) :=
((whiskering_right C D E).obj F).map_iso α
@[simp] lemma iso_whisker_right_hom {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
  (iso_whisker_right α F).hom = whisker_right α.hom F :=
rfl
@[simp] lemma iso_whisker_right_inv {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
  (iso_whisker_right α F).inv = whisker_right α.inv F :=
rfl

instance is_iso_whisker_left (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [is_iso α] : is_iso (whisker_left F α) :=
{ .. iso_whisker_left F (as_iso α) }
instance is_iso_whisker_right {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [is_iso α] : is_iso (whisker_right α F) :=
{ .. iso_whisker_right (as_iso α) F }

variables {B : Type u₄} [ℬ : category.{v₄} B]
include ℬ

local attribute [elab_simple] whisker_left whisker_right

@[simp] lemma whisker_left_twice (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) :
  whisker_left F (whisker_left G α) = whisker_left (F ⋙ G) α :=
rfl

@[simp] lemma whisker_right_twice {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟶ K) :
  whisker_right (whisker_right α F) G = whisker_right α (F ⋙ G) :=
rfl

lemma whisker_right_left (F : B ⥤ C) {G H : C ⥤ D} (α : G ⟶ H) (K : D ⥤ E) :
  whisker_right (whisker_left F α) K = whisker_left F (whisker_right α K) :=
rfl
end

namespace functor

universes u₅ v₅

variables {A : Type u₁} [𝒜 : category.{v₁} A]
variables {B : Type u₂} [ℬ : category.{v₂} B]
include 𝒜 ℬ

def left_unitor (F : A ⥤ B) : ((functor.id _) ⋙ F) ≅ F :=
{ hom := { app := λ X, 𝟙 (F.obj X) },
  inv := { app := λ X, 𝟙 (F.obj X) } }

@[simp] lemma left_unitor_hom_app {F : A ⥤ B} {X} : F.left_unitor.hom.app X = 𝟙 _ := rfl
@[simp] lemma left_unitor_inv_app {F : A ⥤ B} {X} : F.left_unitor.inv.app X = 𝟙 _ := rfl

def right_unitor (F : A ⥤ B) : (F ⋙ (functor.id _)) ≅ F :=
{ hom := { app := λ X, 𝟙 (F.obj X) },
  inv := { app := λ X, 𝟙 (F.obj X) } }

@[simp] lemma right_unitor_hom_app {F : A ⥤ B} {X} : F.right_unitor.hom.app X = 𝟙 _ := rfl
@[simp] lemma right_unitor_inv_app {F : A ⥤ B} {X} : F.right_unitor.inv.app X = 𝟙 _ := rfl

variables {C : Type u₃} [𝒞 : category.{v₃} C]
variables {D : Type u₄} [𝒟 : category.{v₄} D]
include 𝒞 𝒟

def associator (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) : ((F ⋙ G) ⋙ H) ≅ (F ⋙ (G ⋙ H)) :=
{ hom := { app := λ _, 𝟙 _ },
  inv := { app := λ _, 𝟙 _ } }

@[simp] lemma associator_hom_app {F : A ⥤ B} {G : B ⥤ C} {H : C ⥤ D} {X} :
(associator F G H).hom.app X = 𝟙 _ := rfl
@[simp] lemma associator_inv_app {F : A ⥤ B} {G : B ⥤ C} {H : C ⥤ D} {X} :
(associator F G H).inv.app X = 𝟙 _ := rfl

omit 𝒟

lemma triangle (F : A ⥤ B) (G : B ⥤ C) :
  (associator F (functor.id B) G).hom ≫ (whisker_left F (left_unitor G).hom) =
    (whisker_right (right_unitor F).hom G) :=
begin
  ext1,
  dsimp [associator, left_unitor, right_unitor],
  simp
end

variables {E : Type u₅} [ℰ : category.{v₅} E]
include 𝒟 ℰ

variables (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (K : D ⥤ E)

lemma pentagon :
  (whisker_right (associator F G H).hom K) ≫ (associator F (G ⋙ H) K).hom ≫ (whisker_left F (associator G H K).hom) =
    ((associator (F ⋙ G) H K).hom ≫ (associator F G (H ⋙ K)).hom) :=
begin
  ext1,
  dsimp [associator],
  simp,
end

end functor

end category_theory
