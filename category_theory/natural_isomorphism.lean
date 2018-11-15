-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import category_theory.isomorphism
import category_theory.functor_category

open category_theory

namespace category_theory.nat_iso

universes u₁ u₂ v₁ v₂

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

def app {F G : C ⥤ D} (α : F ≅ G) (X : C) : F.obj X ≅ G.obj X :=
{ hom := α.hom.app X,
  inv := α.inv.app X,
  hom_inv_id' := begin rw [← functor.category.comp_app, iso.hom_inv_id], refl, end,
  inv_hom_id' := begin rw [← functor.category.comp_app, iso.inv_hom_id], refl, end }

@[simp] lemma comp_app {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) (X : C) :
  app (α ≪≫ β) X = app α X ≪≫ app β X := rfl

@[simp] lemma app_hom {F G : C ⥤ D} (α : F ≅ G) (X : C) : (app α X).hom = α.hom.app X := rfl
@[simp] lemma app_inv {F G : C ⥤ D} (α : F ≅ G) (X : C) : (app α X).inv = α.inv.app X := rfl

variables {F G : C ⥤ D}

instance hom_app_is_iso (α : F ≅ G) (X : C) : is_iso (α.hom.app X) :=
{ inv := α.inv.app X,
  hom_inv_id' := begin rw [←functor.category.comp_app, iso.hom_inv_id, ←functor.category.id_app] end,
  inv_hom_id' := begin rw [←functor.category.comp_app, iso.inv_hom_id, ←functor.category.id_app] end }
instance inv_app_is_iso (α : F ≅ G) (X : C) : is_iso (α.inv.app X) :=
{ inv := α.hom.app X,
  hom_inv_id' := begin rw [←functor.category.comp_app, iso.inv_hom_id, ←functor.category.id_app] end,
  inv_hom_id' := begin rw [←functor.category.comp_app, iso.hom_inv_id, ←functor.category.id_app] end }

variables {X Y : C}
@[simp] lemma naturality_1 (α : F ≅ G) (f : X ⟶ Y) :
  (α.inv.app X) ≫ (F.map f) ≫ (α.hom.app Y) = G.map f :=
begin erw [nat_trans.naturality, ←category.assoc, is_iso.hom_inv_id, category.id_comp] end
@[simp] lemma naturality_2 (α : F ≅ G) (f : X ⟶ Y) :
  (α.hom.app X) ≫ (G.map f) ≫ (α.inv.app Y) = F.map f :=
begin erw [nat_trans.naturality, ←category.assoc, is_iso.hom_inv_id, category.id_comp] end

def of_components (app : ∀ X : C, (F.obj X) ≅ (G.obj X))
  (naturality : ∀ {X Y : C} (f : X ⟶ Y), (F.map f) ≫ ((app Y).hom) = ((app X).hom) ≫ (G.map f)) :
  F ≅ G :=
{ hom  := { app := λ X, ((app X).hom), },
  inv  :=
  { app := λ X, ((app X).inv),
    naturality' := λ X Y f,
    begin
      let p := congr_arg (λ f, (app X).inv ≫ (f ≫ (app Y).inv)) (eq.symm (naturality f)),
      dsimp at *,
      simp at *,
      erw [←p, ←category.assoc, is_iso.hom_inv_id, category.id_comp],
    end } }.

@[simp] def of_components.app (app' : ∀ X : C, (F.obj X) ≅ (G.obj X)) (naturality) (X) :
  app (of_components app' naturality) X = app' X :=
by tidy
@[simp] def of_components.hom_app (app : ∀ X : C, (F.obj X) ≅ (G.obj X)) (naturality) (X) :
  (of_components app naturality).hom.app X = (app X).hom := rfl
@[simp] def of_components.inv_app (app : ∀ X : C, (F.obj X) ≅ (G.obj X)) (naturality) (X) :
  (of_components app naturality).inv.app X = (app X).inv := rfl

end category_theory.nat_iso

namespace category_theory.functor

universes u₁ u₂ v₁ v₂

section
variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
          {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

@[simp] def id_comp (F : C ⥤ D) : functor.id C ⋙ F ≅ F :=
{ hom := { app := λ X, 𝟙 (F.obj X) },
  inv := { app := λ X, 𝟙 (F.obj X) } }
@[simp] def comp_id (F : C ⥤ D) : F ⋙ functor.id D ≅ F :=
{ hom := { app := λ X, 𝟙 (F.obj X) },
  inv := { app := λ X, 𝟙 (F.obj X) } }

universes u₃ v₃ u₄ v₄

variables {A : Type u₃} [𝒜 : category.{u₃ v₃} A]
          {B : Type u₄} [ℬ : category.{u₄ v₄} B]
include 𝒜 ℬ
variables (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)

@[simp] def assoc : (F ⋙ G) ⋙ H ≅ F ⋙ (G ⋙ H ):=
{ hom := { app := λ X, 𝟙 (H.obj (G.obj (F.obj X))) },
  inv := { app := λ X, 𝟙 (H.obj (G.obj (F.obj X))) } }

-- When it's time to define monoidal categories and 2-categories,
-- we'll need to add lemmas relating these natural isomorphisms,
-- in particular the pentagon for the associator.
end

section
variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
include 𝒞

def ulift_down_up : ulift_down.{u₁ v₁ u₂} C ⋙ ulift_up C ≅ functor.id (ulift.{u₂} C) :=
{ hom := { app := λ X, @category.id (ulift.{u₂} C) _ X },
  inv := { app := λ X, @category.id (ulift.{u₂} C) _ X } }

def ulift_up_down : ulift_up.{u₁ v₁ u₂} C ⋙ ulift_down C ≅ functor.id C :=
{ hom := { app := λ X, 𝟙 X },
  inv := { app := λ X, 𝟙 X } }

end

end category_theory.functor