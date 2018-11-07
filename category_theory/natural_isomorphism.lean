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
{ hom := (α : F ⟶ G).app X,
  inv := (α.symm : G ⟶ F).app X,
  hom_inv_id' := begin rw [← functor.category.comp_app, iso.hom_inv_id], refl, end,
  inv_hom_id' := begin rw [← functor.category.comp_app, iso.inv_hom_id], refl, end }

-- TODO remove this too
instance {F G : C ⥤ D} : has_coe_to_fun (F ≅ G) :=
{ F   := λ α, Π X : C, (F.obj X) ≅ (G.obj X),
  coe := λ α, app α }

@[simp] lemma mk_app {F G : C ⥤ D} (hom : F ⟹ G) (inv) (hom_inv_id') (inv_hom_id') (X : C) :
  ({ hom := hom, inv := inv, hom_inv_id' := hom_inv_id', inv_hom_id' := inv_hom_id' } : F ≅ G) X =
  { hom := hom.app X, inv := inv.app X,
    hom_inv_id' := congr_fun (congr_arg nat_trans.app hom_inv_id') X,
    inv_hom_id' := congr_fun (congr_arg nat_trans.app inv_hom_id') X } :=
rfl
@[simp] lemma mk_app' {F G : C ⥤ D} (hom : F ⟹ G) (inv) (hom_inv_id') (inv_hom_id') (X : C) :
  (({ hom := hom, inv := inv, hom_inv_id' := hom_inv_id', inv_hom_id' := inv_hom_id' } : F ≅ G) : F ⟹ G).app X = hom.app X :=
rfl

@[simp] lemma comp_app {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) (X : C) :
  ((α ≪≫ β) : F ⟹ H).app X = α X ≪≫ β X := rfl

@[simp] lemma hom_eq_coe {F G : C ⥤ D} (α : F ≅ G) (X : C) : α.hom.app X = (α : F ⟶ G).app X := rfl
@[simp] lemma inv_eq_symm_coe {F G : C ⥤ D} (α : F ≅ G) (X : C) : α.inv.app X = (α.symm : G ⟶ F).app X := rfl

variables {F G : C ⥤ D}

instance hom_app_is_iso (α : F ≅ G) (X : C) : is_iso ((α : F ⟶ G).app X) :=
{ inv := α.inv.app X,
  hom_inv_id' := begin dsimp at *, rw [←functor.category.comp_app, iso.hom_inv_id, ←functor.category.id_app] end,
  inv_hom_id' := begin dsimp at *, rw [←functor.category.comp_app, iso.inv_hom_id, ←functor.category.id_app] end }
instance inv_app_is_iso (α : F ≅ G) (X : C) : is_iso ((α.symm : G ⟶ F).app X) :=
{ inv := α.hom.app X,
  hom_inv_id' := begin dsimp at *, erw [is_iso.hom_inv_id] end,
  inv_hom_id' := begin dsimp at *, erw [is_iso.hom_inv_id] end }

variables {X Y : C}
@[simp] lemma naturality_1 (α : F ≅ G) (f : X ⟶ Y) :
  ((α.symm : G ⟶ F).app X) ≫ (F.map f) ≫ ((α : F ⟶ G).app Y) = G.map f :=
begin erw [nat_trans.naturality, ←category.assoc, is_iso.hom_inv_id, category.id_comp] end
@[simp] lemma naturality_2 (α : F ≅ G) (f : X ⟶ Y) :
  ((α : F ⟶ G).app X) ≫ (G.map f) ≫ ((α.symm : G ⟶ F).app Y) = F.map f :=
begin erw [nat_trans.naturality, ←category.assoc, is_iso.hom_inv_id, category.id_comp] end

def of_components (app : ∀ X : C, (F.obj X) ≅ (G.obj X))
  (naturality : ∀ {X Y : C} (f : X ⟶ Y), (F.map f) ≫ ((app Y) : F.obj Y ⟶ G.obj Y) = ((app X) : F.obj X ⟶ G.obj X) ≫ (G.map f)) :
  F ≅ G :=
{ hom  := { app := λ X, ((app X) : F.obj X ⟶ G.obj X), },
  inv  :=
  { app := λ X, ((app X).symm : G.obj X ⟶ F.obj X),
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
  ((of_components app naturality) : F ⟹ G).app X = app X := rfl
@[simp] def of_components.inv_app (app : ∀ X : C, (F.obj X) ≅ (G.obj X)) (naturality) (X) :
  ((of_components app naturality).symm : G ⟹ F).app X = (app X).symm := rfl

end category_theory.nat_iso

namespace category_theory.functor

universes u₁ u₂ v₁ v₂

section
variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
          {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

@[simp] def id_comp (F : C ⥤ D) : functor.id C ⋙ F ≅ F :=
{ hom :=
  { app := λ X, 𝟙 (F.obj X) },
  inv :=
  { app := λ X, 𝟙 (F.obj X) }
}
@[simp] def comp_id (F : C ⥤ D) : F ⋙ functor.id D ≅ F :=
{ hom :=
  { app := λ X, 𝟙 (F.obj X) },
  inv :=
  { app := λ X, 𝟙 (F.obj X) }
}

universes u₃ v₃ u₄ v₄

variables {A : Type u₃} [𝒜 : category.{u₃ v₃} A]
          {B : Type u₄} [ℬ : category.{u₄ v₄} B]
include 𝒜 ℬ
variables (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)

@[simp] def assoc : (F ⋙ G) ⋙ H ≅ F ⋙ (G ⋙ H ):=
{ hom :=
  { app := λ X, 𝟙 (H.obj (G.obj (F.obj X))) },
  inv :=
  { app := λ X, 𝟙 (H.obj (G.obj (F.obj X))) }
}

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