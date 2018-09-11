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

def app {F G : C ⥤ D} (α : F ≅ G) (X : C) : F X ≅ G X :=
{ hom := (α : F ⟶ G) X,
  inv := (α.symm : G ⟶ F) X,
  hom_inv_id' := begin rw [← functor.category.comp_app, iso.hom_inv_id], refl, end,
  inv_hom_id' := begin rw [← functor.category.comp_app, iso.inv_hom_id], refl, end }

instance {F G : C ⥤ D} : has_coe_to_fun (F ≅ G) :=
{ F   := λ α, Π X : C, (F X) ≅ (G X),
  coe := λ α, app α }

@[simp] lemma comp_app {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) (X : C) : 
  ((α ≪≫ β) : F ⟹ H) X = α X ≪≫ β X := rfl

@[simp] lemma hom_eq_coe {F G : C ⥤ D} (α : F ≅ G) (X : C) : α.hom X = (α : F ⟶ G) X := rfl
@[simp] lemma inv_eq_symm_coe {F G : C ⥤ D} (α : F ≅ G) (X : C) : α.inv X = (α.symm : G ⟶ F) X := rfl

variables {F G : C ⥤ D} 

instance hom_app_is_iso (α : F ≅ G) (X : C) : is_iso ((α : F ⟶ G) X) := 
{ inv := α.inv X,
  hom_inv_id' := begin dsimp at *, erw [←functor.category.comp_app, iso.hom_inv_id, ←functor.category.id_app] end,
  inv_hom_id' := begin dsimp at *, erw [←functor.category.comp_app, iso.inv_hom_id, ←functor.category.id_app] end }
instance inv_app_is_iso (α : F ≅ G) (X : C) : is_iso ((α.symm : G ⟶ F) X) := 
{ inv := α.hom X,
  hom_inv_id' := begin dsimp at *, erw [is_iso.hom_inv_id] end,
  inv_hom_id' := begin dsimp at *, erw [is_iso.hom_inv_id] end }

variables {X Y : C}
@[simp] lemma naturality_1 (α : F ≅ G) (f : X ⟶ Y) : ((α.symm : G ⟶ F) X) ≫ (F.map f) ≫ ((α : F ⟶ G) Y) = G.map f :=
begin erw [nat_trans.naturality, ←category.assoc, is_iso.hom_inv_id, category.id_comp] end
@[simp] lemma naturality_2 (α : F ≅ G) (f : X ⟶ Y) : ((α : F ⟶ G) X) ≫ (G.map f) ≫ ((α.symm : G ⟶ F) Y) = F.map f :=
begin erw [nat_trans.naturality, ←category.assoc, is_iso.hom_inv_id, category.id_comp] end

def of_components
  (app : ∀ X : C, (F X) ≅ (G X))
  (naturality : ∀ {X Y : C} (f : X ⟶ Y), (F.map f) ≫ ((app Y) : F Y ⟶ G Y) = ((app X) : F X ⟶ G X) ≫ (G.map f)) : F ≅ G :=
{ hom  := { app := λ X, ((app X) : F X ⟶ G X), },
  inv  := { app := λ X, ((app X).symm : G X ⟶ F X),
            naturality' := λ X Y f, begin 
                                      let p := congr_arg (λ f, (app X).inv ≫ (f ≫ (app Y).inv)) (eq.symm (naturality f)),
                                      dsimp at *, 
                                      simp at *, 
                                      erw [←p, ←category.assoc, is_iso.hom_inv_id, category.id_comp],
                                    end } }

end category_theory.nat_iso