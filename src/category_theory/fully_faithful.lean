/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.isomorphism

universes v₁ v₂ v₃ u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒞 𝒟

class full (F : C ⥤ D) :=
(preimage : ∀ {X Y : C} (f : (F.obj X) ⟶ (F.obj Y)), X ⟶ Y)
(witness' : ∀ {X Y : C} (f : (F.obj X) ⟶ (F.obj Y)), F.map (preimage f) = f . obviously)

restate_axiom full.witness'
attribute [simp] full.witness

class faithful (F : C ⥤ D) : Prop :=
(injectivity' : ∀ {X Y : C} {f g : X ⟶ Y} (p : F.map f = F.map g), f = g . obviously)

restate_axiom faithful.injectivity'

namespace functor
def injectivity (F : C ⥤ D) [faithful F] {X Y : C} {f g : X ⟶ Y} (p : F.map f = F.map g) : f = g :=
faithful.injectivity F p

def preimage (F : C ⥤ D) [full F] {X Y : C} (f : F.obj X ⟶ F.obj Y) : X ⟶ Y :=
full.preimage.{v₁ v₂} f
@[simp] lemma image_preimage (F : C ⥤ D) [full F] {X Y : C} (f : F.obj X ⟶ F.obj Y) :
  F.map (preimage F f) = f :=
by unfold preimage; obviously
end functor


variables {F : C ⥤ D} [full F] [faithful F] {X Y Z : C}
def preimage_iso (f : (F.obj X) ≅ (F.obj Y)) : X ≅ Y :=
{ hom := F.preimage f.hom,
  inv := F.preimage f.inv,
  hom_inv_id' := F.injectivity (by simp),
  inv_hom_id' := F.injectivity (by simp), }

@[simp] lemma preimage_iso_hom (f : (F.obj X) ≅ (F.obj Y)) :
  (preimage_iso f).hom = F.preimage f.hom := rfl
@[simp] lemma preimage_iso_inv (f : (F.obj X) ≅ (F.obj Y)) :
  (preimage_iso f).inv = F.preimage (f.inv) := rfl

@[simp] lemma preimage_id : F.preimage (𝟙 (F.obj X)) = 𝟙 X :=
F.injectivity (by simp)
@[simp] lemma preimage_comp (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z) :
  F.preimage (f ≫ g) = F.preimage f ≫ F.preimage g :=
F.injectivity (by simp)
@[simp] lemma preimage_map (f : X ⟶ Y) :
  F.preimage (F.map f) = f :=
F.injectivity (by simp)

variables (F)
def is_iso_of_fully_faithful (f : X ⟶ Y) [is_iso (F.map f)] : is_iso f :=
{ inv := F.preimage (inv (F.map f)),
  hom_inv_id' := F.injectivity (by simp),
  inv_hom_id' := F.injectivity (by simp) }

end category_theory

namespace category_theory

variables {C : Type u₁} [𝒞 : category.{v₁} C]
include 𝒞

instance full.id : full (𝟭 C) :=
{ preimage := λ _ _ f, f }

instance : faithful (𝟭 C) := by obviously

variables {D : Type u₂} [𝒟 : category.{v₂} D] {E : Type u₃} [ℰ : category.{v₃} E]
include 𝒟 ℰ
variables (F : C ⥤ D) (G : D ⥤ E)

instance faithful.comp [faithful F] [faithful G] : faithful (F ⋙ G) :=
{ injectivity' := λ _ _ _ _ p, F.injectivity (G.injectivity p) }
instance full.comp [full F] [full G] : full (F ⋙ G) :=
{ preimage := λ _ _ f, F.preimage (G.preimage f) }

end category_theory
