-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.isomorphism

universes u₁ v₁ u₂ v₂ u₃ v₃

namespace category_theory

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

class full (F : C ⥤ D) :=
(preimage : ∀ {X Y : C} (f : (F.obj X) ⟶ (F.obj Y)), X ⟶ Y)
(witness'  : ∀ {X Y : C} (f : (F.obj X) ⟶ (F.obj Y)), F.map (preimage f) = f . obviously)

restate_axiom full.witness'
attribute [simp] full.witness

class faithful (F : C ⥤ D) : Prop :=
(injectivity' : ∀ {X Y : C} {f g : X ⟶ Y} (p : F.map f = F.map g), f = g . obviously)

restate_axiom faithful.injectivity'

namespace functor
def injectivity (F : C ⥤ D) [faithful F] {X Y : C} {f g : X ⟶ Y} (p : F.map f = F.map g) : f = g :=
faithful.injectivity F p

def preimage (F : C ⥤ D) [full F] {X Y : C} (f : F.obj X ⟶ F.obj Y) : X ⟶ Y :=
full.preimage.{u₁ v₁ u₂ v₂}  f
@[simp] lemma image_preimage (F : C ⥤ D) [full F] {X Y : C} (f : F.obj X ⟶ F.obj Y) :
  F.map (preimage F f) = f :=
by unfold preimage; obviously
end functor


section
variables {F : C ⥤ D} [full F] [faithful F] {X Y : C}
def preimage_iso (f : (F.obj X) ≅ (F.obj Y)) : X ≅ Y :=
{ hom := F.preimage f.hom,
  inv := F.preimage f.inv,
  hom_inv_id' := begin apply @faithful.injectivity _ _ _ _ F, obviously, end,
  inv_hom_id' := begin apply @faithful.injectivity _ _ _ _ F, obviously, end, }

@[simp] lemma preimage_iso_hom (f : (F.obj X) ≅ (F.obj Y)) :
  (preimage_iso f).hom = F.preimage f.hom := rfl
@[simp] lemma preimage_iso_inv (f : (F.obj X) ≅ (F.obj Y)) :
  (preimage_iso f).inv = F.preimage (f.inv) := rfl
end

class fully_faithful (F : C ⥤ D) extends (full F), (faithful F).
end category_theory

namespace category_theory

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
include 𝒞

instance full.id : full (functor.id C) :=
{ preimage := λ _ _ f, f }

instance : faithful (functor.id C) := by obviously

instance : fully_faithful (functor.id C) := { ((by apply_instance) : full (functor.id C)) with }

variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D] {E : Type u₃} [ℰ : category.{u₃ v₃} E]
include 𝒟 ℰ
variables (F : C ⥤ D) (G : D ⥤ E)

instance faithful.comp [faithful F] [faithful G] : faithful (F ⋙ G) :=
{ injectivity' := λ _ _ _ _ p, F.injectivity (G.injectivity p) }
instance full.comp [full F] [full G] : full (F ⋙ G) :=
{ preimage := λ _ _ f, F.preimage (G.preimage f) }

end category_theory

