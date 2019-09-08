/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import logic.function category_theory.isomorphism

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
(injectivity' : ∀ {X Y : C}, function.injective (@functor.map _ _ _ _ F X Y) . obviously)

restate_axiom faithful.injectivity'

namespace functor
def injectivity (F : C ⥤ D) [faithful F] {X Y : C} : function.injective $ @functor.map _ _ _ _ F X Y :=
faithful.injectivity F

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

lemma faithful.of_comp [faithful $ F ⋙ G] : faithful F :=
{ injectivity' := λ X Y, (F ⋙ G).injectivity.of_comp }

variables {F G}

lemma faithful.of_comp_eq {H : C ⥤ E} [ℋ : faithful H] (h : F ⋙ G = H) : faithful F :=
@faithful.of_comp _ _ _ _ _ _ F G (h.symm ▸ ℋ)

alias faithful.of_comp_eq ← eq.faithful_of_comp

variables (F G)

protected def faithful.div (F : C ⥤ E) [faithful F] (G : D ⥤ E) [faithful G]
  (obj : C → D) (h_obj : ∀ X, G.obj (obj X) = F.obj X)
  (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
  (h_map : ∀ {X Y} {f : X ⟶ Y}, G.map (map f) == F.map f) :
  C ⥤ D :=
{ obj := obj,
  map := @map,
  map_id' :=
  begin
    assume X,
    apply G.injectivity,
    apply eq_of_heq,
    transitivity F.map (𝟙 X), from h_map,
    rw [F.map_id, G.map_id, h_obj X]
  end,
  map_comp' :=
  begin
    assume X Y Z f g,
    apply G.injectivity,
    apply eq_of_heq,
    transitivity F.map (f ≫ g), from h_map,
    rw [F.map_comp, G.map_comp],
    congr' 1;
      try { exact (h_obj _).symm };
      exact h_map.symm
  end }

lemma faithful.div_comp (F : C ⥤ E) [faithful F] (G : D ⥤ E) [faithful G]
  (obj : C → D) (h_obj : ∀ X, G.obj (obj X) = F.obj X)
  (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
  (h_map : ∀ {X Y} {f : X ⟶ Y}, G.map (map f) == F.map f) :
  (faithful.div F G obj @h_obj @map @h_map) ⋙ G = F :=
begin
  tactic.unfreeze_local_instances,
  cases F with F_obj _ _ _; cases G with G_obj _ _ _,
  unfold faithful.div functor.comp,
  unfold_projs at h_obj,
  have: F_obj = G_obj ∘ obj := (funext h_obj).symm,
  subst this,
  congr,
  funext,
  exact eq_of_heq h_map
end

lemma faithful.div_faithful (F : C ⥤ E) [faithful F] (G : D ⥤ E) [faithful G]
  (obj : C → D) (h_obj : ∀ X, G.obj (obj X) = F.obj X)
  (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
  (h_map : ∀ {X Y} {f : X ⟶ Y}, G.map (map f) == F.map f) :
  faithful (faithful.div F G obj @h_obj @map @h_map) :=
(faithful.div_comp F G _ h_obj _ @h_map).faithful_of_comp

instance full.comp [full F] [full G] : full (F ⋙ G) :=
{ preimage := λ _ _ f, F.preimage (G.preimage f) }

end category_theory
