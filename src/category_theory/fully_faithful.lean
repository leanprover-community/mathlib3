/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.natural_isomorphism
import data.equiv.basic

/-!
# Full and faithful functors

We define typeclasses `full` and `faithful`, decorating functors.

Use `F.map_injective` to retrieve the fact that `F.map` is injective when `[faithful F]`,
and `F.preimage` to obtain preimages of morphisms when `[full F]`.

We prove some basic "cancellation" lemmas for full and/or faithful functors.

See `category_theory.equivalence` for the fact that a functor is an equivalence if and only if
it is fully faithful and essentially surjective.

-/

-- declare the `v`'s first; see `category_theory.category` for an explanation
universes v₁ v₂ v₃ u₁ u₂ u₃

namespace category_theory

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

/--
A functor `F : C ⥤ D` is full if for each `X Y : C`, `F.map` is surjective.
In fact, we use a constructive definition, so the `full F` typeclass contains data,
specifying a particular preimage of each `f : F.obj X ⟶ F.obj Y`.

See https://stacks.math.columbia.edu/tag/001C.
-/
class full (F : C ⥤ D) :=
(preimage : ∀ {X Y : C} (f : (F.obj X) ⟶ (F.obj Y)), X ⟶ Y)
(witness' : ∀ {X Y : C} (f : (F.obj X) ⟶ (F.obj Y)), F.map (preimage f) = f . obviously)

restate_axiom full.witness'
attribute [simp] full.witness

/--
A functor `F : C ⥤ D` is faithful if for each `X Y : C`, `F.map` is injective.

See https://stacks.math.columbia.edu/tag/001C.
-/
class faithful (F : C ⥤ D) : Prop :=
(map_injective' [] : ∀ {X Y : C}, function.injective (@functor.map _ _ _ _ F X Y) . obviously)

restate_axiom faithful.map_injective'

namespace functor
lemma map_injective (F : C ⥤ D) [faithful F] {X Y : C} :
  function.injective $ @functor.map _ _ _ _ F X Y :=
faithful.map_injective F

/-- The specified preimage of a morphism under a full functor. -/
def preimage (F : C ⥤ D) [full F] {X Y : C} (f : F.obj X ⟶ F.obj Y) : X ⟶ Y :=
full.preimage.{v₁ v₂} f
@[simp] lemma image_preimage (F : C ⥤ D) [full F] {X Y : C} (f : F.obj X ⟶ F.obj Y) :
  F.map (preimage F f) = f :=
by unfold preimage; obviously
end functor

variables {F : C ⥤ D} [full F] [faithful F] {X Y Z : C}

@[simp] lemma preimage_id : F.preimage (𝟙 (F.obj X)) = 𝟙 X :=
F.map_injective (by simp)
@[simp] lemma preimage_comp (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z) :
  F.preimage (f ≫ g) = F.preimage f ≫ F.preimage g :=
F.map_injective (by simp)
@[simp] lemma preimage_map (f : X ⟶ Y) :
  F.preimage (F.map f) = f :=
F.map_injective (by simp)

/-- If `F : C ⥤ D` is fully faithful, every isomorphism `F.obj X ≅ F.obj Y` has a preimage. -/
def preimage_iso (f : (F.obj X) ≅ (F.obj Y)) : X ≅ Y :=
{ hom := F.preimage f.hom,
  inv := F.preimage f.inv,
  hom_inv_id' := F.map_injective (by simp),
  inv_hom_id' := F.map_injective (by simp), }

@[simp] lemma preimage_iso_hom (f : (F.obj X) ≅ (F.obj Y)) :
  (preimage_iso f).hom = F.preimage f.hom := rfl
@[simp] lemma preimage_iso_inv (f : (F.obj X) ≅ (F.obj Y)) :
  (preimage_iso f).inv = F.preimage (f.inv) := rfl
@[simp] lemma preimage_iso_map_iso (f : X ≅ Y) : preimage_iso (F.map_iso f) = f :=
by tidy

variables (F)

/--
If the image of a morphism under a fully faithful functor in an isomorphism,
then the original morphisms is also an isomorphism.
-/
lemma is_iso_of_fully_faithful (f : X ⟶ Y) [is_iso (F.map f)] : is_iso f :=
⟨⟨F.preimage (inv (F.map f)),
  ⟨F.map_injective (by simp), F.map_injective (by simp)⟩⟩⟩

/-- If `F` is fully faithful, we have an equivalence of hom-sets `X ⟶ Y` and `F X ⟶ F Y`. -/
def equiv_of_fully_faithful {X Y} : (X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y) :=
{ to_fun := λ f, F.map f,
  inv_fun := λ f, F.preimage f,
  left_inv := λ f, by simp,
  right_inv := λ f, by simp }

@[simp]
lemma equiv_of_fully_faithful_apply {X Y : C} (f : X ⟶ Y) :
  equiv_of_fully_faithful F f = F.map f := rfl
@[simp]
lemma equiv_of_fully_faithful_symm_apply {X Y} (f : F.obj X ⟶ F.obj Y) :
  (equiv_of_fully_faithful F).symm f = F.preimage f := rfl

end category_theory

namespace category_theory

variables {C : Type u₁} [category.{v₁} C]

instance full.id : full (𝟭 C) :=
{ preimage := λ _ _ f, f }

instance faithful.id : faithful (𝟭 C) := by obviously

variables {D : Type u₂} [category.{v₂} D] {E : Type u₃} [category.{v₃} E]
variables (F F' : C ⥤ D) (G : D ⥤ E)

instance faithful.comp [faithful F] [faithful G] : faithful (F ⋙ G) :=
{ map_injective' := λ _ _ _ _ p, F.map_injective (G.map_injective p) }

lemma faithful.of_comp [faithful $ F ⋙ G] : faithful F :=
{ map_injective' := λ X Y, (F ⋙ G).map_injective.of_comp }

section
variables {F F'}

/-- If `F` is full, and naturally isomorphic to some `F'`, then `F'` is also full. -/
def full.of_iso [full F] (α : F ≅ F') : full F' :=
{ preimage := λ X Y f, F.preimage ((α.app X).hom ≫ f ≫ (α.app Y).inv),
  witness' := λ X Y f, by simp [←nat_iso.naturality_1 α], }

lemma faithful.of_iso [faithful F] (α : F ≅ F') : faithful F' :=
{ map_injective' := λ X Y f f' h, F.map_injective
  (by rw [←nat_iso.naturality_1 α.symm, h, nat_iso.naturality_1 α.symm]) }
end

variables {F G}

lemma faithful.of_comp_iso {H : C ⥤ E} [ℋ : faithful H] (h : F ⋙ G ≅ H) : faithful F :=
@faithful.of_comp _ _ _ _ _ _ F G (faithful.of_iso h.symm)

alias faithful.of_comp_iso ← category_theory.iso.faithful_of_comp

-- We could prove this from `faithful.of_comp_iso` using `eq_to_iso`,
-- but that would introduce a cyclic import.
lemma faithful.of_comp_eq {H : C ⥤ E} [ℋ : faithful H] (h : F ⋙ G = H) : faithful F :=
@faithful.of_comp _ _ _ _ _ _ F G (h.symm ▸ ℋ)

alias faithful.of_comp_eq ← eq.faithful_of_comp

variables (F G)

/-- “Divide” a functor by a faithful functor. -/
protected def faithful.div (F : C ⥤ E) (G : D ⥤ E) [faithful G]
  (obj : C → D) (h_obj : ∀ X, G.obj (obj X) = F.obj X)
  (map : Π {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
  (h_map : ∀ {X Y} {f : X ⟶ Y}, G.map (map f) == F.map f) :
  C ⥤ D :=
{ obj := obj,
  map := @map,
  map_id' :=
  begin
    assume X,
    apply G.map_injective,
    apply eq_of_heq,
    transitivity F.map (𝟙 X), from h_map,
    rw [F.map_id, G.map_id, h_obj X]
  end,
  map_comp' :=
  begin
    assume X Y Z f g,
    apply G.map_injective,
    apply eq_of_heq,
    transitivity F.map (f ≫ g), from h_map,
    rw [F.map_comp, G.map_comp],
    congr' 1;
      try { exact (h_obj _).symm };
      exact h_map.symm
  end }

-- This follows immediately from `functor.hext` (`functor.hext h_obj @h_map`),
-- but importing `category_theory.eq_to_hom` causes an import loop:
-- category_theory.eq_to_hom → category_theory.opposites →
-- category_theory.equivalence → category_theory.fully_faithful
lemma faithful.div_comp (F : C ⥤ E) [faithful F] (G : D ⥤ E) [faithful G]
  (obj : C → D) (h_obj : ∀ X, G.obj (obj X) = F.obj X)
  (map : Π {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
  (h_map : ∀ {X Y} {f : X ⟶ Y}, G.map (map f) == F.map f) :
  (faithful.div F G obj @h_obj @map @h_map) ⋙ G = F :=
begin
  casesI F with F_obj _ _ _, casesI G with G_obj _ _ _,
  unfold faithful.div functor.comp,
  unfold_projs at h_obj,
  have: F_obj = G_obj ∘ obj := (funext h_obj).symm,
  substI this,
  congr,
  funext,
  exact eq_of_heq h_map
end

lemma faithful.div_faithful (F : C ⥤ E) [faithful F] (G : D ⥤ E) [faithful G]
  (obj : C → D) (h_obj : ∀ X, G.obj (obj X) = F.obj X)
  (map : Π {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
  (h_map : ∀ {X Y} {f : X ⟶ Y}, G.map (map f) == F.map f) :
  faithful (faithful.div F G obj @h_obj @map @h_map) :=
(faithful.div_comp F G _ h_obj _ @h_map).faithful_of_comp

instance full.comp [full F] [full G] : full (F ⋙ G) :=
{ preimage := λ _ _ f, F.preimage (G.preimage f) }

/-- If `F ⋙ G` is full and `G` is faithful, then `F` is full -/
def full.of_comp_faithful [full $ F ⋙ G] [faithful G] : full F :=
{ preimage := λ X Y f, (F ⋙ G).preimage (G.map f),
  witness' := λ X Y f, G.map_injective ((F ⋙ G).image_preimage _) }

/--
Given a natural isomorphism between `F ⋙ H` and `G ⋙ H` for a fully faithful functor `H`, we
can 'cancel' it to give a natural iso between `F` and `G`.
-/
def fully_faithful_cancel_right {F G : C ⥤ D} (H : D ⥤ E)
  [full H] [faithful H] (comp_iso: F ⋙ H ≅ G ⋙ H) : F ≅ G :=
nat_iso.of_components
  (λ X, preimage_iso (comp_iso.app X))
  (λ X Y f, H.map_injective (by simpa using comp_iso.hom.naturality f))

@[simp]
lemma fully_faithful_cancel_right_hom_app {F G : C ⥤ D} {H : D ⥤ E}
  [full H] [faithful H] (comp_iso: F ⋙ H ≅ G ⋙ H) (X : C) :
  (fully_faithful_cancel_right H comp_iso).hom.app X = H.preimage (comp_iso.hom.app X) :=
rfl

@[simp]
lemma fully_faithful_cancel_right_inv_app {F G : C ⥤ D} {H : D ⥤ E}
  [full H] [faithful H] (comp_iso: F ⋙ H ≅ G ⋙ H) (X : C) :
  (fully_faithful_cancel_right H comp_iso).inv.app X = H.preimage (comp_iso.inv.app X) :=
rfl

end category_theory
