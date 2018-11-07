-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton

import category_theory.limits

universes u v

open category_theory
open category_theory.limits

namespace category_theory.limits.types

variables {J : Type u} [small_category J]

def limit (F : J ⥤ Type u) : cone F :=
{ X := {u : Π j, F j // ∀ (j j' : J) (f : j ⟶ j'), F.map f (u j) = u j'},
  π := { app := λ j u, u.val j } }

attribute [extensionality] subtype.eq

def limit_is_limit (F : J ⥤ Type u) : is_limit (limit F) :=
{ lift := λ s v, ⟨λ j, s.π j v, λ j j' f, congr_fun (@cone.w _ _ _ _ _ s j j' f) _⟩,
  uniq' :=
  begin
    tidy,
    have h := congr_fun (w x_1) x,
    exact h
  end }

instance : has_limits.{u+1 u} (Type u) :=
{ cone := @limit, is_limit := @limit_is_limit }

@[simp] lemma types_limit (F : J ⥤ Type u) :
  limits.limit F = {u : Π j, F j // ∀ j j' f, F.map f (u j) = u j'} := rfl
@[simp] lemma types_limit_π (F : J ⥤ Type u) (j : J) (g : (limit F).X) :
  limit.π F j g = g.val j := rfl.
@[simp] lemma types_limit_pre (F : J ⥤ Type u) {K : Type u} [𝒦 : small_category K] (E : K ⥤ J) (g : (limit F).X) :
  limit.pre F E g = (⟨ λ k, g.val (E k), by obviously ⟩ : (limit (E ⋙ F)).X) := rfl
@[simp] lemma types_limit_map {F G : J ⥤ Type u} (α : F ⟹ G) (g : (limit F).X) :
  (lim.map α : (limit F).X → (limit G).X) g =
  (⟨ λ j, (α j) (g.val j), λ j j' f,
     by rw [←functor_to_types.naturality, ←(g.property j j' f)] ⟩ : (limit G).X) :=
rfl

@[simp] lemma types_limit_lift (F : J ⥤ Type u) (c : cone F) (x : c.X):
  limit.lift F c x = (⟨ λ j, c.π j x, λ j j' f, congr_fun (cone.w c f) x ⟩ : (limit F).X) := rfl

def colimit (F : J ⥤ Type u) : cocone F :=
{ X := @quot (Σ j, F j) (λ p p', ∃ f : p.1 ⟶ p'.1, p'.2 = F.map f p.2),
  ι :=
  { app := λ j x, quot.mk _ ⟨j, x⟩,
    naturality' := λ j j' f, funext $ λ x, eq.symm (quot.sound ⟨f, rfl⟩) } }

local attribute [elab_with_expected_type] quot.lift

def colimit_is_colimit (F : J ⥤ Type u) : is_colimit (colimit F) :=
{ desc := λ s, quot.lift (λ (p : Σ j, F j), s.ι p.1 p.2)
  (assume ⟨j, x⟩ ⟨j', x'⟩ ⟨f, hf⟩, by rw hf; exact (congr_fun (cocone.w s f) x).symm),
  fac' := begin tidy end,
  uniq' := begin tidy end }

instance : has_colimits.{u+1 u} (Type u) :=
{ cocone := @colimit, is_colimit := @colimit_is_colimit }

@[simp] lemma types_colimit (F : J ⥤ Type u) :
  limits.colimit F = @quot (Σ j, F j) (λ p p', ∃ f : p.1 ⟶ p'.1, p'.2 = F.map f p.2) := rfl
@[simp] lemma types_colimit_ι (F : J ⥤ Type u) (j : J) : colimit.ι F j = λ x, quot.mk _ (⟨j, x⟩ : (Σ j, F j)) := rfl.

local attribute [extensionality] quot.sound

@[simp] lemma types_colimit_map {F G : J ⥤ Type u} (α : F ⟹ G) :
  (colim.map α : (colimit F).X → (colimit G).X) =
  (quot.lift
    (λ p : Σ (j : J), F j, quot.mk _ ⟨ p.1, (α p.1) p.2 ⟩ )
    (λ p p' r, begin tidy, exact r_w, rw r_h, rw functor_to_types.naturality, end)) := rfl

-- -- TODO remaining lemmas:
-- @[simp] lemma types_colimit_pre
--   (F : J ⥤ Type u) {K : Type u} [𝒦 : small_category K] (E : K ⥤ J) (g : (colimit (E ⋙ F)).X) :
--   colimit.pre F E g = sorry := sorry
-- -- What are you meant to do here? Split into cases depending on whether ∃ j : J, then use choice?
-- @[simp] lemma types_colimit_desc (F : J ⥤ Type u) (c : cocone F) :
--   colimit.desc F c = λ x, sorry := sorry

instance : has_terminal.{u+1 u} (Type u) :=
{ terminal := punit }
instance : has_initial.{u+1 u} (Type u) :=
{ initial := pempty }

open category_theory.limits.walking_cospan
open category_theory.limits.walking_cospan_hom

def pullback {Y₁ Y₂ Z : Type u} (r₁ : Y₁ ⟶ Z) (r₂ : Y₂ ⟶ Z) : cone (cospan r₁ r₂) :=
{ X := { z : Y₁ × Y₂ // r₁ z.1 = r₂ z.2 },
  π :=
  { app := λ j z,
      match j with
      | left  := z.val.1
      | right := z.val.2
      | one   := r₁ z.val.1
      end,
    naturality' := λ j j' f, funext $
      match j, j', f with
      | _, _, (id _) := by tidy
      | _, _, inl := by tidy
      | _, _, inr := λ x, begin dsimp [cospan], erw ← x.property, refl end
      end } }

instance : has_pullbacks.{u+1 u} (Type u) :=
{ square := λ Y₁ Y₂ Z r₁ r₂, pullback r₁ r₂,
  is_pullback := λ Y₁ Y₂ Z r₁ r₂,
  { lift  := λ s x, ⟨ (s.π left x, s.π right x),
    begin
      have swl := congr_fun (@cone.w _ _ _ _ _ s left one inl) x,
      have swr := congr_fun (@cone.w _ _ _ _ _ s right one inr) x,
      exact eq.trans swl (eq.symm swr),
    end ⟩,
    fac' := λ s j, funext $ λ x,
    begin
      cases j, refl, refl,
      exact congr_fun (s.w inl) x,
    end,
    uniq' := λ s m w,
    begin
      tidy,
      exact congr_fun (w left) x,
      exact congr_fun (w right) x,
    end }, }

-- TODO should we provide 'hand-rolled' instances, like those above? probably!

instance : has_products.{u+1 u} (Type u) := has_products_of_has_limits
instance : has_equalizers.{u+1 u} (Type u) := has_equalizers_of_has_limits

instance : has_coproducts.{u+1 u} (Type u) := has_coproducts_of_has_colimits
instance : has_coequalizers.{u+1 u} (Type u) := has_coequalizers_of_has_colimits
instance : has_pushouts.{u+1 u} (Type u) := has_pushouts_of_has_colimits

end category_theory.limits.types
