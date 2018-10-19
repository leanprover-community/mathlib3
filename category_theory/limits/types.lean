-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton

import category_theory.limits

universes u v

open category_theory
open category_theory.limits

namespace category_theory.universal.types

variables {J : Type u} [𝒥 : small_category J]
include 𝒥

def limit (F : J ⥤ Type u) : cone F :=
{ X := {u : Π j, F j // ∀ (j j' : J) (f : j ⟶ j'), F.map f (u j) = u j'},
  π := λ j u, u.val j }

attribute [extensionality] subtype.eq

def limit_is_limit (F : J ⥤ Type u) : is_limit (limit F) :=
{ lift := λ s v, ⟨λ j, s.π j v, λ j j' f, congr_fun (s.w f) _⟩,
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
  limit.lift F c x = (⟨ λ j, c.π j x, λ j j' f, congr_fun (c.w f) x ⟩ : (limit F).X) := rfl

def colimit (F : J ⥤ Type u) : cocone F :=
{ X := @quot (Σ j, F j) (λ p p', ∃ f : p.1 ⟶ p'.1, p'.2 = F.map f p.2),
  ι := λ j x, quot.mk _ ⟨j, x⟩,
  w' := λ j j' f, funext $ λ x, eq.symm (quot.sound ⟨f, rfl⟩) }

local attribute [elab_with_expected_type] quot.lift

def colimit_is_colimit (F : J ⥤ Type u) : is_colimit (colimit F) :=
{ desc := λ s, quot.lift (λ (p : Σ j, F j), s.ι p.1 p.2)
  (assume ⟨j, x⟩ ⟨j', x'⟩ ⟨f, hf⟩, by rw hf; exact (congr_fun (s.w f) x).symm) }

instance : has_colimits.{u+1 u} (Type u) :=
{ cocone := @colimit, is_colimit := @colimit_is_colimit }

@[simp] lemma types_colimit (F : J ⥤ Type u) :
  limits.colimit F = @quot (Σ j, F j) (λ p p', ∃ f : p.1 ⟶ p'.1, p'.2 = F.map f p.2) := rfl
@[simp] lemma types_colimit_ι (F : J ⥤ Type u) (j : J) : colimit.ι F j = λ x, quot.mk _ (⟨j, x⟩ : (Σ j, F j)) := rfl.
-- TODO remaining lemmas:
@[simp] lemma types_colimit_pre
  (F : J ⥤ Type u) {K : Type u} [𝒦 : small_category K] (E : K ⥤ J) (g : (colimit (E ⋙ F)).X) :
  colimit.pre F E g = sorry := sorry
@[simp] lemma types_colimit_map {F G : J ⥤ Type u} (α : F ⟹ G) :
  (colim.map α : (colimit F).X → (colimit G).X) =
  (quot.lift
    (λ p : Σ (j : J), F j, quot.mk _ ⟨ p.1, (α p.1) p.2 ⟩ )
    (λ p p' r, begin tidy, end)) := sorry
-- @[simp] lemma types_colimit_lift (F : J ⥤ Type u) (c : cocone F) (x : c.X) :
--   colimit.desc F c x = sorry := sorry
#print quot.lift
end category_theory.universal.types
