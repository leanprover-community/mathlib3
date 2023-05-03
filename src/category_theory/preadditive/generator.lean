/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.generator
import category_theory.preadditive.yoneda.basic

/-!
# Separators in preadditive categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains characterizations of separating sets and objects that are valid in all
preadditive categories.

-/

universes v u

open category_theory opposite

namespace category_theory
variables {C : Type u} [category.{v} C] [preadditive C]

lemma preadditive.is_separating_iff (𝒢 : set C) :
  is_separating 𝒢 ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ (G ∈ 𝒢) (h : G ⟶ X), h ≫ f = 0) → f = 0 :=
⟨λ h𝒢 X Y f hf, h𝒢 _ _ (by simpa only [limits.comp_zero] using hf),
 λ h𝒢 X Y f g hfg, sub_eq_zero.1 $ h𝒢 _
  (by simpa only [preadditive.comp_sub, sub_eq_zero] using hfg)⟩

lemma preadditive.is_coseparating_iff (𝒢 : set C) :
  is_coseparating 𝒢 ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ (G ∈ 𝒢) (h : Y ⟶ G), f ≫ h = 0) → f = 0 :=
⟨λ h𝒢 X Y f hf, h𝒢 _ _ (by simpa only [limits.zero_comp] using hf),
 λ h𝒢 X Y f g hfg, sub_eq_zero.1 $ h𝒢 _
  (by simpa only [preadditive.sub_comp, sub_eq_zero] using hfg)⟩

lemma preadditive.is_separator_iff (G : C) :
  is_separator G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : G ⟶ X, h ≫ f = 0) → f = 0 :=
⟨λ hG X Y f hf, hG.def _ _ (by simpa only [limits.comp_zero] using hf),
 λ hG, (is_separator_def _).2 $ λ X Y f g hfg, sub_eq_zero.1 $ hG _
  (by simpa only [preadditive.comp_sub, sub_eq_zero] using hfg)⟩

lemma preadditive.is_coseparator_iff (G : C) :
  is_coseparator G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : Y ⟶ G, f ≫ h = 0) → f = 0 :=
⟨λ hG X Y f hf, hG.def _ _ (by simpa only [limits.zero_comp] using hf),
 λ hG, (is_coseparator_def _).2 $ λ X Y f g hfg, sub_eq_zero.1 $ hG _
  (by simpa only [preadditive.sub_comp, sub_eq_zero] using hfg)⟩

lemma is_separator_iff_faithful_preadditive_coyoneda (G : C) :
  is_separator G ↔ faithful (preadditive_coyoneda.obj (op G)) :=
begin
  rw [is_separator_iff_faithful_coyoneda_obj, ← whiskering_preadditive_coyoneda, functor.comp_obj,
    whiskering_right_obj_obj],
  exact ⟨λ h, by exactI faithful.of_comp _ (forget AddCommGroup), λ h, by exactI faithful.comp _ _⟩
end

lemma is_separator_iff_faithful_preadditive_coyoneda_obj (G : C) :
  is_separator G ↔ faithful (preadditive_coyoneda_obj (op G)) :=
begin
  rw [is_separator_iff_faithful_preadditive_coyoneda, preadditive_coyoneda_obj_2],
  exact ⟨λ h, by exactI faithful.of_comp _ (forget₂ _ AddCommGroup.{v}),
         λ h, by exactI faithful.comp _ _⟩
end

lemma is_coseparator_iff_faithful_preadditive_yoneda (G : C) :
  is_coseparator G ↔ faithful (preadditive_yoneda.obj G) :=
begin
  rw [is_coseparator_iff_faithful_yoneda_obj, ← whiskering_preadditive_yoneda, functor.comp_obj,
    whiskering_right_obj_obj],
  exact ⟨λ h, by exactI faithful.of_comp _ (forget AddCommGroup), λ h, by exactI faithful.comp _ _⟩
end

lemma is_coseparator_iff_faithful_preadditive_yoneda_obj (G : C) :
  is_coseparator G ↔ faithful (preadditive_yoneda_obj G) :=
begin
  rw [is_coseparator_iff_faithful_preadditive_yoneda, preadditive_yoneda_obj_2],
  exact ⟨λ h, by exactI faithful.of_comp _ (forget₂ _ AddCommGroup.{v}),
         λ h, by exactI faithful.comp _ _⟩
end

end category_theory
