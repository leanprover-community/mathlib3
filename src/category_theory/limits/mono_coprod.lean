/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.limits.shapes.regular_mono
import category_theory.limits.shapes.zero_morphisms

/-!

# Categories where inclusions into coproducts are monomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If `C` is a category, the class `mono_coprod C` expresses that left
inclusions `A ⟶ A ⨿ B` are monomorphisms when `has_coproduct A B`
is satisfied. If it is so, it is shown that right inclusions are
also monomorphisms.

TODO @joelriou: show that if `X : I → C` and `ι : J → I` is an injective map,
then the canonical morphism `∐ (X ∘ ι) ⟶ ∐ X` is a monomorphism.

TODO: define distributive categories, and show that they satisfy `mono_coprod`, see
<https://ncatlab.org/toddtrimble/published/distributivity+implies+monicity+of+coproduct+inclusions>

-/

noncomputable theory

open category_theory category_theory.category category_theory.limits

universe u

namespace category_theory

namespace limits

variables (C : Type*) [category C]

/-- This condition expresses that inclusion morphisms into coproducts are monomorphisms. -/
class mono_coprod : Prop :=
(binary_cofan_inl : ∀ ⦃A B : C⦄ (c : binary_cofan A B) (hc : is_colimit c), mono c.inl)

variable {C}

@[priority 100]
instance mono_coprod_of_has_zero_morphisms
  [has_zero_morphisms C] : mono_coprod C :=
⟨λ A B c hc, begin
  haveI : is_split_mono c.inl := is_split_mono.mk'
    (split_mono.mk (hc.desc (binary_cofan.mk (𝟙 A) 0)) (is_colimit.fac _ _ _)),
  apply_instance,
end⟩

namespace mono_coprod

lemma binary_cofan_inr {A B : C}[mono_coprod C] (c : binary_cofan A B) (hc : is_colimit c) :
  mono c.inr :=
begin
  have hc' : is_colimit (binary_cofan.mk c.inr c.inl) :=
    binary_cofan.is_colimit_mk (λ s, hc.desc (binary_cofan.mk s.inr s.inl)) (by tidy) (by tidy)
    (λ s m h₁ h₂, binary_cofan.is_colimit.hom_ext hc
      (by simp only [h₂, is_colimit.fac, binary_cofan.ι_app_left, binary_cofan.mk_inl])
      (by simp only [h₁, is_colimit.fac, binary_cofan.ι_app_right, binary_cofan.mk_inr])),
  exact binary_cofan_inl _ hc',
end

instance {A B : C} [mono_coprod C] [has_binary_coproduct A B] :
  mono (coprod.inl : A ⟶ A ⨿ B) :=
binary_cofan_inl _ (colimit.is_colimit _)

instance {A B : C} [mono_coprod C] [has_binary_coproduct A B] :
  mono (coprod.inr : B ⟶ A ⨿ B) :=
binary_cofan_inr _ (colimit.is_colimit _)

lemma mono_inl_iff {A B : C} {c₁ c₂ : binary_cofan A B} (hc₁ : is_colimit c₁)
  (hc₂ : is_colimit c₂) : mono c₁.inl ↔ mono c₂.inl :=
begin
  suffices : ∀ (c₁ c₂ : binary_cofan A B) (hc₁ : is_colimit c₁) (hc₂ : is_colimit c₂)
    (h : mono c₁.inl), mono c₂.inl,
  { exact ⟨λ h₁, this _ _ hc₁ hc₂ h₁, λ h₂, this _ _ hc₂ hc₁ h₂⟩, },
  intros c₁ c₂ hc₁ hc₂,
  introI,
  simpa only [is_colimit.comp_cocone_point_unique_up_to_iso_hom]
    using mono_comp c₁.inl (hc₁.cocone_point_unique_up_to_iso hc₂).hom,
end

lemma mk' (h : ∀ (A B : C), ∃ (c : binary_cofan A B) (hc : is_colimit c), mono c.inl) :
  mono_coprod C :=
⟨λ A B c' hc', begin
  obtain ⟨c, hc₁, hc₂⟩ := h A B,
  simpa only [mono_inl_iff hc' hc₁] using hc₂,
end⟩

instance mono_coprod_type : mono_coprod (Type u) :=
mono_coprod.mk' (λ A B, begin
  refine ⟨binary_cofan.mk (sum.inl : A ⟶ A ⊕ B) sum.inr, _, _⟩,
  { refine binary_cofan.is_colimit.mk _ (λ Y f₁ f₂ x, by { cases x, exacts [f₁ x, f₂ x], })
      (λ Y f₁ f₂, rfl) (λ Y f₁ f₂, rfl) _,
    intros Y f₁ f₂ m h₁ h₂,
    ext x,
    cases x,
    { dsimp, exact congr_fun h₁ x, },
    { dsimp, exact congr_fun h₂ x, }, },
  { rw mono_iff_injective,
    intros a₁ a₂ h,
    simp only [binary_cofan.mk_inl] at h,
    dsimp at h,
    simpa only using h, },
end)

end mono_coprod

end limits

end category_theory
