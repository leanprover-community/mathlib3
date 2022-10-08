/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.limits.types
import category_theory.morphism_property

/-!

# Categories where inclusions into coproducts are monomorphisms

If `C` is a category that has finite coproducts, the class `mono_coprod C`
expresses that left inclusions `A ⟶ A ⨿ B` are monomorphisms. If it is so,
it is shown that right inclusions are also monomorphisms.

TODO @joelriou: show that if `X : I → C` and `ι : J → I` is an injective map,
then the canonical morphism `∐ (X ∘ ι) ⟶ ∐ X` is a monomorphism.

-/

noncomputable theory

open category_theory category_theory.category category_theory.limits

universe u

namespace category_theory

namespace limits

variables (C : Type*) [category C] [hC : has_finite_coproducts C]

include hC

/-- This condition expresses that inclusion morphisms into coproducts are monomorphisms. -/
class mono_coprod : Prop :=
(inl : Π (A B : C), mono (coprod.inl : A ⟶ A ⨿ B))

variable {C}

@[priority 100]
instance mono_coprod_of_has_zero_morphisms
  [has_zero_morphisms C] : mono_coprod C :=
⟨λ A B, infer_instance⟩

omit hC

lemma mono_sigma_ι_iff_of_is_colimit {J : Type*} (X : J → C) [has_coproduct X]
  (c : cocone (discrete.functor X)) (hc : is_colimit c) (j : J) :
  mono (sigma.ι X j) ↔ mono (c.ι.app (discrete.mk j)) :=
(morphism_property.respects_iso.monomorphisms C).arrow_iso_iff
  (arrow.iso_mk' (sigma.ι X j) (c.ι.app (discrete.mk j)) (iso.refl _)
    (colimit.iso_colimit_cocone ⟨c, hc⟩) (by simp))

include hC

lemma mono_coprod_inl_iff_of_is_colimit {A B : C} (c : binary_cofan A B) (hc : is_colimit c) :
  mono (coprod.inl : A ⟶ A ⨿ B) ↔ mono c.inl :=
mono_sigma_ι_iff_of_is_colimit (pair_function A B) c hc walking_pair.left

lemma mono_coprod_inr_iff_of_is_colimit {A B : C} (c : binary_cofan A B) (hc : is_colimit c) :
  mono (coprod.inr : B ⟶ A ⨿ B) ↔ mono c.inr :=
mono_sigma_ι_iff_of_is_colimit (pair_function A B) c hc walking_pair.right

omit hC

instance mono_coprod_type : mono_coprod (Type u) :=
⟨λ A B, begin
  let c : binary_cofan A B := binary_cofan.mk (sum.inl : A ⟶ A ⊕ B) sum.inr,
  have hc : is_colimit c :=
  { desc := λ (s : binary_cofan A B) x, by { cases x, exacts [s.inl x, s.inr x], },
    fac' := λ s j, by { discrete_cases, cases j; refl, },
    uniq' := λ (s : binary_cofan A B) m hm, begin
      ext x,
      cases x,
      { dsimp, exact congr_fun (hm (discrete.mk walking_pair.left)) x, },
      { dsimp, exact congr_fun (hm (discrete.mk walking_pair.right)) x, },
    end },
  rw [mono_coprod_inl_iff_of_is_colimit c hc, mono_iff_injective],
  intros a₁ a₂ h,
  simp only [binary_cofan.mk_inl] at h,
  dsimp at h,
  simpa only using h,
end⟩

namespace mono_coprod

include hC

instance [mono_coprod C] {A B : C} : mono (coprod.inl : A ⟶ A ⨿ B) := mono_coprod.inl A B

instance [mono_coprod C] {A B : C} : mono (coprod.inr : B ⟶ A ⨿ B) :=
begin
  suffices : mono (coprod.inl ≫ (coprod.braiding B A).hom),
  { simpa only [coprod.braiding_hom, coprod.inl_desc] using this, },
  apply mono_comp,
end

lemma mono_binary_cofan_inl [mono_coprod C] {A B : C} (c : binary_cofan A B)
  (hc : is_colimit c) : mono c.inl :=
by { rw ← mono_coprod_inl_iff_of_is_colimit c hc, apply_instance, }

lemma mono_binary_cofan_inr [mono_coprod C] {A B : C} (c : binary_cofan A B)
  (hc : is_colimit c) : mono c.inr :=
by { rw ← mono_coprod_inr_iff_of_is_colimit c hc, apply_instance, }

end mono_coprod

end limits

end category_theory
