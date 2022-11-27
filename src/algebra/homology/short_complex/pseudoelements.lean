import algebra.homology.short_complex.short_exact
import category_theory.abelian.pseudoelements

open category_theory

variables {C : Type*} [category C] [abelian C] (S : short_complex C)

open_locale pseudoelement

namespace short_complex

lemma exact_iff_pseudo_exact : S.exact ↔
  (∀ b, S.g b = 0 → ∃ a, S.f a = b) :=
begin
  have eq : S.exact ↔ category_theory.exact S.f S.g,
  { rw exact_iff_exact_short_complex _ _ S.zero,
    cases S,
    refl, },
  rw eq,
  split,
  { intro h,
    exact (abelian.pseudoelement.pseudo_exact_of_exact h).2, },
  { intro h,
    refine abelian.pseudoelement.exact_of_pseudo_exact S.f S.g _,
    split,
    { intro a,
      rw [← abelian.pseudoelement.comp_apply, S.zero,
        abelian.pseudoelement.zero_apply], },
    { exact h}, }
end

variable {S}

lemma exact.pseudo_exact (h : S.exact) (b) (hb : S.g b = 0) :
  ∃ a, S.f a = b :=
begin
  rw exact_iff_pseudo_exact at h,
  exact h b hb,
end


lemma exact.pseudo_exact' (h : S.exact) {A : C} (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0) :
  ∃ (A' : C) (π : A' ⟶ A) (hπ : epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f := sorry

end short_complex
