import algebra.homology.short_complex.short_exact
import category_theory.abelian.pseudoelements

namespace category_theory

open limits

variables {C : Type*} [category C] [abelian C] {S : short_complex C}

lemma abelian.pseudo_surjective_of_epi'
  {A X Y : C} (f : X ⟶ Y) [epi f] (y : A ⟶ Y) :
  ∃ (A' : C) (π : A' ⟶ A) (hπ : epi π) (x : A' ⟶ X), π ≫ y = x ≫ f :=
⟨pullback f y, pullback.snd, infer_instance, pullback.fst, pullback.condition.symm⟩

namespace short_complex

lemma exact.pseudo_exact' (h : S.exact) {A : C} (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0) :
  ∃ (A' : C) (π : A' ⟶ A) (hπ : epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f :=
begin
  haveI := h,
  refine ⟨pullback (S.lift_cycles _ hx₂) S.to_cycles, pullback.fst, _, pullback.snd, _⟩,
  { rw short_complex.exact_iff_epi_to_cycles at h,
    haveI := h,
    apply_instance, },
  { simp only [← S.to_cycles_i, ← pullback.condition_assoc, lift_cycles_i], },
end

variable (S)

lemma exact_iff_pseudo_exact' : S.exact ↔
  ∀ ⦃A : C⦄ (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0),
  ∃ (A' : C) (π : A' ⟶ A) (hπ : epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f :=
begin
  split,
  { exact λ h A, h.pseudo_exact', },
  { exact exact.of_pseudo_exact' _, },
end

open_locale pseudoelement

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

end short_complex

end category_theory
