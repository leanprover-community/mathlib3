/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.decomposition.lebesgue
import measure_theory.measure.with_density_vector_measure

/-!
# Radon-Nikodym theorem

This file proves the Radon-Nikodym theorem. The Radon-Nikodym theorem states that, given measures
`μ, ν`, if `have_lebesgue_decomposition μ ν`, then `μ` is absolutely continuous with respect to
`ν` if and only if there exists a measurable function `f : α → ℝ≥0∞` such that `μ = fν`.
In particular, we have `f = radon_nikodym_deriv μ ν`.

The Radon-Nikodym theorem will allow us to define many important concepts in probability theory,
most notably conditional expectations and probability cumulative functions.

## Main results

* `measure_theory.measure.absolutely_continuous_iff_with_density_radon_nikodym_deriv_eq` :
  the Radon-Nikodym theorem
* `measure_theory.signed_measure.absolutely_continuous_iff_with_density_radon_nikodym_deriv_eq` :
  the Radon-Nikodym theorem for signed measures

## Tags

Radon-Nikodym theorem
-/

noncomputable theory
open_locale classical measure_theory nnreal ennreal

variables {α β : Type*} {m : measurable_space α}

namespace measure_theory

namespace measure

include m

lemma with_density_radon_nikodym_deriv_eq
  (μ ν : measure α) [have_lebesgue_decomposition μ ν] (h : μ ≪ ν) :
  ν.with_density (radon_nikodym_deriv μ ν) = μ :=
begin
  obtain ⟨hf₁, ⟨E, hE₁, hE₂, hE₃⟩, hadd⟩:= have_lebesgue_decomposition_spec μ ν,
  have : singular_part μ ν = 0,
  { refine le_antisymm (λ A hA, _) (measure.zero_le _),
    suffices : singular_part μ ν set.univ = 0,
    { rw [measure.coe_zero, pi.zero_apply, ← this],
      exact measure_mono (set.subset_univ _) },
    rw [← set.union_compl_self E, measure_union (@disjoint_compl_right _ E _) hE₁ hE₁.compl,
        hE₂, zero_add],
    have : (singular_part μ ν + ν.with_density (radon_nikodym_deriv μ ν)) Eᶜ = μ Eᶜ,
    { rw ← hadd },
    rw [measure.coe_add, pi.add_apply, h hE₃] at this,
    exact (add_eq_zero_iff.1 this).1 },
  rw [this, zero_add] at hadd,
  exact hadd.symm
end

/-- **The Radon-Nikodym theorem**: Given two measures `μ` and `ν`, if
`have_lebesgue_decomposition μ ν`, then `μ` is absolutely continuous to `ν` if and only if
`ν.with_density (radon_nikodym_deriv μ ν) = μ`. -/
theorem absolutely_continuous_iff_with_density_radon_nikodym_deriv_eq
  {μ ν : measure α} [have_lebesgue_decomposition μ ν] :
  μ ≪ ν ↔ ν.with_density (radon_nikodym_deriv μ ν) = μ :=
⟨with_density_radon_nikodym_deriv_eq μ ν, λ h, h ▸ with_density_absolutely_continuous _ _⟩

lemma with_density_radon_nikodym_deriv_to_real_eq {μ ν : measure α} [is_finite_measure μ]
  [have_lebesgue_decomposition μ ν] (h : μ ≪ ν) {i : set α} (hi : measurable_set i) :
  ∫ x in i, (μ.radon_nikodym_deriv ν x).to_real ∂ν = (μ i).to_real :=
begin
  rw [integral_to_real, ← with_density_apply _ hi,
      with_density_radon_nikodym_deriv_eq μ ν h],
  { measurability },
  { refine ae_lt_top (μ.measurable_radon_nikodym_deriv ν)
      (lt_of_le_of_lt (lintegral_mono_set i.subset_univ) _),
    rw [← with_density_apply _ measurable_set.univ,
        with_density_radon_nikodym_deriv_eq μ ν h],
    exact measure_lt_top _ _ },
end

end measure

namespace signed_measure

include m

open measure vector_measure

theorem with_densityᵥ_radon_nikodym_deriv_eq
  (s : signed_measure α) (μ : measure α) [sigma_finite μ]
  (h : s ≪ μ.to_ennreal_vector_measure) :
  μ.with_densityᵥ (s.radon_nikodym_deriv μ) = s :=
begin
  rw [absolutely_continuous_ennreal_iff,
      (_ : μ.to_ennreal_vector_measure.ennreal_to_measure = μ),
      total_variation_absolutely_continuous_iff] at h,
  { ext1 i hi,
    rw [with_densityᵥ_apply (integrable_radon_nikodym_deriv _ _) hi,
        radon_nikodym_deriv, integral_sub,
        with_density_radon_nikodym_deriv_to_real_eq h.1 hi,
        with_density_radon_nikodym_deriv_to_real_eq h.2 hi],
    { conv_rhs { rw ← s.to_signed_measure_to_jordan_decomposition },
      erw vector_measure.sub_apply,
      rw [to_signed_measure_apply_measurable hi, to_signed_measure_apply_measurable hi] },
    all_goals { rw ← integrable_on_univ,
      refine integrable_on.restrict _ measurable_set.univ,
      refine ⟨_, has_finite_integral_to_real_of_lintegral_ne_top _⟩,
      { measurability },
      { rw set_lintegral_univ,
        exact (lintegral_radon_nikodym_deriv_lt_top _ _).ne } } },
  { exact equiv_measure.right_inv μ }
end

/-- The Radon-Nikodym theorem for signed measures. -/
theorem absolutely_continuous_iff_with_densityᵥ_radon_nikodym_deriv_eq
  (s : signed_measure α) (μ : measure α) [sigma_finite μ] :
  s ≪ μ.to_ennreal_vector_measure ↔
  μ.with_densityᵥ (s.radon_nikodym_deriv μ) = s :=
⟨with_densityᵥ_radon_nikodym_deriv_eq s μ,
 λ h, h ▸ with_densityᵥ_absolutely_continuous _ _⟩

lemma radon_nikodym_deriv_neg (s : signed_measure α) (μ : measure α) [sigma_finite μ]
  (hs : s ≪ μ.to_ennreal_vector_measure) :
  (-s).radon_nikodym_deriv μ =ᵐ[μ] - s.radon_nikodym_deriv μ :=
begin
  refine integrable.ae_eq_of_with_densityᵥ_eq
    (integrable_radon_nikodym_deriv _ _) (integrable_radon_nikodym_deriv _ _).neg _,
  rw [with_densityᵥ_neg, with_densityᵥ_radon_nikodym_deriv_eq s μ hs,
      with_densityᵥ_radon_nikodym_deriv_eq _ _ hs.neg_left]
end

lemma radon_nikodym_deriv_add (s t : signed_measure α) (μ : measure α) [sigma_finite μ]
  (hs : s ≪ μ.to_ennreal_vector_measure) (ht : t ≪ μ.to_ennreal_vector_measure) :
  (s + t).radon_nikodym_deriv μ =ᵐ[μ] s.radon_nikodym_deriv μ + t.radon_nikodym_deriv μ :=
begin
  refine integrable.ae_eq_of_with_densityᵥ_eq
    (integrable_radon_nikodym_deriv _ _)
    ((integrable_radon_nikodym_deriv _ _).add (integrable_radon_nikodym_deriv _ _)) _,
  rw [with_densityᵥ_radon_nikodym_deriv_eq _ _ (hs.add ht),
      with_densityᵥ_add
        (integrable_radon_nikodym_deriv _ _) (integrable_radon_nikodym_deriv _ _),
      with_densityᵥ_radon_nikodym_deriv_eq s μ hs,
      with_densityᵥ_radon_nikodym_deriv_eq t μ ht]
end

lemma radon_nikodym_deriv_sub (s t : signed_measure α) (μ : measure α) [sigma_finite μ]
  (hs : s ≪ μ.to_ennreal_vector_measure) (ht : t ≪ μ.to_ennreal_vector_measure) :
  (s - t).radon_nikodym_deriv μ =ᵐ[μ] s.radon_nikodym_deriv μ - t.radon_nikodym_deriv μ :=
begin
  refine integrable.ae_eq_of_with_densityᵥ_eq
    (integrable_radon_nikodym_deriv _ _)
    ((integrable_radon_nikodym_deriv _ _).sub (integrable_radon_nikodym_deriv _ _)) _,
  rw [with_densityᵥ_radon_nikodym_deriv_eq _ _ (hs.sub ht),
      with_densityᵥ_sub
        (integrable_radon_nikodym_deriv _ _) (integrable_radon_nikodym_deriv _ _),
      with_densityᵥ_radon_nikodym_deriv_eq s μ hs,
      with_densityᵥ_radon_nikodym_deriv_eq t μ ht]
end

lemma radon_nikodym_deriv_smul (s : signed_measure α) (μ : measure α) [sigma_finite μ]
  (r : ℝ) (hs : s ≪ μ.to_ennreal_vector_measure) :
  (r • s).radon_nikodym_deriv μ =ᵐ[μ] r • s.radon_nikodym_deriv μ :=
begin
  refine integrable.ae_eq_of_with_densityᵥ_eq
    (integrable_radon_nikodym_deriv _ _) ((integrable_radon_nikodym_deriv _ _).smul r) _,
  rw [@with_densityᵥ_smul _ _ μ _ _ _ _ _ _ _ (s.radon_nikodym_deriv μ) _ _ _ _ _ _ r,
      with_densityᵥ_radon_nikodym_deriv_eq _ _ hs,
      with_densityᵥ_radon_nikodym_deriv_eq _ _ hs.smul],
end

end signed_measure

end measure_theory
