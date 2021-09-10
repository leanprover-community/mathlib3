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

lemma has_finite_integral_to_real_of_lintegral_ne_top
  {μ : measure α} {f : α → ℝ≥0∞} (hf : ∫⁻ x, f x ∂μ ≠ ∞) :
  has_finite_integral (λ x, (f x).to_real) μ :=
begin
  have : ∀ x, (∥(f x).to_real∥₊ : ℝ≥0∞) =
    @coe ℝ≥0 ℝ≥0∞ _ (⟨(f x).to_real, ennreal.to_real_nonneg⟩ : ℝ≥0),
  { intro x, rw real.nnnorm_of_nonneg },
  simp_rw [has_finite_integral, this],
  refine lt_of_le_of_lt (lintegral_mono (λ x, _)) (lt_top_iff_ne_top.2 hf),
  by_cases hfx : f x = ∞,
  { simp [hfx] },
  { lift f x to ℝ≥0 using hfx with fx,
    simp [← h] }
end

lemma lintegral_radon_nikodym_deriv_lt_top
  (μ ν : measure α) [is_finite_measure μ] :
  ∫⁻ x, μ.radon_nikodym_deriv ν x ∂ν < ∞ :=
begin
  by_cases hl : have_lebesgue_decomposition μ ν,
  { haveI := hl,
    obtain ⟨-, -, hadd⟩ := have_lebesgue_decomposition_spec μ ν,
    rw [← set_lintegral_univ, ← with_density_apply _ measurable_set.univ],
    refine lt_of_le_of_lt
      (le_add_left (le_refl _) : _ ≤ μ.singular_part ν set.univ +
        ν.with_density (μ.radon_nikodym_deriv ν) set.univ) _,
    rw [← measure.add_apply, ← hadd],
    exact measure_lt_top _ _ },
  { erw [measure.radon_nikodym_deriv, dif_neg hl, lintegral_zero],
    exact with_top.zero_lt_top },
end

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

/-- The Radon-Nikodym derivative between a signed measure and a positive measure.

`radon_nikodym_deriv s μ` satisfies `μ.with_densityᵥ (s.radon_nikodym_deriv μ) = s`
if and only if `s` is absolutely continuous with respect to `μ` and this fact is known as
`measure_theory.signed_measure.absolutely_continuous_iff_with_density_radon_nikodym_deriv_eq`. -/
def radon_nikodym_deriv (s : signed_measure α) (μ : measure α) : α → ℝ := λ x,
(s.to_jordan_decomposition.pos_part.radon_nikodym_deriv μ x).to_real -
(s.to_jordan_decomposition.neg_part.radon_nikodym_deriv μ x).to_real

@[measurability]
lemma measurable_radon_nikodym_deriv (s : signed_measure α) (μ : measure α) :
  measurable (radon_nikodym_deriv s μ) :=
begin
  rw [radon_nikodym_deriv],
  measurability,
end

lemma integrable_radon_nikodym_deriv (s : signed_measure α) (μ : measure α) :
  integrable (radon_nikodym_deriv s μ) μ :=
begin
  refine integrable.sub _ _;
  { split, measurability,
    exact has_finite_integral_to_real_of_lintegral_ne_top
      (lintegral_radon_nikodym_deriv_lt_top _ μ).ne }
end

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
theorem absolutely_continuous_iff_with_density_radon_nikodym_deriv_eq
  (s : signed_measure α) (μ : measure α) [sigma_finite μ] :
  s ≪ μ.to_ennreal_vector_measure ↔
  μ.with_densityᵥ (s.radon_nikodym_deriv μ) = s :=
⟨with_densityᵥ_radon_nikodym_deriv_eq s μ,
 λ h, h ▸ with_densityᵥ_absolutely_continuous _ _⟩

end signed_measure

end measure_theory
