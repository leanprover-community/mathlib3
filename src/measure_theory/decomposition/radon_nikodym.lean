/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.decomposition.lebesgue

/-!
# Radon-Nikodym theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves the Radon-Nikodym theorem. The Radon-Nikodym theorem states that, given measures
`μ, ν`, if `have_lebesgue_decomposition μ ν`, then `μ` is absolutely continuous with respect to
`ν` if and only if there exists a measurable function `f : α → ℝ≥0∞` such that `μ = fν`.
In particular, we have `f = rn_deriv μ ν`.

The Radon-Nikodym theorem will allow us to define many important concepts in probability theory,
most notably probability cumulative functions. It could also be used to define the conditional
expectation of a real function, but we take a different approach (see the file
`measure_theory/function/conditional_expectation`).

## Main results

* `measure_theory.measure.absolutely_continuous_iff_with_density_rn_deriv_eq` :
  the Radon-Nikodym theorem
* `measure_theory.signed_measure.absolutely_continuous_iff_with_density_rn_deriv_eq` :
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

lemma with_density_rn_deriv_eq
  (μ ν : measure α) [have_lebesgue_decomposition μ ν] (h : μ ≪ ν) :
  ν.with_density (rn_deriv μ ν) = μ :=
begin
  obtain ⟨hf₁, ⟨E, hE₁, hE₂, hE₃⟩, hadd⟩:= have_lebesgue_decomposition_spec μ ν,
  have : singular_part μ ν = 0,
  { refine le_antisymm (λ A hA, _) (measure.zero_le _),
    suffices : singular_part μ ν set.univ = 0,
    { rw [measure.coe_zero, pi.zero_apply, ← this],
      exact measure_mono (set.subset_univ _) },
    rw [← measure_add_measure_compl hE₁, hE₂, zero_add],
    have : (singular_part μ ν + ν.with_density (rn_deriv μ ν)) Eᶜ = μ Eᶜ,
    { rw ← hadd },
    rw [measure.coe_add, pi.add_apply, h hE₃] at this,
    exact (add_eq_zero_iff.1 this).1 },
  rw [this, zero_add] at hadd,
  exact hadd.symm
end

/-- **The Radon-Nikodym theorem**: Given two measures `μ` and `ν`, if
`have_lebesgue_decomposition μ ν`, then `μ` is absolutely continuous to `ν` if and only if
`ν.with_density (rn_deriv μ ν) = μ`. -/
theorem absolutely_continuous_iff_with_density_rn_deriv_eq
  {μ ν : measure α} [have_lebesgue_decomposition μ ν] :
  μ ≪ ν ↔ ν.with_density (rn_deriv μ ν) = μ :=
⟨with_density_rn_deriv_eq μ ν, λ h, h ▸ with_density_absolutely_continuous _ _⟩

lemma with_density_rn_deriv_to_real_eq {μ ν : measure α} [is_finite_measure μ]
  [have_lebesgue_decomposition μ ν] (h : μ ≪ ν) {i : set α} (hi : measurable_set i) :
  ∫ x in i, (μ.rn_deriv ν x).to_real ∂ν = (μ i).to_real :=
begin
  rw [integral_to_real, ← with_density_apply _ hi,
      with_density_rn_deriv_eq μ ν h],
  { measurability },
  { refine ae_lt_top (μ.measurable_rn_deriv ν)
      (lt_of_le_of_lt (lintegral_mono_set i.subset_univ) _).ne,
    rw [← with_density_apply _ measurable_set.univ,
        with_density_rn_deriv_eq μ ν h],
    exact measure_lt_top _ _ },
end

end measure

namespace signed_measure

include m

open measure vector_measure

theorem with_densityᵥ_rn_deriv_eq
  (s : signed_measure α) (μ : measure α) [sigma_finite μ]
  (h : s ≪ᵥ μ.to_ennreal_vector_measure) :
  μ.with_densityᵥ (s.rn_deriv μ) = s :=
begin
  rw [absolutely_continuous_ennreal_iff,
      (_ : μ.to_ennreal_vector_measure.ennreal_to_measure = μ),
      total_variation_absolutely_continuous_iff] at h,
  { ext1 i hi,
    rw [with_densityᵥ_apply (integrable_rn_deriv _ _) hi,
        rn_deriv, integral_sub,
        with_density_rn_deriv_to_real_eq h.1 hi,
        with_density_rn_deriv_to_real_eq h.2 hi],
    { conv_rhs { rw ← s.to_signed_measure_to_jordan_decomposition },
      erw vector_measure.sub_apply,
      rw [to_signed_measure_apply_measurable hi, to_signed_measure_apply_measurable hi] },
    all_goals { rw ← integrable_on_univ,
      refine integrable_on.restrict _ measurable_set.univ,
      refine ⟨_, has_finite_integral_to_real_of_lintegral_ne_top _⟩,
      { apply measurable.ae_strongly_measurable,
        measurability },
      { rw set_lintegral_univ,
        exact (lintegral_rn_deriv_lt_top _ _).ne } } },
  { exact equiv_measure.right_inv μ }
end

/-- The Radon-Nikodym theorem for signed measures. -/
theorem absolutely_continuous_iff_with_densityᵥ_rn_deriv_eq
  (s : signed_measure α) (μ : measure α) [sigma_finite μ] :
  s ≪ᵥ μ.to_ennreal_vector_measure ↔
  μ.with_densityᵥ (s.rn_deriv μ) = s :=
⟨with_densityᵥ_rn_deriv_eq s μ,
 λ h, h ▸ with_densityᵥ_absolutely_continuous _ _⟩

end signed_measure

end measure_theory
