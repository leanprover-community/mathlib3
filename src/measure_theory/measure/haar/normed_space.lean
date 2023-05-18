/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Sébastien Gouëzel
-/
import measure_theory.measure.lebesgue.eq_haar
import measure_theory.integral.bochner

/-!
# Basic properties of Haar measures on real vector spaces

-/

open measure finite_dimensional

namespace measure_theory
namespace measure

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [measurable_space E]
  [borel_space E] [finite_dimensional ℝ E] (μ : measure E) [is_add_haar_measure μ]
  {F : Type*} [normed_add_comm_group F] [normed_space ℝ F] [complete_space F]

variables (μ) {s : set E}

/-- The integral of `f (R • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
lemma integral_comp_smul (f : E → F) (R : ℝ) :
  ∫ x, f (R • x) ∂μ = |(R ^ finrank ℝ E)⁻¹| • ∫ x, f x ∂μ :=
begin
  rcases eq_or_ne R 0 with rfl|hR,
  { simp only [zero_smul, integral_const],
    rcases nat.eq_zero_or_pos (finrank ℝ E) with hE|hE,
    { haveI : subsingleton E, from finrank_zero_iff.1 hE,
      have : f = (λ x, f 0), { ext x, rw subsingleton.elim x 0 },
      conv_rhs { rw this },
      simp only [hE, pow_zero, inv_one, abs_one, one_smul, integral_const] },
    { haveI : nontrivial E, from finrank_pos_iff.1 hE,
      simp only [zero_pow hE, measure_univ_of_is_add_left_invariant, ennreal.top_to_real, zero_smul,
        inv_zero, abs_zero]} },
  { calc ∫ x, f (R • x) ∂μ = ∫ y, f y ∂(measure.map (λ x, R • x) μ) :
      (integral_map_equiv (homeomorph.smul (is_unit_iff_ne_zero.2 hR).unit)
        .to_measurable_equiv f).symm
    ... = |(R ^ finrank ℝ E)⁻¹| • ∫ x, f x ∂μ :
      by simp only [map_add_haar_smul μ hR, integral_smul_measure, ennreal.to_real_of_real,
                    abs_nonneg] }
end

/-- The integral of `f (R • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
lemma integral_comp_smul_of_nonneg (f : E → F) (R : ℝ) {hR : 0 ≤ R} :
  ∫ x, f (R • x) ∂μ = (R ^ finrank ℝ E)⁻¹ • ∫ x, f x ∂μ :=
by rw [integral_comp_smul μ f R, abs_of_nonneg (inv_nonneg.2 (pow_nonneg hR _))]

/-- The integral of `f (R⁻¹ • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
lemma integral_comp_inv_smul (f : E → F) (R : ℝ) :
  ∫ x, f (R⁻¹ • x) ∂μ = |(R ^ finrank ℝ E)| • ∫ x, f x ∂μ :=
by rw [integral_comp_smul μ f (R⁻¹), inv_pow, inv_inv]

/-- The integral of `f (R⁻¹ • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
lemma integral_comp_inv_smul_of_nonneg (f : E → F) {R : ℝ} (hR : 0 ≤ R) :
  ∫ x, f (R⁻¹ • x) ∂μ = R ^ finrank ℝ E • ∫ x, f x ∂μ :=
by rw [integral_comp_inv_smul μ f R, abs_of_nonneg ((pow_nonneg hR _))]

end measure
end measure_theory
