/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import analysis.fourier.add_circle
import analysis.fourier.fourier_transform

/-!
# Poisson's summation formula

We prove Poisson's summation formula `∑ (n : ℤ), f n = ∑ (n : ℤ), 𝓕 f n`, where `𝓕 f` is the
Fourier transform of `f`, under the following hypotheses:
* `f` is a continuous function `ℝ → ℂ`.
* The sum `∑ (n : ℤ), 𝓕 f n` is convergent.
* For all compacts `K ⊂ ℝ`, the sum `∑ (n : ℤ), sup { ‖f(x + n)‖ | x ∈ K }` is convergent.

## TODO

* Show that the conditions on `f` are automatically satisfied for Schwartz functions.
-/

noncomputable theory

open function (hiding comp_apply) complex real set (hiding restrict_apply)
  topological_space filter measure_theory

open_locale real big_operators filter fourier_transform

local attribute [instance] real.fact_zero_lt_one

open continuous_map

/-- The key lemma for Poisson summation: the `m`-th Fourier coefficient of the periodic function
`∑' n : ℤ, f (x + n)` is the value at `m` of the Fourier transform of `f`. -/
lemma real.fourier_coeff_tsum_comp_add {f : C(ℝ, ℂ)}
  (hf : ∀ (K : compacts ℝ), summable (λ n : ℤ, ‖(f.comp (continuous_map.add_right n)).restrict K‖))
  (m : ℤ) :
  fourier_coeff (periodic.lift $ f.periodic_tsum_comp_add_zsmul 1) m = 𝓕 f m :=
begin
  -- NB: This proof can be shortened somewhat by telescoping together some of the steps in the calc
  -- block, but I think it's more legible this way. We start with preliminaries about the integrand.
  let e : C(ℝ, ℂ) := (fourier (-m)).comp ⟨(coe : ℝ → unit_add_circle), continuous_quotient_mk⟩,
  have neK : ∀ (K : compacts ℝ) (g : C(ℝ, ℂ)), ‖(e * g).restrict K‖ = ‖g.restrict K‖,
  { have : ∀ (x : ℝ), ‖e x‖ = 1, from λ x, abs_coe_circle _,
    intros K g,
    simp_rw [norm_eq_supr_norm, restrict_apply, mul_apply, norm_mul, this, one_mul] },
  have eadd : ∀ (n : ℤ), e.comp (continuous_map.add_right n) = e,
  { intro n, ext1 x,
    have : periodic e 1, from periodic.comp (λ x, add_circle.coe_add_period 1 x) _,
    simpa only [mul_one] using this.int_mul n x },
  -- Now the main argument. First unwind some definitions.
  calc fourier_coeff (periodic.lift $ f.periodic_tsum_comp_add_zsmul 1) m
  = ∫ x in 0..1, e x * (∑' n : ℤ, f.comp (continuous_map.add_right n)) x :
    by simp_rw [fourier_coeff_eq_interval_integral _ m 0, div_one, one_smul, zero_add, comp_apply,
      coe_mk, periodic.lift_coe, zsmul_one, smul_eq_mul]
  -- Transform sum in C(ℝ, ℂ) evaluated at x into pointwise sum of values.
  ... = ∫ x in 0..1, (∑' n : ℤ, (e * f.comp (continuous_map.add_right n)) x) :
    by simp_rw [coe_mul, pi.mul_apply, ←tsum_apply (summable_of_locally_summable_norm hf),
      tsum_mul_left]
  -- Swap sum and integral.
  ... = ∑' n : ℤ, ∫ x in 0..1, (e * f.comp (continuous_map.add_right n)) x :
    begin
      refine (interval_integral.tsum_interval_integral_eq_of_summable_norm _).symm,
      convert hf ⟨uIcc 0 1, is_compact_uIcc⟩,
      exact funext (λ n, neK _ _)
    end
  ... = ∑' n : ℤ, ∫ x in 0..1, (e * f).comp (continuous_map.add_right n) x :
    begin
      simp only [continuous_map.comp_apply, mul_comp] at eadd ⊢,
      simp_rw eadd,
    end
  -- Rearrange sum of interval integrals into an integral over `ℝ`.
  ... = ∫ x, e x * f x :
    begin
      suffices : integrable ⇑(e * f), from this.has_sum_interval_integral_comp_add_int.tsum_eq,
      apply integrable_of_summable_norm_Icc,
      convert hf ⟨Icc 0 1, is_compact_Icc⟩,
      simp_rw [continuous_map.comp_apply, mul_comp] at eadd ⊢,
      simp_rw eadd,
      exact funext (λ n, neK ⟨Icc 0 1, is_compact_Icc⟩ _),
    end
  -- Minor tidying to finish
  ... = 𝓕 f m :
    begin
      rw fourier_integral_eq_integral_exp_smul,
      congr' 1 with x : 1,
      rw [smul_eq_mul, comp_apply, coe_mk, fourier_coe_apply],
      congr' 2,
      push_cast,
      ring
    end
end

/-- **Poisson's summation formula**. -/
theorem real.tsum_eq_tsum_fourier_integral {f : C(ℝ, ℂ)}
  (h_norm : ∀ (K : compacts ℝ),
    summable (λ n : ℤ, ‖(f.comp $ continuous_map.add_right n).restrict K‖))
  (h_sum : summable (λ n : ℤ, 𝓕 f n)) :
  ∑' (n : ℤ), f n = ∑' (n : ℤ), 𝓕 f n :=
begin
  let F : C(unit_add_circle, ℂ) := ⟨(f.periodic_tsum_comp_add_zsmul 1).lift,
    continuous_coinduced_dom.mpr (map_continuous _)⟩,
  have : summable (fourier_coeff F),
  { convert h_sum,
    exact funext (λ n, real.fourier_coeff_tsum_comp_add h_norm n) },
  convert (has_pointwise_sum_fourier_series_of_summable this 0).tsum_eq.symm using 1,
  { have := (has_sum_apply (summable_of_locally_summable_norm h_norm).has_sum 0).tsum_eq,
    simpa only [coe_mk, ←quotient_add_group.coe_zero, periodic.lift_coe, zsmul_one, comp_apply,
      coe_add_right, zero_add] using this },
  { congr' 1 with n : 1,
    rw [←real.fourier_coeff_tsum_comp_add h_norm n, fourier_eval_zero, smul_eq_mul, mul_one],
    refl },
end
