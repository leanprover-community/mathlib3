/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import measure_theory.integral.exp_decay

/-!
# The Gamma function

This file treats Euler's integral for the `Γ` function, `∫ x in Ioi 0, exp (-x) * x ^ (s - 1)`, for
`s` a real or complex variable.

We prove convergence of the integral for `1 ≤ s` in the real case, and `1 ≤ re s` in the complex
case (which is non-optimal, but the optimal bound of `0 < s`, resp `0 < re s`, is harder to prove
using the methods in the library). We also show `Γ(1) = 1`.

The recurrence `Γ(s + 1) = s * Γ(s)`, holomorphy in `s`, and extension to the whole complex plane
will be added in future pull requests.

## Tags

gamma
-/

noncomputable theory
open filter interval_integral set real measure_theory
open_locale topological_space

section gamma_real

/-- Asymptotic bound for the Γ function integrand. -/
lemma gamma_integrand_is_O (s : ℝ) : asymptotics.is_O (λ x:ℝ, exp (-x) * x ^ s)
  (λ x:ℝ, exp (-(1/2) * x)) at_top :=
begin
  refine asymptotics.is_o.is_O (asymptotics.is_o_of_tendsto _ _),
  { intros x hx, exfalso, exact (exp_pos (-(1 / 2) * x)).ne' hx },
  have : (λ (x:ℝ), exp (-x) * x ^ s / exp (-(1 / 2) * x)) = (λ (x:ℝ), exp ((1 / 2) * x) / x ^ s )⁻¹,
  { ext1 x, dsimp,
    have : exp (-x) = exp (-(1 / 2) * x) * exp (-(1 / 2) * x),
    { rw ←real.exp_add, field_simp },
    rw this,
    have : exp (1 / 2 * x) = (exp (-(1 / 2) * x))⁻¹ := by { rw ←exp_neg, field_simp, },
    rw this,
    field_simp [(exp_pos (-x/2)).ne'], ring },
  rw this,
  exact (tendsto_exp_mul_div_rpow_at_top s (1 / 2) one_half_pos).inv_tendsto_at_top,
end

/-- Euler's integral for the `Γ` function (of a real variable `s`), defined as
`∫ x in Ioi 0, exp (-x) * x ^ (s - 1)`.

See `gamma_real_integral_convergent` for a proof of the convergence of the integral for `1 ≤ s`. -/
def gamma_real_integral (s : ℝ) : ℝ := ∫ x in Ioi (0:ℝ), exp (-x) * x ^ (s - 1)

/-- The integral defining the Γ function converges for real `s` with `1 ≤ s`.

This is not optimal, but the optimal bound (convergence for `0 < s`) is hard to establish with the
results currently in the library. -/
lemma gamma_real_integral_convergent {s : ℝ} (h : 1 ≤ s) : integrable_on
  (λ x:ℝ, exp (-x) * x ^ (s - 1)) (Ioi 0) :=
begin
  refine integrable_of_is_O_exp_neg one_half_pos _ (gamma_integrand_is_O _ ),
  refine continuous_on_id.neg.exp.mul (continuous_on_id.rpow_const _),
  intros x hx, right, simpa only [sub_nonneg] using h,
end

/- Most of this is just showing `∫ x in Ioi 0, exp (-x) = 1` -- maybe this should go elsewhere? -/
lemma gamma_real_integral_one : gamma_real_integral 1 = 1 :=
begin
  have : ∫ (x : ℝ) in Ioi 0, exp (-x) * x ^ (0:ℝ) = ∫ (x : ℝ) in Ioi 0, exp (-x),
  { congr, ext1, rw [rpow_zero, mul_one], },
  rw [gamma_real_integral, sub_self, this],
  have t1: tendsto (λ X:ℝ, ∫ x in 0..X, exp (-x)) at_top (𝓝 1),
  { simp only [integral_comp_neg, neg_zero, integral_exp, real.exp_zero],
    simpa only [sub_zero] using tendsto_exp_neg_at_top_nhds_0.const_sub 1, },
  refine tendsto_nhds_unique (interval_integral_tendsto_integral_Ioi _ _ tendsto_id) t1,
  simpa only [neg_mul, one_mul] using exp_neg_integrable_on_Ioi 0 zero_lt_one,
end

end gamma_real

section gamma_complex

open complex

lemma abs_cpow_of_pos_real (s : ℂ) {x : ℝ} (hx : 0 < x) : complex.abs (x ^ s)  = x ^ (s.re) :=
begin
  rw cpow_def_of_ne_zero,
  { rw [complex.abs_exp, ←of_real_log hx.le, of_real_mul_re, exp_mul, exp_log hx],},
  { rwa [ne.def, of_real_eq_zero, ←ne.def], exact hx.ne',}
end

/-- The integral defining the Γ function converges for complex `s` with `1 ≤ re s`.

This is proved by reduction to the real case. The bound is not optimal, but the optimal bound
(convergence for `0 < re s`) is hard to establish with the results currently in the library. -/
lemma gamma_complex_integral_convergent {s : ℂ} (hs : 1 ≤ s.re) :
  integrable_on (λ x:ℝ, real.exp (-x) * x ^ (s - 1) : ℝ → ℂ) (Ioi 0) :=
begin
  -- This is slightly subtle if `s` is non-real but `s.re = 1`, as the integrand is not continuous
  -- at the lower endpoint. However, it is continuous on the interior, and its norm is continuous
  -- at the endpoint, which is good enough.
  split,
  { refine continuous_on.ae_measurable _ measurable_set_Ioi,
    apply (continuous_of_real.comp continuous_neg.exp).continuous_on.mul,
    apply continuous_at.continuous_on,
    intros x hx,
    have : continuous_at (λ x:ℂ, x ^ (s - 1)) ↑x,
    { apply continuous_at_cpow_const, rw of_real_re, exact or.inl hx, },
    exact continuous_at.comp this continuous_of_real.continuous_at },
  { rw ←has_finite_integral_norm_iff,
    refine has_finite_integral.congr (gamma_real_integral_convergent hs).2 _,
    refine (ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ (λ x hx, _)),
    dsimp only,
    rw [complex.norm_eq_abs, complex.abs_mul, complex.abs_of_nonneg $ le_of_lt $ exp_pos $ -x,
      abs_cpow_of_pos_real _ hx],
    simp }
end

/-- Euler's integral for the `Γ` function (of a complex variable `s`), defined as
`∫ x in Ioi 0, exp (-x) * x ^ (s - 1)`.

See `gamma_complex_integral_convergent` for a proof of the convergence of the integral for
`1 ≤ re s`. -/
def gamma_complex_integral (s : ℂ) : ℂ := ∫ x in Ioi (0:ℝ), ↑(exp (-x)) * ↑x ^ (s - 1)

lemma gamma_complex_integral_of_real (s : ℝ) :
  gamma_complex_integral ↑s = ↑(gamma_real_integral s) :=
begin
  rw [gamma_real_integral, ←integral_of_real],
  refine set_integral_congr measurable_set_Ioi _,
  intros x hx, dsimp only,
  rw [of_real_mul, of_real_cpow (mem_Ioi.mp hx).le],
  simp,
end

lemma gamma_complex_integral_one : gamma_complex_integral 1 = 1 :=
begin
  rw [←of_real_one, gamma_complex_integral_of_real 1, of_real_inj],
  exact gamma_real_integral_one,
end

end gamma_complex
