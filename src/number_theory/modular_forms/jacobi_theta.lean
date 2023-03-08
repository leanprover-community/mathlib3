/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import analysis.fourier.poisson_summation
import analysis.schwartz_space
import analysis.p_series
import analysis.special_functions.gaussian

/-! # Jacobi's theta function

This file defines the Jacobi theta function

$$\theta(\tau) = \sum_{n \in \mathbb{Z}} \exp (i \pi n ^ 2 \tau),$$

and proves the modular transformation properties `θ (τ + 2) = θ τ` and
`θ (-1 / τ) = (-I * τ) ^ (1 / 2) * θ τ`, using Poisson's summation formula for the latter.
-/

open filter asymptotics function set complex (hiding abs_of_nonneg sq_abs) real (hiding exp)

open_locale real topology big_operators filter fourier_transform

/-- Jacobi's theta function `∑' (n : ℤ), exp (π * I * n ^ 2 * τ)`. -/
noncomputable def jacobi_theta (τ : ℂ) : ℂ := ∑' (n : ℤ), cexp (π * I * n ^ 2 * τ)

lemma jacobi_theta_add_two : periodic jacobi_theta 2 :=
begin
  refine λ τ, tsum_congr (λ n, _),
  suffices : cexp (↑π * I * ↑n ^ 2 * 2) = 1, by rw [mul_add, complex.exp_add, this, mul_one],
  rw [(by { push_cast, ring } : ↑π * I * ↑n ^ 2 * 2 = ↑(n ^ 2) * (2 * π * I)),
    complex.exp_int_mul, complex.exp_two_pi_mul_I, one_zpow],
end

lemma jacobi_theta_neg_one_div {τ : ℂ} (hτ : 0 < τ.im) :
  jacobi_theta (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * jacobi_theta τ :=
begin
  have ha : 0 < (-I * τ).re,
    by rwa [neg_mul, neg_re, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, neg_neg],
  have ha' : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0,
  { rw [ne.def, cpow_eq_zero_iff],
    contrapose! ha,
    rw [ha.1, zero_re] },
  have hτ : τ ≠ 0, by { contrapose! hτ, rw [hτ, zero_im] },
  have := tsum_exp_neg_mul_int_sq ha,
  rw [mul_comm ((1:ℂ) / _) _, mul_one_div, eq_div_iff ha', mul_comm _ (_ ^ _), eq_comm] at this,
  convert this using 2,
  { refine tsum_congr (λ n, congr_arg _ _),
    field_simp [hτ, I_ne_zero],
    ring_nf,
    rw [I_sq, mul_neg, mul_one, neg_mul] },
  { exact tsum_congr (λ n, congr_arg _ (by ring_nf)) }
end
