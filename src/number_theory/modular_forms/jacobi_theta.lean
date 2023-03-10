/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import analysis.complex.upper_half_plane.topology
import analysis.special_functions.gaussian

/-! # Jacobi's theta function

This file defines the Jacobi theta function

$$\theta(\tau) = \sum_{n \in \mathbb{Z}} \exp (i \pi n ^ 2 \tau),$$

and proves the modular transformation properties `θ (τ + 2) = θ τ` and
`θ (-1 / τ) = (-I * τ) ^ (1 / 2) * θ τ`, using Poisson's summation formula for the latter.
-/

open filter asymptotics function set complex (hiding abs_of_nonneg sq_abs) real (hiding exp)

open_locale real topology big_operators filter upper_half_plane

/-- Jacobi's theta function `∑' (n : ℤ), exp (π * I * n ^ 2 * τ)`. -/
noncomputable def jacobi_theta (τ : ℍ) : ℂ := ∑' (n : ℤ), cexp (π * I * n ^ 2 * τ)

lemma jacobi_theta_summable (τ : ℍ) : summable (λ n : ℤ, cexp (π * I * n ^ 2 * τ)) :=
begin
  rw ←summable_norm_iff,
  let y := rexp (-π * (τ : ℂ).im),
  have h : y < 1, from exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) τ.im_pos),
  have h' : ∀ (n : ℤ), ‖cexp (π * I * n ^ 2 * τ)‖ ≤ y ^ |n|,
  { intro n,
    have : |n| ≤ n ^ 2,
    { have : ((n.nat_abs) : ℤ) ≤ _, from nat.cast_le.mpr (n.nat_abs.le_mul_self),
      rwa [←int.abs_eq_nat_abs, ←pow_two, nat.cast_pow, int.nat_abs_sq] at this },
    replace : y ^ (n ^ 2) ≤ y ^ |n|,
    { rw [←inv_inv y, inv_zpow' _ (|n|), inv_zpow' _ (n ^ 2)],
      exact zpow_le_of_le (one_le_inv (exp_pos _) h.le) (neg_le_neg this) },
    refine (le_of_eq _).trans this,
    rw [complex.norm_eq_abs, complex.abs_exp],
    suffices : (↑π * I * n ^ 2 * τ).re = (-π * (τ : ℂ).im) * n ^ 2,
      by rw [this, exp_mul, ←int.cast_pow, rpow_int_cast],
    rw [(by { push_cast, ring } : ↑π * I * n ^ 2 * τ = ↑(π * n ^ 2) * (τ * I)),
      of_real_mul_re, mul_I_re],
    ring },
  refine summable_of_nonneg_of_le (λ n, norm_nonneg _) h' (summable_int_of_summable_nat _ _),
  { simp_rw [int.abs_coe_nat, zpow_coe_nat],
    exact summable_geometric_of_lt_1 (real.exp_pos _).le h },
  { simp_rw [abs_neg, int.abs_coe_nat, zpow_coe_nat],
    exact summable_geometric_of_lt_1 (real.exp_pos _).le h },
end

lemma jacobi_theta_two_vadd (τ : ℍ) : jacobi_theta ((2 : ℝ) +ᵥ τ) = jacobi_theta τ :=
begin
  refine tsum_congr (λ n, _),
  rw [upper_half_plane.coe_vadd, of_real_bit0, of_real_one],
  suffices : cexp (↑π * I * ↑n ^ 2 * 2) = 1, by rw [mul_add, complex.exp_add, this, one_mul],
  rw [(by { push_cast, ring } : ↑π * I * ↑n ^ 2 * 2 = ↑(n ^ 2) * (2 * π * I)),
    complex.exp_int_mul, complex.exp_two_pi_mul_I, one_zpow],
end

lemma jacobi_theta_T_sq_smul (τ : ℍ) :
  jacobi_theta (modular_group.T ^ 2 • τ) = jacobi_theta τ :=
begin
  rw [upper_half_plane.modular_T_pow_smul, nat.cast_two],
  exact jacobi_theta_two_vadd τ,
end

lemma jacobi_theta_S_smul (τ : ℍ) :
  jacobi_theta (modular_group.S • τ) = (-I * τ) ^ (1 / 2 : ℂ) * jacobi_theta τ :=
begin
  unfold jacobi_theta,
  rw [upper_half_plane.modular_S_smul, upper_half_plane.coe_mk],
  have ha : 0 < (-I * τ).re,
  { rw [neg_mul, neg_re, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, neg_neg],
    exact τ.im_pos },
  have ha' : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0,
  { rw [ne.def, cpow_eq_zero_iff],
    contrapose! ha,
    rw [ha.1, zero_re] },
  have hτ : (τ : ℂ) ≠ 0, from τ.ne_zero,
  have := complex.tsum_exp_neg_mul_int_sq ha,
  rw [mul_comm ((1:ℂ) / _) _, mul_one_div, eq_div_iff ha', mul_comm _ (_ ^ _), eq_comm] at this,
  convert this using 3,
  { ext1 n,
    congr' 1,
    field_simp [hτ, I_ne_zero],
    ring_nf,
    rw [I_sq, mul_neg, mul_one, neg_mul, neg_neg] },
  { ext1 n,
    congr' 1,
    ring_nf }
end
