/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import analysis.complex.upper_half_plane.basic
import analysis.special_functions.gaussian

/-! # Jacobi's theta function

This file defines the Jacobi theta function

$$\theta(\tau) = \sum_{n \in \mathbb{Z}} \exp (i \pi n ^ 2 \tau),$$

and proves the modular transformation properties `θ (τ + 2) = θ τ` and
`θ (-1 / τ) = (-I * τ) ^ (1 / 2) * θ τ`, using Poisson's summation formula for the latter.
-/

open complex real

open_locale real big_operators upper_half_plane

/-- Jacobi's theta function `∑' (n : ℤ), exp (π * I * n ^ 2 * τ)`. -/
noncomputable def jacobi_theta (τ : ℍ) : ℂ := ∑' (n : ℤ), cexp (π * I * n ^ 2 * τ)

lemma jacobi_theta_unif_summable {R : ℝ} (hR : 0 < R) :
  ∃ (bd : ℤ → ℝ), (summable bd) ∧
  (∀ {τ : ℍ} (hτ : R ≤ τ.im) (n : ℤ), ‖cexp (π * I * n ^ 2 * τ)‖ ≤ bd n) :=
begin
  let y := rexp (-π * R),
  have h : y < 1, from exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hR),
  refine ⟨λ n, y ^ |n|, summable_int_of_summable_nat _ _, λ τ hτ n, _⟩, swap 3,
  { refine le_trans _ (_ : y ^ (n ^ 2) ≤ y ^ |n|),
    { rw [complex.norm_eq_abs, complex.abs_exp],
      have : (↑π * I * n ^ 2 * τ).re = (-π * (τ : ℂ).im) * n ^ 2,
      { rw [(by { push_cast, ring } : ↑π * I * n ^ 2 * τ = ↑(π * n ^ 2) * (τ * I)),
          of_real_mul_re, mul_I_re],
        ring },
      obtain ⟨m, hm⟩ := int.eq_coe_of_zero_le (sq_nonneg n),
      rw [this, exp_mul, ←int.cast_pow, rpow_int_cast, hm, zpow_coe_nat, zpow_coe_nat],
      refine pow_le_pow_of_le_left (exp_pos _).le (real.exp_le_exp.mpr _) _,
      rwa [mul_le_mul_left_of_neg (neg_lt_zero.mpr pi_pos), upper_half_plane.coe_im] },
    { rw [←inv_inv y, inv_zpow' _ (|n|), inv_zpow' _ (n ^ 2)],
      refine zpow_le_of_le (one_le_inv (exp_pos _) h.le) (neg_le_neg _),
      rw [int.abs_eq_nat_abs, ←int.nat_abs_sq, ←nat.cast_pow, nat.cast_le, sq],
      exact n.nat_abs.le_mul_self } },
  all_goals { simp only [abs_neg, int.abs_coe_nat, zpow_coe_nat],
    exact summable_geometric_of_lt_1 (real.exp_pos _).le h },
end

lemma jacobi_theta_summable (τ : ℍ) : summable (λ n : ℤ, cexp (π * I * n ^ 2 * τ)) :=
let ⟨bd, h, h'⟩ := jacobi_theta_unif_summable τ.im_pos in
  summable_norm_iff.mp (summable_of_nonneg_of_le (λ n, norm_nonneg _) (h' $ le_refl _) h)

lemma jacobi_theta_two_vadd (τ : ℍ) : jacobi_theta ((2 : ℝ) +ᵥ τ) = jacobi_theta τ :=
begin
  refine tsum_congr (λ n, _),
  rw [upper_half_plane.coe_vadd, of_real_bit0, of_real_one],
  suffices : cexp (↑π * I * ↑n ^ 2 * 2) = 1, by rw [mul_add, complex.exp_add, this, one_mul],
  rw [(by { push_cast, ring } : ↑π * I * ↑n ^ 2 * 2 = ↑(n ^ 2) * (2 * π * I)),
    complex.exp_int_mul, complex.exp_two_pi_mul_I, one_zpow],
end

lemma jacobi_theta_T_sq_smul (τ : ℍ) : jacobi_theta (modular_group.T ^ 2 • τ) = jacobi_theta τ :=
begin
  suffices : (2 : ℝ) +ᵥ τ = modular_group.T ^ (2 : ℤ) • τ, from this ▸ (jacobi_theta_two_vadd τ),
  rw [←subtype.coe_inj, upper_half_plane.coe_vadd, upper_half_plane.special_linear_group_apply,
    upper_half_plane.coe_mk, modular_group.coe_T_zpow, add_comm],
  simp only [of_real_bit0, matrix.of_apply, matrix.cons_val_zero, algebra_map.coe_one, one_mul,
    matrix.cons_val_one, matrix.head_cons, int.cast_bit0, algebra_map.coe_zero, zero_mul, zero_add,
    div_one],
end

--by simpa only [upper_half_plane.modular_T_pow_smul, nat.cast_two] using jacobi_theta_two_vadd τ

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
