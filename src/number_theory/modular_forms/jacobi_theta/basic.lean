/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import analysis.special_functions.gaussian
import analysis.complex.locally_uniform_limit
import analysis.complex.upper_half_plane.functions_bounded_at_infty
import analysis.complex.upper_half_plane.topology

/-! # Jacobi's theta function

This file defines the Jacobi theta function

$$\theta(\tau) = \sum_{n \in \mathbb{Z}} \exp (i \pi n ^ 2 \tau),$$

and proves the modular transformation properties `θ (τ + 2) = θ τ` and
`θ (-1 / τ) = (-I * τ) ^ (1 / 2) * θ τ`, using Poisson's summation formula for the latter. We also
show that `θ` is differentiable on `ℍ`, and `θ(τ) - 1` has exponential decay as `im τ → ∞`.
-/

open complex real asymptotics filter
open_locale real big_operators upper_half_plane

/-- Jacobi's theta function `∑' (n : ℤ), exp (π * I * n ^ 2 * τ)`. -/
noncomputable def jacobi_theta (z : ℂ) : ℂ := ∑' (n : ℤ), cexp (π * I * n ^ 2 * z)

lemma norm_exp_mul_sq_le {z : ℂ} (hz : 0 < z.im) (n : ℤ) :
  ‖cexp (π * I * n ^ 2 * z)‖ ≤ exp (-π * z.im) ^ n.nat_abs :=
begin
  let y := rexp (-π * z.im),
  have h : y < 1, from exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hz),
  refine (le_of_eq _).trans (_ : y ^ (n ^ 2) ≤ _),
  { rw [complex.norm_eq_abs, complex.abs_exp],
    have : (↑π * I * n ^ 2 * z).re = (-π * z.im) * n ^ 2,
    { rw [(by { push_cast, ring } : ↑π * I * n ^ 2 * z = ↑(π * n ^ 2) * (z * I)),
        of_real_mul_re, mul_I_re],
      ring },
    obtain ⟨m, hm⟩ := int.eq_coe_of_zero_le (sq_nonneg n),
    rw [this, exp_mul, ←int.cast_pow, rpow_int_cast, hm, zpow_coe_nat] },
  { have : n ^ 2 = ↑(n.nat_abs ^ 2), by rw [nat.cast_pow, int.nat_abs_sq],
    rw [this, zpow_coe_nat],
    exact pow_le_pow_of_le_one (exp_pos _).le h.le ((sq n.nat_abs).symm ▸ n.nat_abs.le_mul_self) },
end

lemma exists_summable_bound_exp_mul_sq {R : ℝ} (hR : 0 < R) :
  ∃ (bd : ℤ → ℝ), (summable bd) ∧
  (∀ {τ : ℂ} (hτ : R ≤ τ.im) (n : ℤ), ‖cexp (π * I * n ^ 2 * τ)‖ ≤ bd n) :=
begin
  let y := rexp (-π * R),
  have h : y < 1, from exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hR),
  refine ⟨λ n, y ^ n.nat_abs, summable_int_of_summable_nat _ _, λ τ hτ n, _⟩, swap 3,
  { refine (norm_exp_mul_sq_le (hR.trans_le hτ) n).trans _,
    refine pow_le_pow_of_le_left (exp_pos _).le (real.exp_le_exp.mpr _) _,
    rwa [mul_le_mul_left_of_neg (neg_lt_zero.mpr pi_pos)] },
  all_goals { simpa only [int.nat_abs_neg, int.nat_abs_of_nat]
    using summable_geometric_of_lt_1 (real.exp_pos _).le h },
end

lemma summable_exp_mul_sq {z : ℂ} (hz : 0 < z.im) :
  summable (λ n : ℤ, cexp (π * I * n ^ 2 * z)) :=
let ⟨bd, h, h'⟩ := exists_summable_bound_exp_mul_sq hz in
  summable_norm_iff.mp (summable_of_nonneg_of_le (λ n, norm_nonneg _) (h' $ le_refl _) h)

lemma jacobi_theta_two_add (z : ℂ) : jacobi_theta (2 + z) = jacobi_theta z :=
begin
  refine tsum_congr (λ n, _),
  suffices : cexp (↑π * I * ↑n ^ 2 * 2) = 1, by rw [mul_add, complex.exp_add, this, one_mul],
  rw [(by { push_cast, ring } : ↑π * I * ↑n ^ 2 * 2 = ↑(n ^ 2) * (2 * π * I)),
    complex.exp_int_mul, complex.exp_two_pi_mul_I, one_zpow],
end

lemma jacobi_theta_T_sq_smul (τ : ℍ) :
  jacobi_theta ↑(modular_group.T ^ 2 • τ) = jacobi_theta τ :=
begin
  suffices : ↑(modular_group.T ^ 2 • τ) = (2 : ℂ) + ↑τ,
  { simp_rw [this, jacobi_theta_two_add] },
  have : modular_group.T ^ (2 : ℕ) = modular_group.T ^ (2 : ℤ), by refl,
  simp_rw [this, upper_half_plane.modular_T_zpow_smul, upper_half_plane.coe_vadd],
  push_cast,
end

lemma jacobi_theta_S_smul (τ : ℍ) :
  jacobi_theta ↑(modular_group.S • τ) = (-I * τ) ^ (1 / 2 : ℂ) * jacobi_theta τ :=
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

lemma has_sum_nat_jacobi_theta {z : ℂ} (hz : 0 < im z) :
  has_sum (λ (n : ℕ), cexp (π * I * (n + 1) ^ 2 * z)) ((jacobi_theta z - 1) / 2) :=
begin
  have := (summable_exp_mul_sq hz).has_sum.sum_nat_of_sum_int,
  rw ←@has_sum_nat_add_iff' ℂ _ _ _ _ 1 at this,
  simp_rw [finset.sum_range_one, int.cast_neg, int.cast_coe_nat, nat.cast_zero, neg_zero,
    int.cast_zero, sq (0:ℂ), mul_zero, zero_mul, neg_sq, ←mul_two, complex.exp_zero,
    add_sub_assoc, (by norm_num : (1 : ℂ) - 1 * 2 = -1), ←sub_eq_add_neg,
    nat.cast_add, nat.cast_one] at this,
  convert this.div_const 2,
  simp_rw mul_div_cancel _ two_ne_zero,
end

lemma jacobi_theta_eq_tsum_nat {z : ℂ} (hz : 0 < im z) :
  jacobi_theta z = 1 + 2 * ∑' (n : ℕ), cexp (π * I * (n + 1) ^ 2 * z) :=
by rw [(has_sum_nat_jacobi_theta hz).tsum_eq, mul_div_cancel' _ (two_ne_zero' ℂ), ←add_sub_assoc,
  add_sub_cancel']

/-- An explicit upper bound for `‖jacobi_theta τ - 1‖`. -/
lemma norm_jacobi_theta_sub_one_le {z : ℂ} (hz : 0 < im z) :
  ‖jacobi_theta z - 1‖ ≤ 2 / (1 - exp (-π * z.im)) * exp (-π * z.im) :=
begin
  suffices : ‖∑' (n : ℕ), cexp (π * I * (n + 1) ^ 2 * z)‖ ≤ exp (-π * z.im) / (1 - exp (-π * z.im)),
  { calc ‖jacobi_theta z - 1‖ = 2 * ‖∑' (n : ℕ), cexp (π * I * (n + 1) ^ 2 * z)‖ :
      by rw [sub_eq_iff_eq_add'.mpr (jacobi_theta_eq_tsum_nat hz), norm_mul, complex.norm_eq_abs,
        complex.abs_two]
    ... ≤ 2 * (rexp (-π * z.im) / (1 - rexp (-π * z.im))) :
      by rwa [mul_le_mul_left (zero_lt_two' ℝ)]
    ... = 2 / (1 - rexp (-π * z.im)) * rexp (-π * z.im) : by rw [div_mul_comm, mul_comm] },
  have : ∀ (n : ℕ), ‖cexp (π * I * (n + 1) ^ 2 * z)‖ ≤ exp (-π * z.im) ^ (n + 1),
  { intro n,
    simpa only [int.cast_add, int.cast_one] using norm_exp_mul_sq_le hz (n + 1) },
  have s : has_sum (λ n : ℕ, rexp (-π * z.im) ^ (n + 1)) (exp (-π * z.im) / (1 - exp (-π * z.im))),
  { simp_rw [pow_succ, div_eq_mul_inv, has_sum_mul_left_iff (real.exp_ne_zero _)],
    exact has_sum_geometric_of_lt_1 (exp_pos (-π * z.im)).le
      (exp_lt_one_iff.mpr $ (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hz)) },
  have aux : summable (λ (n : ℕ), ‖cexp (↑π * I * (↑n + 1) ^ 2 * z)‖),
    from summable_of_nonneg_of_le (λ n, norm_nonneg _) this s.summable,
  exact (norm_tsum_le_tsum_norm aux).trans
    ((tsum_mono aux s.summable this).trans (le_of_eq s.tsum_eq)),
end

/-- The norm of `jacobi_theta τ - 1` decays exponentially as `im τ → ∞`. -/
lemma is_O_at_im_infty_jacobi_theta_sub_one :
  (λ τ, jacobi_theta τ - 1) =O[comap im at_top] (λ τ, rexp (-π * τ.im)) :=
begin
  simp_rw [is_O, is_O_with, filter.eventually_comap, filter.eventually_at_top],
  refine ⟨2 / (1 - rexp (-π)), 1, λ y hy z hz, (norm_jacobi_theta_sub_one_le
    (hz.symm ▸ (zero_lt_one.trans_le hy) : 0 < im z)).trans _⟩,
  rw [real.norm_eq_abs, real.abs_exp],
  refine mul_le_mul_of_nonneg_right _ (exp_pos _).le,
  rw [div_le_div_left (zero_lt_two' ℝ), sub_le_sub_iff_left, exp_le_exp, neg_mul, neg_le_neg_iff],
  { exact le_mul_of_one_le_right pi_pos.le (hz.symm ▸ hy) },
  { rw [sub_pos, exp_lt_one_iff, neg_mul, neg_lt_zero],
    exact mul_pos pi_pos (hz.symm ▸ (zero_lt_one.trans_le hy)) },
  { rw [sub_pos, exp_lt_one_iff, neg_lt_zero], exact pi_pos }
end

lemma differentiable_at_jacobi_theta {z : ℂ} (hz : 0 < im z) :
  differentiable_at ℂ jacobi_theta z :=
begin
  suffices : ∀ (y : ℝ) (hy : 0 < y),
    differentiable_on ℂ (λ z, ∑' (n : ℤ), cexp (π * I * n ^ 2 * z)) {w : ℂ | y < im w},
  from let ⟨y, hy, hy'⟩ := exists_between hz in (this y hy).differentiable_at
    ((complex.continuous_im.is_open_preimage _ is_open_Ioi).mem_nhds hy'),
  intros y hy,
  have h1 : ∀ (n : ℤ) (w : ℂ) (hw : y < im w), differentiable_within_at ℂ
    (λ (v : ℂ), cexp (↑π * I * ↑n ^ 2 * v)) {z : ℂ | y < im z} w,
  from λ n w hw, (differentiable_at_id.const_mul _).cexp.differentiable_within_at,
  have h2 : is_open {w : ℂ | y < im w}, from continuous_im.is_open_preimage _ is_open_Ioi,
  obtain ⟨bd, bd_s, le_bd⟩ := exists_summable_bound_exp_mul_sq hy,
  exact differentiable_on_tsum_of_summable_norm bd_s h1 h2 (λ i w hw, le_bd (le_of_lt hw) i),
end

lemma continuous_at_jacobi_theta {z : ℂ} (hz : 0 < im z) :
  continuous_at jacobi_theta z := (differentiable_at_jacobi_theta hz).continuous_at
