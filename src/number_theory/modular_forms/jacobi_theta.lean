/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import analysis.complex.upper_half_plane.topology
import analysis.complex.upper_half_plane.functions_bounded_at_infty
import analysis.special_functions.gaussian
import analysis.calculus.series

/-! # Jacobi's theta function

This file defines the Jacobi theta function

$$\theta(\tau) = \sum_{n \in \mathbb{Z}} \exp (i \pi n ^ 2 \tau),$$

and proves the modular transformation properties `θ (τ + 2) = θ τ` and
`θ (-1 / τ) = (-I * τ) ^ (1 / 2) * θ τ`, using Poisson's summation formula for the latter. We also
show that `θ` is differentiable on `ℍ`, and `θ(τ) - 1` has exponential decay as `im τ → ∞`.
-/

open complex real asymptotics

open_locale real big_operators upper_half_plane

/-- Jacobi's theta function `∑' (n : ℤ), exp (π * I * n ^ 2 * τ)`. -/
noncomputable def jacobi_theta (τ : ℍ) : ℂ := ∑' (n : ℤ), cexp (π * I * n ^ 2 * τ)

/-- Geometric bound for the terms in the series. (Formulated in a way that is logically non-optimal
but easier to apply -- we don't want to be messing around checking that `exp (-π * im τ) < 1`, etc,
further downstream.) -/
lemma jacobi_theta_term_bound {t : ℝ} (ht : 0 < t) : ∃ y : ℝ, 0 < y ∧ y < 1 ∧
  ∀ (z : ℂ) (hz : t ≤ z.im) (n : ℤ), ‖cexp (π * I * n ^ 2 * z)‖ ≤ y ^ n.nat_abs :=
begin
  refine ⟨_, exp_pos _,
    exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) ht), (λ z hz n, _)⟩,
  have : rexp (-π * z.im) ≤ rexp (-π * t),
  { rw [exp_le_exp, neg_mul, neg_mul, neg_le_neg_iff],
    exact mul_le_mul_of_nonneg_left hz pi_pos.le },
  refine le_trans _ (pow_le_pow_of_le_left (exp_pos _).le this _),
  let y := rexp (-π * z.im),
  replace hz := ht.trans_le hz,
  have h : y < 1, from exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hz),
  refine (le_of_eq _).trans (_ : y ^ (n ^ 2) ≤ y ^ (n.nat_abs)),
  { rw [complex.norm_eq_abs, complex.abs_exp],
    have : (↑π * I * n ^ 2 * z).re = (-π * z.im) * n ^ 2,
    { rw [(by { push_cast, ring } : ↑π * I * n ^ 2 * z = ↑(π * n ^ 2) * (z * I)),
        of_real_mul_re, mul_I_re],
      ring },
    obtain ⟨m, hm⟩ := int.eq_coe_of_zero_le (sq_nonneg n),
    rw [this, exp_mul, ←int.cast_pow, rpow_int_cast, hm, zpow_coe_nat] },
  { have : n ^ 2 = ↑(n.nat_abs ^ 2), by rw [nat.cast_pow, int.nat_abs_sq],
    rw [this, zpow_coe_nat],
    refine pow_le_pow_of_le_one (exp_pos _).le h.le _,
    rw sq,
    exact n.nat_abs.le_mul_self },
end

lemma jacobi_theta_unif_summable {R : ℝ} (hR : 0 < R) :
  ∃ (bd : ℤ → ℝ), (summable bd) ∧
  (∀ {τ : ℍ} (hτ : R ≤ τ.im) (n : ℤ), ‖cexp (π * I * n ^ 2 * τ)‖ ≤ bd n) :=
begin
  obtain ⟨y, hy1, hy2, hb⟩ := jacobi_theta_term_bound hR,
  refine ⟨λ n, y ^ n.nat_abs, summable_int_of_summable_nat _ _, λ τ hτ n, hb _ hτ n⟩,
  all_goals { simpa only [int.nat_abs_neg, int.nat_abs_of_nat]
    using summable_geometric_of_lt_1 hy1.le hy2, },
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
  simp only [←subtype.coe_inj, upper_half_plane.modular_T_zpow_smul, int.cast_two],
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

lemma jacobi_theta_continuous : continuous jacobi_theta :=
begin
  suffices : ∀ (y : ℝ) (hy : 0 < y), continuous_on jacobi_theta {z : ℍ | y < z.im},
  { refine continuous_iff_continuous_at.mpr (λ τ, _),
    exact let ⟨y, hy, hy'⟩ := exists_between τ.im_pos in continuous_on.continuous_at (this y hy)
      ((upper_half_plane.continuous_im.is_open_preimage _ is_open_Ioi).mem_nhds hy') },
  intros y hy,
  obtain ⟨bd, h_bd, h_bd2⟩ := jacobi_theta_unif_summable hy,
  refine continuous_on_tsum (λ n, continuous.continuous_on _) h_bd (λ n z h, h_bd2 (le_of_lt h) n),
  exact complex.continuous_exp.comp (continuous_const.mul continuous_induced_dom)
end

lemma jacobi_theta_has_sum_nat (τ : ℍ) :
  has_sum (λ (n : ℕ), cexp (π * I * (n + 1) ^ 2 * τ)) ((jacobi_theta τ - 1) / 2) :=
begin
  have := (jacobi_theta_summable τ).has_sum.sum_nat_of_sum_int,
  rw ←@has_sum_nat_add_iff' ℂ _ _ _ _ 1 at this,
  simp_rw [finset.sum_range_one, int.cast_neg, int.cast_coe_nat, nat.cast_zero, neg_zero,
    int.cast_zero, sq (0:ℂ), mul_zero, zero_mul, neg_sq, ←mul_two, complex.exp_zero,
    add_sub_assoc, (by norm_num : (1 : ℂ) - 1 * 2 = -1), ←sub_eq_add_neg,
    nat.cast_add, nat.cast_one] at this,
  convert this.div_const 2,
  simp_rw mul_div_cancel _ two_ne_zero,
end

lemma jacobi_theta_eq_tsum_nat (τ : ℍ) :
  jacobi_theta τ = 1 + 2 * ∑' (n : ℕ), cexp (π * I * (n + 1) ^ 2 * τ) :=
by rw [(jacobi_theta_has_sum_nat τ).tsum_eq, mul_div_cancel' _ (two_ne_zero' ℂ), ←add_sub_assoc,
  add_sub_cancel']

/-- An explicit upper bound for `‖jacobi_theta τ - 1‖`. -/
lemma jacobi_theta_sub_one_norm_le (τ : ℍ) :
  ‖jacobi_theta τ - 1‖ ≤ 2 / (1 - exp (-π * τ.im)) * exp (-π * τ.im) :=
begin
  suffices : ‖∑' (n : ℕ), cexp (π * I * (n + 1) ^ 2 * τ)‖ ≤ exp (-π * τ.im) / (1 - exp (-π * τ.im)),
  { calc ‖jacobi_theta τ - 1‖ = 2 * ‖∑' (n : ℕ), cexp (π * I * (n + 1) ^ 2 * τ)‖ :
      by rw [sub_eq_iff_eq_add'.mpr (jacobi_theta_eq_tsum_nat τ), norm_mul, complex.norm_eq_abs,
        complex.abs_two]
    ... ≤ 2 * (rexp (-π * τ.im) / (1 - rexp (-π * τ.im))) :
      by rwa [mul_le_mul_left (zero_lt_two' ℝ)]
    ... = 2 / (1 - rexp (-π * τ.im)) * rexp (-π * τ.im) : by rw [div_mul_comm, mul_comm] },
  have : ∀ (n : ℕ), ‖cexp (π * I * (n + 1) ^ 2 * τ)‖ ≤ exp (-π * τ.im) ^ (n + 1),
  { intro n,
    rw [(by { push_cast, ring } : ↑π * I * (n + 1) ^ 2 * τ = ↑(π * (n + 1) ^ 2 : ℝ) * (τ * I)),
      complex.norm_eq_abs, complex.abs_exp, of_real_mul_re, mul_I_re, upper_half_plane.coe_im,
      mul_neg, ←neg_mul, ←neg_mul, mul_assoc, mul_comm, mul_assoc, mul_comm τ.im,
      (by push_cast : ((n:ℝ) + 1) ^ 2 = ↑((n + 1) ^ 2)), real.exp_nat_mul],
    exact pow_le_pow_of_le_one (exp_pos _).le
      (exp_le_one_iff.mpr $ (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) τ.im_pos).le)
      (nat.le_self_pow two_ne_zero _) },
  have s : has_sum (λ n : ℕ, rexp (-π * τ.im) ^ (n + 1))
    (rexp (-π * τ.im) / (1 - rexp (-π * τ.im))),
  { simp_rw [pow_succ, div_eq_mul_inv, has_sum_mul_left_iff (real.exp_ne_zero _)],
    exact has_sum_geometric_of_lt_1 (exp_pos (-π * τ.im)).le
      (exp_lt_one_iff.mpr $ (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) τ.im_pos)) },
  have aux : summable (λ (n : ℕ), ‖cexp (↑π * I * (↑n + 1) ^ 2 * ↑τ)‖),
    from summable_of_nonneg_of_le (λ n, norm_nonneg _) this s.summable,
  exact (norm_tsum_le_tsum_norm aux).trans
    ((tsum_mono aux s.summable this).trans (le_of_eq s.tsum_eq)),
end

/-- The norm of `jacobi_theta τ - 1` decays exponentially as `im τ → ∞`. -/
lemma jacobi_theta_sub_one_is_O_im_infty :
  is_O upper_half_plane.at_im_infty (λ τ, jacobi_theta τ - 1) (λ τ, rexp (-π * τ.im)) :=
begin
  simp_rw [is_O, is_O_with, filter.eventually, upper_half_plane.at_im_infty_mem],
  refine ⟨2 / (1 - rexp (-π)), 1, (λ τ hτ, (jacobi_theta_sub_one_norm_le τ).trans _)⟩,
  rw [real.norm_eq_abs, real.abs_exp],
  refine mul_le_mul_of_nonneg_right _ (exp_pos _).le,
  rw [div_le_div_left (zero_lt_two' ℝ), sub_le_sub_iff_left, exp_le_exp, neg_mul, neg_le_neg_iff],
  { exact le_mul_of_one_le_right pi_pos.le hτ },
  { rw [sub_pos, exp_lt_one_iff, neg_mul, neg_lt_zero], exact mul_pos pi_pos τ.im_pos },
  { rw [sub_pos, exp_lt_one_iff, neg_lt_zero], exact pi_pos }
end

-- Formulation of this result is somewhat roundabout, since functions on subtypes don't play well
-- with `differentiable_at`.
lemma jacobi_theta_differentiable_at (τ : ℍ) :
  differentiable_at ℂ (λ z, ∑' (n : ℤ), cexp (π * I * n ^ 2 * z)) ↑τ :=
begin
  suffices : ∀ (y : ℝ) (hy : 0 < y),
    differentiable_on ℂ (λ z, ∑' (n : ℤ), cexp (π * I * n ^ 2 * z)) {z : ℂ | y < im z},
  from let ⟨y, hy, hy'⟩ := exists_between τ.im_pos in (this y hy).differentiable_at
    ((complex.continuous_im.is_open_preimage _ is_open_Ioi).mem_nhds (τ.coe_im ▸ hy')),
  intros y hy z hz,
  -- Check the easy hypotheses for summability result
  have h1 : is_open {w : ℂ | y < im w}, from continuous_im.is_open_preimage _ is_open_Ioi,
  have h2 : is_preconnected {w : ℂ | y < im w}, from (convex_halfspace_im_gt _).is_preconnected,
  have h3 : ∀ (n : ℤ) (w : ℂ), w ∈ {v : ℂ | y < v.im} →
    has_deriv_at (λ (v : ℂ), cexp (↑π * I * ↑n ^ 2 * v))
    (cexp (↑π * I * ↑n ^ 2 * w) * (↑π * I * ↑n ^ 2)) w,
  { intros n w hw,
    apply has_deriv_at.cexp,
    convert (has_deriv_at_id w).const_mul _ using 1,
    rw mul_one },
  have h3' := (λ n w hw, (h3 n w hw).has_fderiv_at),
  have h4 : z ∈ {w : ℂ | y < im w}, from hz,
  have h5 : summable (λ (n : ℤ), cexp (↑π * I * ↑n ^ 2 * z)),
    by apply jacobi_theta_summable ⟨z, hy.trans hz⟩,
  -- The harder one: uniform summability of termwise derivatives
  obtain ⟨q, hq, hq', hb⟩ := jacobi_theta_term_bound hy,
  have h_le_bd : ∀ (n : ℤ) (w : ℂ) (hw : y < im w),
    ‖cexp (↑π * I * ↑n ^ 2 * w) * (↑π * I * ↑n ^ 2)‖ ≤ π * n ^ 2 * q ^ n.nat_abs,
  { intros n w hw,
    rw [norm_mul, mul_comm ‖_‖],
    refine mul_le_mul (le_of_eq _) (hb _ hw.le _) (norm_nonneg _)
      (mul_nonneg pi_pos.le $ sq_nonneg _),
    rw [norm_mul, norm_mul, is_R_or_C.norm_of_nonneg pi_pos.le, complex.norm_eq_abs, abs_I,
        mul_one, ←of_real_int_cast, ←of_real_pow, is_R_or_C.norm_of_nonneg (sq_nonneg _)] },
  have h_bd_s : summable (λ n : ℤ, π * n ^ 2 * q ^ n.nat_abs),
  { simp_rw mul_assoc,
    apply summable.mul_left,
    have : summable (λ n : ℕ, ↑n ^ 2 * q ^ n), from summable_pow_mul_geometric_of_norm_lt_1 2
      ((norm_of_nonneg hq.le).symm ▸ hq'),
    refine summable_int_of_summable_nat this _,
    simpa only [int.cast_neg, int.nat_abs_neg, neg_sq] using this},
  -- now main proof
  apply differentiable_at.differentiable_within_at,
  apply has_fderiv_at.differentiable_at,
  refine has_fderiv_at_tsum_of_is_preconnected h_bd_s h1 h2 h3' (λ n w hw, _) h4 h5 h4,
  refine (le_of_eq _).trans (h_le_bd n w hw),
  rw [continuous_linear_map.norm_smul_right_apply, norm_one, one_mul],
end
