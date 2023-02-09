/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import analysis.quaternion
import analysis.normed_space.exponential
import analysis.inner_product_space.pi_L2
import analysis.special_functions.trigonometric.series

/-!
# Lemmas about `exp` on `quaternion`s

This file contains results about `exp` on `quaternion ℝ`.

## Main results

* `quaternion.exp_eq`: the general expansion of the quaternion exponential in terms of `real.cos`
  and `real.sin`.
* `quaternion.exp_of_re_eq_zero`: the special case when the quaternion has a zero real part.


-/

open_locale quaternion nat

-- TODO: move
lemma div_div_cancel_left' {G₀} [comm_group_with_zero G₀] (a b : G₀) (ha : a ≠ 0) :
  a / b / a = b⁻¹ :=
by rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm, mul_inv_cancel ha, one_mul]


namespace quaternion

section
variables {α : Type*}

lemma has_sum_coe {f : α → ℝ} {r : ℝ} (h : has_sum f r) :
  has_sum (λ a, (f a : ℍ[ℝ])) (↑r : ℍ[ℝ]) :=
by simpa only using h.map (algebra_map ℝ ℍ[ℝ]) (continuous_algebra_map _ _)

@[simp]
lemma summable_coe_iff  {f : α → ℝ} : summable (λ a, (f a : ℍ[ℝ])) ↔ summable f :=
by simpa only using summable.map_iff_of_left_inverse (algebra_map ℝ ℍ[ℝ])
  ({to_fun := re, map_add' := add_re, map_zero' := zero_re} : ℍ[ℝ] →+ ℝ)
  (continuous_algebra_map _ _) continuous_re coe_re

lemma tsum_coe (f : α → ℝ) : ∑' a, (f a : ℍ[ℝ]) = ↑(∑' a, f a) :=
begin
  by_cases hf : summable f,
  { exact (has_sum_coe hf.has_sum).tsum_eq, },
  { simp [tsum_eq_zero_of_not_summable hf,
      tsum_eq_zero_of_not_summable (summable_coe_iff.not.mpr hf)] },
end

end

@[simp, norm_cast] lemma exp_coe (r : ℝ) : exp ℝ (r : ℍ[ℝ]) = ↑(exp ℝ r) :=
(map_exp ℝ (algebra_map ℝ ℍ[ℝ]) (continuous_algebra_map _ _) _).symm

lemma conj_eq_neg_iff {q : ℍ} : conj q = -q ↔ q.re = 0 :=
ext_iff.trans $ by simp [eq_neg_iff_add_eq_zero]

/-- Auxiliary result; if the power series corresponding to `real.cos` and `real.sin` evaluatated
at `‖q‖` tend to `c` and `s`, then the exponential series tends to `c + (s / ‖q‖)`. -/
lemma has_sum_exp_series_of_imaginary
  {q : quaternion ℝ} (hq : q.re = 0) {c s : ℝ}
  (hc : has_sum (λ n, (-1)^n * ‖q‖^(2 * n) / (2 * n)!) c)
  (hs : has_sum (λ n, (-1)^n * ‖q‖^(2 * n + 1) / (2 * n + 1)!) s) :
  has_sum (λ n, exp_series ℝ _ n (λ _, q)) (↑c + (s / ‖q‖) • q) :=
begin
  replace hc := has_sum_coe hc,
  replace hs := (hs.div_const ‖q‖).smul_const q,
  obtain rfl | hq0 := eq_or_ne q 0,
  { clear hs,
    simp_rw [exp_series_apply_zero, norm_zero, div_zero, zero_smul, add_zero],
    simp_rw [norm_zero] at hc,
    convert hc,
    ext (_ | n) : 1,
    { rw [pow_zero, mul_zero, pow_zero, nat.factorial_zero, nat.cast_one, div_one, one_mul,
        pi.single_eq_same, coe_one], },
    { rw [zero_pow (mul_pos two_pos (nat.succ_pos _)), mul_zero, zero_div,
        pi.single_eq_of_ne (n.succ_ne_zero), coe_zero], } },
  simp_rw exp_series_apply_eq,
  have hq2 : q^2 = -norm_sq q,
  { rw [←quaternion.conj_mul_self, conj_eq_neg_iff.mpr hq, neg_mul, neg_neg, sq], },

  have hqn := norm_ne_zero_iff.mpr hq0,
  refine has_sum.even_add_odd _ _,
  { convert hc using 1,
    ext n : 1,
    let k : ℝ := ↑(2 * n)!,
    calc k⁻¹ • q ^ (2 * n)
        = k⁻¹ • ((-norm_sq q) ^ n) : by rw [pow_mul, hq2]
    ... = k⁻¹ • ↑((-1) ^ n * ‖q‖ ^ (2 * n)) : _
    ... = ↑((-1) ^ n * ‖q‖ ^ (2 * n) / k) : _,
    { congr' 1,
      rw [neg_pow, norm_sq_eq_norm_sq, pow_mul, sq],
      push_cast },
    { rw [←coe_mul_eq_smul, div_eq_mul_inv],
      norm_cast,
      ring_nf } },
  { convert hs using 1,
    ext n : 1,
    let k : ℝ := ↑(2 * n + 1)!,
    calc k⁻¹ • q ^ (2 * n + 1)
        = k⁻¹ • ((-norm_sq q) ^ n * q) : by rw [pow_succ', pow_mul, hq2]
    ... = k⁻¹ • ((-1) ^ n * ‖q‖ ^ (2 * n)) • q : _
    ... = ((-1) ^ n * ‖q‖ ^ (2 * n + 1) / k / ‖q‖) • q : _,
    { congr' 1,
      rw [neg_pow, norm_sq_eq_norm_sq, pow_mul, sq, ←coe_mul_eq_smul],
      push_cast },
    { rw smul_smul,
      congr' 1,
      simp_rw [pow_succ', mul_div_assoc, div_div_cancel_left' _ _ hqn],
      ring } },
end

/-- The closed for for the quaternion exponential on imaginary quaternions. -/
lemma exp_of_re_eq_zero (q : quaternion ℝ) (hq : q.re = 0) :
  exp ℝ q = ↑(real.cos ‖q‖) + (real.sin ‖q‖ / ‖q‖) • q :=
begin
  rw [exp_eq_tsum],
  refine has_sum.tsum_eq _,
  simp_rw ← exp_series_apply_eq,
  exact has_sum_exp_series_of_imaginary hq (real.has_sum_cos _) (real.has_sum_sin _),
end

-- -- TODO: remove, unless this proof is nicer?
-- lemma exp_of_imaginary (q : quaternion ℝ) (hq : q.re = 0) :
--   exp ℝ q = ↑(real.cos ‖q‖) + (real.sin ‖q‖ / ‖q‖) • q :=
-- begin
--   obtain rfl | hq0 := eq_or_ne q 0,
--   { simp },
--   have hconj : conj q = -q,
--   { ext,
--     { simp [hq] },
--     iterate 3 { refl } },
--   have : q^2 = -norm_sq q,
--   { rw [←quaternion.conj_mul_self, hconj, neg_mul, neg_neg, sq], },
--   simp_rw exp_eq_tsum,
--   have heven : ∀ k : ℕ,
--     ((2 * k)! : ℝ)⁻¹ • q ^ (2 * k) = ↑((-1)^k * ((2 * k)! : ℝ)⁻¹ * ‖q‖ ^ (2 * k)),
--   { intro k,
--     rw [pow_mul, this, ←coe_neg, ←coe_pow, ←coe_smul, norm_sq_eq_norm_sq,
--       ←sq, neg_pow (‖q‖^2), smul_eq_mul, pow_mul, mul_left_comm, mul_assoc], },
--   have hodd : ∀ k : ℕ,
--     ((2 * k + 1)! : ℝ)⁻¹ • q ^ (2 * k + 1)
--       = ↑((-1)^k * ((2 * k + 1)! : ℝ)⁻¹ * ‖q‖ ^ (2 * k + 1) / ‖q‖) * q,
--   { intro k,
--     rw [pow_succ' _ (2 * _), pow_mul, this, ←coe_neg, ←coe_pow, ←smul_mul_assoc,
--       ←coe_smul, norm_sq_eq_norm_sq,
--       ←sq, neg_pow (‖q‖^2), smul_eq_mul, mul_left_comm, ←pow_mul, div_eq_mul_inv, mul_assoc,
--       mul_assoc, pow_succ', mul_assoc, mul_inv_cancel (norm_ne_zero_iff.mpr hq0), mul_one], },
--   simp_rw [mul_assoc, ←div_eq_inv_mul, ←mul_div_assoc] at heven hodd,
--   rw ←tsum_even_add_odd,
--   { simp_rw [heven, hodd, tsum_mul_right, tsum_coe, coe_mul_eq_smul, tsum_div_const],
--     congr' 3,
--     { rw real.cos_eq_tsum },
--     { rw real.sin_eq_tsum } },
--   { simp_rw heven,
--     rw summable_coe_iff,
--     exact (real.has_sum_cos _).summable },
--   { simp_rw hodd,
--     apply summable.mul_right,
--     rw summable_coe_iff,
--     apply summable.div_const,
--     exact (real.has_sum_sin _).summable },
-- end


/-- The closed form for the quaternion exponential on arbitrary quaternions. -/
lemma exp_eq (q : quaternion ℝ) :
  exp ℝ q = exp ℝ q.re • (
    let v := q - q.re in ↑(real.cos ‖v‖) + (real.sin ‖v‖ / ‖v‖) • v) :=
begin
  dsimp only,
  rw [←exp_of_re_eq_zero (q - q.re), ←coe_mul_eq_smul, ←exp_coe,
    ←exp_add_of_commute, add_sub_cancel'_right],
  exact algebra.commutes q.re (_ : ℍ[ℝ]),
  exact sub_self _,
end

end quaternion
