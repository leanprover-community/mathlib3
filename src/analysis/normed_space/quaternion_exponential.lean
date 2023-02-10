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
* `quaternion.norm_exp`: the norm of the quaternion exponential is the norm of the exponential of
  the real part.

-/

open_locale quaternion nat

-- TODO: move
lemma div_div_cancel_left' {G₀} [comm_group_with_zero G₀] (a b : G₀) (ha : a ≠ 0) :
  a / b / a = b⁻¹ :=
by rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm, mul_inv_cancel ha, one_mul]


namespace quaternion

section
variables {α : Type*}

@[simp, norm_cast] lemma has_sum_coe {f : α → ℝ} {r : ℝ} :
  has_sum (λ a, (f a : ℍ[ℝ])) (↑r : ℍ[ℝ]) ↔ has_sum f r :=
⟨λ h, by simpa only using
  h.map (show ℍ[ℝ] →ₗ[ℝ] ℝ, from quaternion_algebra.re_lm _ _) continuous_re,
  λ h, by simpa only using h.map (algebra_map ℝ ℍ[ℝ]) (continuous_algebra_map _ _)⟩

@[simp, norm_cast]
lemma summable_coe {f : α → ℝ} : summable (λ a, (f a : ℍ[ℝ])) ↔ summable f :=
by simpa only using summable.map_iff_of_left_inverse (algebra_map ℝ ℍ[ℝ])
  (show ℍ[ℝ] →ₗ[ℝ] ℝ, from quaternion_algebra.re_lm _ _)
  (continuous_algebra_map _ _) continuous_re coe_re

@[norm_cast] lemma tsum_coe (f : α → ℝ) : ∑' a, (f a : ℍ[ℝ]) = ↑(∑' a, f a) :=
begin
  by_cases hf : summable f,
  { exact (has_sum_coe.mpr hf.has_sum).tsum_eq, },
  { simp [tsum_eq_zero_of_not_summable hf,
      tsum_eq_zero_of_not_summable (summable_coe.not.mpr hf)] },
end

end

lemma conj_exp (q : ℍ[ℝ]) : conj (exp ℝ q) = exp ℝ (conj q) := star_exp q

@[simp, norm_cast] lemma exp_coe (r : ℝ) : exp ℝ (r : ℍ[ℝ]) = ↑(exp ℝ r) :=
(map_exp ℝ (algebra_map ℝ ℍ[ℝ]) (continuous_algebra_map _ _) _).symm

/-- Auxiliary result; if the power series corresponding to `real.cos` and `real.sin` evaluatated
at `‖q‖` tend to `c` and `s`, then the exponential series tends to `c + (s / ‖q‖)`. -/
lemma has_sum_exp_series_of_imaginary
  {q : quaternion ℝ} (hq : q.re = 0) {c s : ℝ}
  (hc : has_sum (λ n, (-1)^n * ‖q‖^(2 * n) / (2 * n)!) c)
  (hs : has_sum (λ n, (-1)^n * ‖q‖^(2 * n + 1) / (2 * n + 1)!) s) :
  has_sum (λ n, exp_series ℝ _ n (λ _, q)) (↑c + (s / ‖q‖) • q) :=
begin
  replace hc := has_sum_coe.mpr hc,
  replace hs := (hs.div_const ‖q‖).smul_const q,
  obtain rfl | hq0 := eq_or_ne q 0,
  { simp_rw [exp_series_apply_zero, norm_zero, div_zero, zero_smul, add_zero],
    simp_rw [norm_zero] at hc,
    convert hc,
    ext (_ | n) : 1,
    { rw [pow_zero, mul_zero, pow_zero, nat.factorial_zero, nat.cast_one, div_one, one_mul,
        pi.single_eq_same, coe_one], },
    { rw [zero_pow (mul_pos two_pos (nat.succ_pos _)), mul_zero, zero_div,
        pi.single_eq_of_ne (n.succ_ne_zero), coe_zero], } },
  simp_rw exp_series_apply_eq,
  have hq2 : q^2 = -norm_sq q := sq_eq_neg_norm_sq.mpr hq,
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

lemma re_exp (q : ℍ[ℝ]) : (exp ℝ q).re = exp ℝ q.re * (real.cos ‖q - q.re‖) :=
by simp [exp_eq]

lemma norm_sq_exp (q : ℍ[ℝ]) : norm_sq (exp ℝ q) = (exp ℝ q.re)^2 :=
let v := q - q.re in
calc norm_sq (exp ℝ q)
    = norm_sq (exp ℝ q.re • (↑(real.cos ‖v‖) + (real.sin ‖v‖ / ‖v‖) • v))
    : by rw exp_eq
... = (exp ℝ q.re)^2 * norm_sq ((↑(real.cos ‖v‖) + (real.sin ‖v‖ / ‖v‖) • v))
    : by rw [norm_sq_smul]
... = (exp ℝ q.re)^2 * ((real.cos ‖v‖) ^ 2 + (real.sin ‖v‖)^2)
    : begin
      congr' 1,
      have : v.re = 0,
      { rw [sub_re, coe_re, sub_self] },
      obtain hv | hv := eq_or_ne (‖v‖) 0,
      { simp [hv] },
      rw [norm_sq_add, norm_sq_smul, conj_smul, coe_mul_eq_smul, smul_re, smul_re, conj_re, this,
        smul_zero, smul_zero, mul_zero, add_zero, div_pow, norm_sq_coe, norm_sq_eq_norm_sq, ←sq,
        div_mul_cancel _ (pow_ne_zero _ hv)],
    end
... = (exp ℝ q.re)^2 : by rw [real.cos_sq_add_sin_sq, mul_one]

/-- Note that this implies that exponentials of pure imaginary quaternions are unit quaternions. -/
@[simp] lemma norm_exp (q : ℍ[ℝ]) : ‖exp ℝ q‖ = ‖exp ℝ q.re‖ :=
by rw [norm_eq_sqrt_real_inner (exp ℝ q), inner_self, norm_sq_exp, real.sqrt_sq_eq_abs,
  real.norm_eq_abs]

end quaternion
