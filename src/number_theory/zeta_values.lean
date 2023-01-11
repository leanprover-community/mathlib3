/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import number_theory.bernoulli_polynomials
import analysis.special_functions.integrals
import measure_theory.integral.interval_integral
import analysis.fourier.add_circle
import analysis.p_series


/-!
# Critical values of the Riemann zeta function

In this file we prove formulae for the critical values of `ζ(s)`, and more generally of Hurwitz
zeta functions, in terms of Bernoulli polynomials.

## Main results:

* `zeta_value`: the final formula for zeta values,
  $$\zeta(2k) = \frac{(-1)^{(k + 1)} 2 ^ {2k - 1} π ^ {2k} B_{2 k}}{(2 k)!}.$$
* `zeta_two` and `zeta_four`: special cases given explicitly.
* `polylog_eval_even`: a formula for the sum `∑ (n : ℕ), cos (2 π i n x) / n ^ k` as an explicit
  multiple of `Bₖ(x)`, for any `x ∈ [0, 1]` and `k ≥ 2` even.
* `polylog_eval_odd`: a formula for the sum `∑ (n : ℕ), sin (2 π i n x) / n ^ k` as an explicit
  multiple of `Bₖ(x)`, for any `x ∈ [0, 1]` and `k ≥ 3` odd.
-/


noncomputable theory
open_locale nat real interval
open complex measure_theory set interval_integral

section bernoulli_fun_props
/-! Simple properties of the Bernoulli polynomial, as a function `ℝ → ℝ`. -/

/-- The function `x ↦ Bₖ(x) : ℝ → ℝ`. -/
def bernoulli_fun (k : ℕ) (x : ℝ) : ℝ :=
(polynomial.map (algebra_map ℚ ℝ) (polynomial.bernoulli k)).eval x

lemma bernoulli_fun_eval_zero (k : ℕ) : bernoulli_fun k 0 = bernoulli k :=
by rw [bernoulli_fun, polynomial.eval_zero_map, polynomial.bernoulli_eval_zero, eq_rat_cast]

lemma bernoulli_fun_endpoints_eq_of_ne_one {k : ℕ} (hk : k ≠ 1) :
  bernoulli_fun k 1 = bernoulli_fun k 0 :=
by rw [bernoulli_fun_eval_zero, bernoulli_fun, polynomial.eval_one_map,
  polynomial.bernoulli_eval_one, bernoulli_eq_bernoulli'_of_ne_one hk, eq_rat_cast]

lemma bernoulli_fun_eval_one (k : ℕ) : bernoulli_fun k 1 = bernoulli_fun k 0 + ite (k = 1) 1 0 :=
begin
  rw [bernoulli_fun, bernoulli_fun_eval_zero, polynomial.eval_one_map,
    polynomial.bernoulli_eval_one],
  split_ifs,
  { rw [h, bernoulli_one, bernoulli'_one, eq_rat_cast],
    push_cast, ring },
  { rw [bernoulli_eq_bernoulli'_of_ne_one h, add_zero, eq_rat_cast], }
end

lemma has_deriv_at_bernoulli_fun (k : ℕ) (x : ℝ) :
  has_deriv_at (bernoulli_fun k) (k * bernoulli_fun (k - 1) x) x :=
begin
  convert ((polynomial.bernoulli k).map $ algebra_map ℚ ℝ).has_deriv_at x using 1,
  simp only [bernoulli_fun, polynomial.derivative_map, polynomial.derivative_bernoulli k,
    polynomial.map_mul, polynomial.map_nat_cast, polynomial.eval_mul, polynomial.eval_nat_cast],
end

lemma antideriv_bernoulli_fun (k : ℕ) (x : ℝ) :
  has_deriv_at (λ x, (bernoulli_fun (k + 1) x) / (k + 1)) (bernoulli_fun k x) x :=
begin
  convert (has_deriv_at_bernoulli_fun (k + 1) x).div_const _,
  field_simp [nat.cast_add_one_ne_zero k],
  ring,
end

lemma integral_bernoulli_fun_eq_zero {k : ℕ} (hk : k ≠ 0) :
  ∫ (x : ℝ) in 0..1, bernoulli_fun k x = 0 :=
begin
  rw integral_eq_sub_of_has_deriv_at (λ x hx, antideriv_bernoulli_fun k x)
    ((polynomial.continuous _).interval_integrable _ _),
  dsimp only,
  rw bernoulli_fun_eval_one,
  split_ifs,
  { exfalso, exact hk (nat.succ_inj'.mp h), }, { simp },
end

end bernoulli_fun_props

section bernoulli_fourier_coeffs
/-! Compute the Fourier coefficients of the Bernoulli functions via integration by parts. -/

local attribute [instance] real.fact_zero_lt_one

/-- The `n`-th Fourier coefficient of the `k`-th Bernoulli function on the interval `[0, 1]`. -/
def bernoulli_fourier_coeff (k : ℕ) (n : ℤ) : ℂ :=
fourier_coeff_on zero_lt_one (λ x, bernoulli_fun k x) n

/-- Recurrence relation (in `k`) for the `n`-th Fourier coefficient of `Bₖ`. -/
lemma bernoulli_fourier_coeff_recurrence (k : ℕ) {n : ℤ} (hn : n ≠ 0) :
  bernoulli_fourier_coeff k n = 1 / ((-2) * π * I * n) *
  (ite (k = 1) 1 0 - k * bernoulli_fourier_coeff (k - 1) n) :=
begin
  unfold bernoulli_fourier_coeff,
  rw [fourier_coeff_on_of_has_deriv_at zero_lt_one
    hn (λ x hx, (has_deriv_at_bernoulli_fun k x).of_real_comp)
    ((continuous_of_real.comp $ continuous_const.mul
      $ polynomial.continuous _).interval_integrable _ _)],
  dsimp only,
  simp_rw [of_real_one, of_real_zero, sub_zero, one_mul],
  rw [quotient_add_group.coe_zero, fourier_eval_zero, one_mul,
    ←of_real_sub, bernoulli_fun_eval_one, add_sub_cancel'],
  congr' 2,
  { split_ifs, all_goals { simp only [of_real_one, of_real_zero, one_mul]}, },
  { simp_rw [of_real_mul, of_real_nat_cast, fourier_coeff_on.const_mul] },
end

/-- The Fourier coefficients of `B₀(x) = 1`. -/
lemma bernoulli_zero_fourier_coeff {n : ℤ} (hn : n ≠ 0) : bernoulli_fourier_coeff 0 n = 0 :=
by simpa using bernoulli_fourier_coeff_recurrence 0 hn

/-- The `0`-th Fourier coefficient of `Bₖ(x)`. -/
lemma bernoulli_fourier_coeff_zero {k : ℕ} (hk : k ≠ 0) : bernoulli_fourier_coeff k 0 = 0 :=
by simp_rw [bernoulli_fourier_coeff, fourier_coeff_on_eq_integral, neg_zero, fourier_zero, sub_zero,
  div_one, one_smul, interval_integral.integral_of_real, integral_bernoulli_fun_eq_zero hk,
  of_real_zero]

lemma bernoulli_fourier_coeff_eq {k : ℕ} (hk : k ≠ 0) (n : ℤ) :
  bernoulli_fourier_coeff k n = - k! / (2 * π * I * n) ^ k :=
begin
  rcases eq_or_ne n 0 with rfl|hn,
  { rw [bernoulli_fourier_coeff_zero hk, int.cast_zero, mul_zero,
    zero_pow' _ hk, div_zero] },
  refine nat.le_induction _ (λ k hk h'k, _) k (nat.one_le_iff_ne_zero.mpr hk),
  { rw bernoulli_fourier_coeff_recurrence 1 hn,
    simp only [nat.cast_one, tsub_self, neg_mul, one_mul, eq_self_iff_true, if_true,
      nat.factorial_one, pow_one, inv_I, mul_neg],
    rw [bernoulli_zero_fourier_coeff hn, sub_zero, mul_one, div_neg, neg_div], },
  { rw [bernoulli_fourier_coeff_recurrence (k + 1) hn, nat.add_sub_cancel k 1],
    split_ifs,
    { exfalso, exact (ne_of_gt (nat.lt_succ_iff.mpr hk)) h,},
    { rw [h'k, nat.factorial_succ, zero_sub, nat.cast_mul, pow_add, pow_one, neg_div,
        mul_neg, mul_neg, mul_neg, neg_neg, neg_mul, neg_mul, neg_mul, div_neg],
      field_simp [int.cast_ne_zero.mpr hn, I_ne_zero],
      ring_nf, } }
end

end bernoulli_fourier_coeffs

section zsums
/-! Some utility results about sums indexed by `ℤ`. -/

variables {α : Type*} {f : ℤ → α} {a : α} [add_comm_group α]

lemma summable_int_of_summable_nat [topological_space α] [topological_add_group α]
  (hp : summable (λ n:ℕ, f n)) (hn: summable (λ n:ℕ, f (-n))) : summable f :=
(has_sum.nonneg_add_neg hp.has_sum $ summable.has_sum $ (summable_nat_add_iff 1).mpr hn).summable

lemma has_sum.sum_nat_of_sum_int' [uniform_space α] [uniform_add_group α] [complete_space α]
  [t2_space α] (hf : has_sum f a) : has_sum (λ n:ℕ, f n + f (-n)) (a + f 0) :=
begin
  obtain ⟨b₁, h₁⟩ : summable (λ n : ℕ, f n) := hf.summable.comp_injective (λ x y, by simp),
  obtain ⟨b₂, h₂⟩ : summable (λ n : ℕ, f (-n.succ)) := hf.summable.comp_injective (λ x y, by simp),
  rcases (has_sum.nonneg_add_neg h₁ h₂).unique hf with rfl,
  simp_rw nat.succ_eq_add_one at h₂,
  rw [@has_sum_nat_add_iff _ _ _ _ (λ n:ℕ, f (-n)), finset.range_one, finset.sum_singleton] at h₂,
  convert h₁.add h₂ using 1,
  rw [nat.cast_zero, neg_zero, ←add_assoc],
end

lemma real.summable_one_div_int_pow {p : ℕ} (h : 1 < p) : summable (λ n:ℤ, 1 / (n : ℝ) ^ p) :=
begin
  refine summable_int_of_summable_nat (real.summable_one_div_nat_pow.mpr h)
    (((real.summable_one_div_nat_pow.mpr h).mul_left $ 1 / (-1) ^ p).congr $ λ n, _),
  conv_rhs { rw [int.cast_neg, neg_eq_neg_one_mul, mul_pow, ←div_div] },
  conv_lhs { rw [mul_div, mul_one], },
  refl,
end

end zsums

section bernoulli_periodized
/-! In this section we start actually applying genuine results from Fourier theory, notably
 `has_pointwise_sum_fourier_series_of_summable`, to obtain an explicit formula for
 `∑ (n:ℕ), 1 / n ^ k * cos (2 π i n x)` (for k even) or `∑ (n:ℕ), 1 / n ^ k * sin (2 π i n x)` (for
 k odd). -/

private lemma fact_zero_lt_one : fact ((0:ℝ) < 1) := ⟨zero_lt_one⟩
local attribute [instance] fact_zero_lt_one

/-- The Bernoulli polynomial, extended from `[0, 1]` to a continuous function on the circle. -/
def periodized_bernoulli {k : ℕ} (hk : k ≠ 1) : C(unit_add_circle, ℂ) :=
{ to_fun            := add_circle.lift_Ico 1 0 (coe ∘ bernoulli_fun k),
  continuous_to_fun := add_circle.lift_Ico_zero_continuous
                        (by exact_mod_cast (bernoulli_fun_endpoints_eq_of_ne_one hk).symm)
                        (continuous_of_real.comp (polynomial.continuous _)).continuous_on }

lemma fourier_coeff_bernoulli_eq {k : ℕ} (hk : 2 ≤ k) (n : ℤ) : fourier_coeff
  (periodized_bernoulli (by linarith : k ≠ 1)) n = -k.factorial / (2 * π * I * n) ^ k :=
begin
  rw [fourier_coeff_eq_interval_integral,
    ←bernoulli_fourier_coeff_eq (by linarith : k ≠ 0) n, bernoulli_fourier_coeff,
    fourier_coeff_on_eq_integral, zero_add, sub_zero, div_one, one_smul, one_smul],
  simp_rw [interval_integral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo],
  refine set_integral_congr measurable_set_Ioo (λ x hx, _),
  dsimp only,
  rw [periodized_bernoulli, continuous_map.coe_mk,
    add_circle.lift_Ico_zero_coe_apply ⟨hx.1.le, hx.2⟩],
end

lemma bernoulli_fourier_summable {k : ℕ} (hk : 2 ≤ k) :
  summable (λ n, -k.factorial / (2 * ↑π * I * n) ^ k : ℤ → ℂ) :=
begin
  have : ∀ (n : ℤ), -(k.factorial : ℂ) / (2 * π * I * n) ^ k
    = (-k.factorial / (2 * π * I) ^ k) * (1 / n ^ k),
  { intro n, rw [mul_one_div, div_div, ←mul_pow], },
  simp_rw this,
  apply summable.mul_left,
  rw ←summable_norm_iff,
  have : (λ (x : ℤ), ‖1 / (x:ℂ) ^ k‖) = (λ (x : ℤ), |1 / (x:ℝ) ^ k|),
  { ext1 x,
    rw [norm_eq_abs, ←complex.abs_of_real],
    congr' 1,
    norm_cast },
  simp_rw this,
  rw [summable_abs_iff],
  exact real.summable_one_div_int_pow (one_lt_two.trans_le hk),
end

lemma polylog_eval0 {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
  has_sum (λ n:ℤ, 1 / (n:ℂ) ^ k * @fourier 1 n x)
  (-(2 * π * I) ^ k / k.factorial * bernoulli_fun k x) :=
begin
  have := has_pointwise_sum_fourier_series_of_summable ((bernoulli_fourier_summable hk).congr
    (λ n, (fourier_coeff_bernoulli_eq hk n).symm)) x,
  have ev0 : periodized_bernoulli (_ : k ≠ 1) x = bernoulli_fun k x,
  { rw periodized_bernoulli,
    dsimp,
    exact add_circle.lift_Ico_zero_coe_apply hx, },
  rw ev0 at this,
  simp_rw [fourier_coeff_bernoulli_eq hk, smul_eq_mul] at this,
  convert this.mul_left ((-(2 * ↑π * I) ^ k) / (k.factorial : ℂ)),
  ext1 n,
  rw [←mul_assoc, mul_div, mul_neg, div_mul_cancel, neg_neg, mul_pow _ ↑n, ←div_div, div_self],
  { rw [ne.def, pow_eq_zero_iff', not_and_distrib],
    exact or.inl two_pi_I_ne_zero, },
  { exact nat.cast_ne_zero.mpr (nat.factorial_ne_zero _), },
end

end bernoulli_periodized

section cleanup
/-! This section is just reformulating the results in a nicer form. -/

lemma polylog_eval {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
  has_sum (λ n:ℕ, 1 / (n:ℂ) ^ k * (@fourier 1 n x + (-1) ^ k * @fourier 1 (-n) x))
  (-(2 * π * I) ^ k / k.factorial * bernoulli_fun k x) :=
begin
  convert (polylog_eval0 hk hx).sum_nat_of_sum_int',
  { ext1 n,
    rw [int.cast_neg, mul_add, ←mul_assoc],
    conv_rhs { rw [neg_eq_neg_one_mul, mul_pow, ←div_div] },
    congr' 2,
    rw [div_mul_eq_mul_div₀, one_mul],
    congr' 1,
    rw [eq_div_iff, ←mul_pow, ←neg_eq_neg_one_mul, neg_neg, one_pow],
    apply pow_ne_zero, rw neg_ne_zero, exact one_ne_zero, },
  { rw [int.cast_zero, zero_pow (by linarith : 0 < k), div_zero, zero_mul, add_zero] },
end

lemma polylog_eval_even0 {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
  has_sum (λ n:ℕ, 1 / (n:ℂ) ^ (2 * k) * (@fourier 1 n x + @fourier 1 (-n) x))
  ((-1) ^ (k + 1) * (2 * π) ^ (2 * k) / (2 * k).factorial * bernoulli_fun (2 * k) x) :=
begin
  convert (polylog_eval (by linarith : 2 ≤ 2 * k) hx),
  { ext1 n,
    rw [pow_mul (-1 : ℂ),neg_one_sq, one_pow, one_mul], },
  { rw [pow_add, pow_one],
    conv_rhs { rw [mul_pow], congr, congr, skip, rw [pow_mul, I_sq] },
    ring, }
end

lemma polylog_eval_even {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
  has_sum (λ n:ℕ, 1 / (n:ℝ) ^ (2 * k) * real.cos (2 * π * n * x))
  ((-1) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k).factorial *
  (polynomial.map (algebra_map ℚ ℝ) (polynomial.bernoulli (2 * k))).eval x) :=
begin
  convert ((has_sum_iff _ _).mp ((polylog_eval_even0 hk hx).div_const 2)).1,
  { ext1 n,
    convert (of_real_re _).symm,
    rw of_real_mul,rw ←mul_div, congr,
    { rw [of_real_div, of_real_one, of_real_pow], refl, },
    { rw [of_real_cos, of_real_mul, fourier_coe_apply, fourier_coe_apply, cos, of_real_one, div_one,
        div_one, of_real_mul, of_real_mul, of_real_bit0, of_real_one, int.cast_neg,
        int.cast_coe_nat, of_real_nat_cast],
      congr' 3,
      { ring }, { ring }, }, },
  { convert (of_real_re _).symm,
    rw [of_real_mul, of_real_div, of_real_div, of_real_mul, of_real_pow, of_real_pow, of_real_neg,
      of_real_nat_cast, of_real_mul, of_real_bit0, of_real_one],
    ring },
end

lemma polylog_eval_odd0 {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
  has_sum (λ n:ℕ, 1 / (n:ℂ) ^ (2 * k + 1) * (@fourier 1 n x - @fourier 1 (-n) x))
  ((-1)^(k + 1) * I * (2 * π)^(2 * k + 1) / (2 * k + 1).factorial * bernoulli_fun (2 * k + 1) x) :=
begin
  convert (polylog_eval (by linarith : 2 ≤ 2 * k + 1) hx),
  { ext1 n,
    rw [pow_add (-1: ℂ), pow_mul (-1 : ℂ), neg_one_sq, one_pow, one_mul, pow_one,
      ←neg_eq_neg_one_mul, ←sub_eq_add_neg], },
  { rw [pow_add, pow_one],
    conv_rhs { rw [mul_pow], congr, congr, skip, rw [pow_add, pow_one, pow_mul, I_sq] },
    ring, },
end

lemma polylog_eval_odd {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
  has_sum (λ n:ℕ, 1 / (n:ℝ) ^ (2 * k + 1) * real.sin (2 * π * n * x))
  ((-1) ^ (k + 1) * (2 * π) ^ (2 * k + 1) / 2 / (2 * k + 1).factorial *
  (polynomial.map (algebra_map ℚ ℝ) (polynomial.bernoulli (2 * k + 1))).eval x) :=
begin
  convert ((has_sum_iff _ _).mp ((polylog_eval_odd0 hk hx).div_const (2 * I))).1,
  { ext1 n,
    convert (of_real_re _).symm,
    rw of_real_mul,rw ←mul_div, congr,
    { rw [of_real_div, of_real_one, of_real_pow], refl, },
    { rw [of_real_sin, of_real_mul, fourier_coe_apply, fourier_coe_apply, sin, of_real_one, div_one,
        div_one, of_real_mul, of_real_mul, of_real_bit0, of_real_one, int.cast_neg,
        int.cast_coe_nat, of_real_nat_cast, ←div_div, div_I, div_mul_eq_mul_div₀, ←neg_div,
        ←neg_mul, neg_sub],
      congr' 4,
      { ring, }, { ring }, }, },
  { convert (of_real_re _).symm,
    rw [of_real_mul, of_real_div, of_real_div, of_real_mul, of_real_pow, of_real_pow, of_real_neg,
      of_real_nat_cast, of_real_mul, of_real_bit0, of_real_one,
      ←div_div, div_I, div_mul_eq_mul_div₀],
    have : ∀ (α β γ δ : ℂ), α * I * β / γ * δ * I = I ^ 2 * α * β / γ * δ := by { intros, ring },
    rw [this, I_sq],
    ring, },
end

lemma zeta_value {k : ℕ} (hk : 1 ≤ k) : has_sum (λ n:ℕ, 1 / (n:ℝ) ^ (2 * k))
  ((-1) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) * bernoulli (2 * k) / ((2 * k).factorial)) :=
begin
  convert polylog_eval_even hk (left_mem_Ico.mpr zero_lt_one),
  { ext1 n, rw [mul_zero, real.cos_zero, mul_one], },
  rw [polynomial.eval_zero_map, polynomial.bernoulli_eval_zero, eq_rat_cast],
  have : (2:ℝ) ^ (2 * k - 1) = (2:ℝ) ^ (2 * k) / 2,
  { rw eq_div_iff (two_ne_zero' ℝ),
    conv_lhs { congr, skip, rw ←pow_one (2:ℝ) },
    rw [←pow_add, nat.sub_add_cancel],
    linarith,  },
  rw [this, mul_pow],
  ring,
end

end cleanup

section examples

lemma zeta_two : has_sum (λ n:ℕ, 1 / (n : ℝ) ^ 2) (π ^ 2 / 6) :=
begin
  convert zeta_value (le_refl 1) using 1, rw mul_one,
  rw [bernoulli_eq_bernoulli'_of_ne_one (by dec_trivial : 2 ≠ 1), bernoulli'_two],
  norm_num, field_simp, ring,
end

lemma zeta_four : has_sum (λ n:ℕ, 1 / (n : ℝ) ^ 4) (π ^ 4 / 90) :=
begin
  convert zeta_value one_le_two using 1, norm_num,
  rw [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_four],
  norm_num, field_simp, ring, dec_trivial,
end

lemma bernoulli_three_eval_one_quarter : (polynomial.bernoulli 3).eval (1 / 4) = 3 / 64 :=
begin
  simp_rw [polynomial.bernoulli, finset.sum_range_succ, polynomial.eval_add,
    polynomial.eval_monomial],
  rw [finset.sum_range_zero, polynomial.eval_zero, zero_add, bernoulli_one],
  rw [bernoulli_eq_bernoulli'_of_ne_one zero_ne_one, bernoulli'_zero,
      bernoulli_eq_bernoulli'_of_ne_one (by dec_trivial : 2 ≠ 1), bernoulli'_two,
      bernoulli_eq_bernoulli'_of_ne_one (by dec_trivial : 3 ≠ 1), bernoulli'_three],
norm_num,
end

/-- Explicit formula for `L(χ, 3)`, where `χ` is the unique nontrivial Dirichlet character modulo 4.
-/
lemma L_function_mod_four_eval_three :
  has_sum (λ n:ℕ, (1 / (n:ℝ) ^ 3 * real.sin (π * n / 2))) (π ^ 3 / 32) :=
begin
  convert polylog_eval_odd (le_refl 1) (_ : 1 / 4 ∈ Ico (0:ℝ) 1),
  { ext1 n,
    norm_num,
    left,
    congr' 1,
    ring, },
  { have : (1 / 4 : ℝ) = (algebra_map ℚ ℝ) (1 / 4 : ℚ), by norm_num,
    rw [this, mul_pow, polynomial.eval_map, polynomial.eval₂_at_apply,
      (by dec_trivial : 2 * 1 + 1 = 3), bernoulli_three_eval_one_quarter],
    norm_num, field_simp, ring },
  { rw mem_Ico, split, linarith, linarith, },
end
end examples
