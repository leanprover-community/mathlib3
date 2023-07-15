/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import analysis.special_functions.exponential
/-!
# Trigonometric functions as sums of infinite series

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we express trigonometric functions in terms of their series expansion.

## Main results

* `complex.has_sum_cos`, `complex.tsum_cos`: `complex.cos` as the sum of an infinite series.
* `real.has_sum_cos`, `real.tsum_cos`: `real.cos` as the sum of an infinite series.
* `complex.has_sum_sin`, `complex.tsum_sin`: `complex.sin` as the sum of an infinite series.
* `real.has_sum_sin`, `real.tsum_sin`: `real.sin` as the sum of an infinite series.
-/

open_locale nat

/-! ### `cos` and `sin` for `ℝ` and `ℂ` -/

section sin_cos

lemma complex.has_sum_cos' (z : ℂ) :
  has_sum (λ n : ℕ, (z * complex.I) ^ (2 * n) / ↑(2 * n)!) (complex.cos z) :=
begin
  rw [complex.cos, complex.exp_eq_exp_ℂ],
  have := ((exp_series_div_has_sum_exp ℂ (z * complex.I)).add
          (exp_series_div_has_sum_exp ℂ (-z * complex.I))).div_const 2,
  replace := ((nat.div_mod_equiv 2)).symm.has_sum_iff.mpr this,
  dsimp [function.comp] at this,
  simp_rw [←mul_comm 2 _] at this,
  refine this.prod_fiberwise (λ k, _),
  dsimp only,
  convert has_sum_fintype (_ : fin 2 → ℂ) using 1,
  rw fin.sum_univ_two,
  simp_rw [fin.coe_zero, fin.coe_one, add_zero, pow_succ', pow_mul,
    mul_pow, neg_sq, ←two_mul, neg_mul, mul_neg, neg_div, add_right_neg, zero_div, add_zero,
    mul_div_cancel_left _ (two_ne_zero : (2 : ℂ) ≠ 0)],
end

lemma complex.has_sum_sin' (z : ℂ) :
  has_sum (λ n : ℕ, (z * complex.I) ^ (2 * n + 1) / ↑(2 * n + 1)! / complex.I) (complex.sin z) :=
begin
  rw [complex.sin, complex.exp_eq_exp_ℂ],
  have := (((exp_series_div_has_sum_exp ℂ (-z * complex.I)).sub
          (exp_series_div_has_sum_exp ℂ (z * complex.I))).mul_right complex.I).div_const 2,
  replace := ((nat.div_mod_equiv 2)).symm.has_sum_iff.mpr this,
  dsimp [function.comp] at this,
  simp_rw [←mul_comm 2 _] at this,
  refine this.prod_fiberwise (λ k, _),
  dsimp only,
  convert has_sum_fintype (_ : fin 2 → ℂ) using 1,
  rw fin.sum_univ_two,
  simp_rw [fin.coe_zero, fin.coe_one, add_zero, pow_succ', pow_mul,
    mul_pow, neg_sq, sub_self, zero_mul, zero_div, zero_add,
    neg_mul, mul_neg, neg_div, ← neg_add', ←two_mul, neg_mul, neg_div, mul_assoc,
    mul_div_cancel_left _ (two_ne_zero : (2 : ℂ) ≠ 0), complex.div_I],
end

/-- The power series expansion of `complex.cos`. -/
lemma complex.has_sum_cos (z : ℂ) :
  has_sum (λ n : ℕ, ((-1) ^ n) * z ^ (2 * n) / ↑(2 * n)!) (complex.cos z) :=
begin
  convert complex.has_sum_cos' z using 1,
  simp_rw [mul_pow, pow_mul, complex.I_sq, mul_comm]
end

/-- The power series expansion of `complex.sin`. -/
lemma complex.has_sum_sin (z : ℂ) :
  has_sum (λ n : ℕ, ((-1) ^ n) * z ^ (2 * n + 1) / ↑(2 * n + 1)!) (complex.sin z) :=
begin
  convert complex.has_sum_sin' z using 1,
  simp_rw [mul_pow, pow_succ', pow_mul, complex.I_sq, ←mul_assoc,
    mul_div_assoc, div_right_comm, div_self complex.I_ne_zero, mul_comm _ ((-1 : ℂ)^_), mul_one_div,
    mul_div_assoc, mul_assoc]
end

lemma complex.cos_eq_tsum' (z : ℂ) :
  complex.cos z = ∑' n : ℕ, (z * complex.I) ^ (2 * n) / ↑(2 * n)! :=
(complex.has_sum_cos' z).tsum_eq.symm

lemma complex.sin_eq_tsum' (z : ℂ) :
  complex.sin z = ∑' n : ℕ, (z * complex.I) ^ (2 * n + 1) / ↑(2 * n + 1)! / complex.I :=
(complex.has_sum_sin' z).tsum_eq.symm

lemma complex.cos_eq_tsum (z : ℂ) :
  complex.cos z = ∑' n : ℕ, ((-1) ^ n) * z ^ (2 * n) / ↑(2 * n)! :=
(complex.has_sum_cos z).tsum_eq.symm

lemma complex.sin_eq_tsum (z : ℂ) :
  complex.sin z = ∑' n : ℕ, ((-1) ^ n) * z ^ (2 * n + 1) / ↑(2 * n + 1)! :=
(complex.has_sum_sin z).tsum_eq.symm

/-- The power series expansion of `real.cos`. -/
lemma real.has_sum_cos (r : ℝ) :
  has_sum (λ n : ℕ, ((-1) ^ n) * r ^ (2 * n) / ↑(2 * n)!) (real.cos r) :=
by exact_mod_cast complex.has_sum_cos r

/-- The power series expansion of `real.sin`. -/
lemma real.has_sum_sin (r : ℝ) :
  has_sum (λ n : ℕ, ((-1) ^ n) * r ^ (2 * n + 1) / ↑(2 * n + 1)!) (real.sin r) :=
by exact_mod_cast complex.has_sum_sin r

lemma real.cos_eq_tsum (r : ℝ) :
  real.cos r = ∑' n : ℕ, ((-1) ^ n) * r ^ (2 * n) / ↑(2 * n)! :=
(real.has_sum_cos r).tsum_eq.symm

lemma real.sin_eq_tsum (r : ℝ) :
  real.sin r = ∑' n : ℕ, ((-1) ^ n) * r ^ (2 * n + 1) / ↑(2 * n + 1)! :=
(real.has_sum_sin r).tsum_eq.symm

end sin_cos
