/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import number_theory.bernoulli_polynomials
import analysis.special_functions.integrals
import measure_theory.integral.interval_integral
import analysis.fourier.add_circle

/-!
# Critical values of the Riemann zeta function

In this file we evaluate the Fourier coefficients of Bernoulli polynomials on the interval `[0, 1]`.
In a future iteration this will be used to evaluate critical values of the Riemann zeta function
(and other Dirichlet L-functions).
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
