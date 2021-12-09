/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import ring_theory.power_series.basic
import data.nat.parity
import algebra.big_operators.nat_antidiagonal

/-!
# Definition of well-known power series

In this file we define the following power series:

* `power_series.inv_units_sub`: given `u : units R`, this is the series for `1 / (u - x)`.
  It is given by `∑ n, x ^ n /ₚ u ^ (n + 1)`.

* `power_series.sin`, `power_series.cos`, `power_series.exp` : power series for sin, cosine, and
  exponential functions.
-/

namespace power_series

section ring

variables {R S : Type*} [ring R] [ring S]

/-- The power series for `1 / (u - x)`. -/
def inv_units_sub (u : units R) : power_series R := mk $ λ n, 1 /ₚ u ^ (n + 1)

@[simp] lemma coeff_inv_units_sub (u : units R) (n : ℕ) :
  coeff R n (inv_units_sub u) = 1 /ₚ u ^ (n + 1) :=
coeff_mk _ _

@[simp] lemma constant_coeff_inv_units_sub (u : units R) :
  constant_coeff R (inv_units_sub u) = 1 /ₚ u :=
by rw [← coeff_zero_eq_constant_coeff_apply, coeff_inv_units_sub, zero_add, pow_one]

@[simp] lemma inv_units_sub_mul_X (u : units R) :
  inv_units_sub u * X = inv_units_sub u * C R u - 1 :=
begin
  ext (_|n),
  { simp },
  { simp [n.succ_ne_zero, pow_succ] }
end

@[simp] lemma inv_units_sub_mul_sub (u : units R) : inv_units_sub u * (C R u - X) = 1 :=
by simp [mul_sub, sub_sub_cancel]

lemma map_inv_units_sub (f : R →+* S) (u : units R) :
  map f (inv_units_sub u) = inv_units_sub (units.map (f : R →* S) u) :=
by { ext, simp [← monoid_hom.map_pow] }

end ring

section field

variables (A A' : Type*) [ring A] [ring A'] [algebra ℚ A] [algebra ℚ A']

open_locale nat

/-- Power series for the exponential function at zero. -/
def exp : power_series A := mk $ λ n, algebra_map ℚ A (1 / n!)

/-- Power series for the sine function at zero. -/
def sin : power_series A :=
mk $ λ n, if even n then 0 else algebra_map ℚ A ((-1) ^ (n / 2) / n!)

/-- Power series for the cosine function at zero. -/
def cos : power_series A :=
mk $ λ n, if even n then algebra_map ℚ A ((-1) ^ (n / 2) / n!) else 0

variables {A A'} (n : ℕ) (f : A →+* A')

@[simp] lemma coeff_exp : coeff A n (exp A) = algebra_map ℚ A (1 / n!) := coeff_mk _ _

@[simp] lemma constant_coeff_exp : constant_coeff A (exp A) = 1 :=
by { rw [← coeff_zero_eq_constant_coeff_apply, coeff_exp], simp }

@[simp] lemma map_exp : map (f : A →+* A') (exp A) = exp A' := by { ext, simp }

@[simp] lemma map_sin : map f (sin A) = sin A' := by { ext, simp [sin, apply_ite f] }

@[simp] lemma map_cos : map f (cos A) = cos A' := by { ext, simp [cos, apply_ite f] }

end field

open ring_hom
open finset nat

variables {A : Type*} [comm_ring A]

/-- Shows that $e^{aX} * e^{bX} = e^{(a + b)X}$ -/
theorem exp_mul_exp_eq_exp_add [algebra ℚ A] (a b : A) :
  rescale a (exp A) * rescale b (exp A) = rescale (a + b) (exp A) :=
begin
  ext,
  simp only [coeff_mul, exp, rescale, coeff_mk, coe_mk, factorial,
    nat.sum_antidiagonal_eq_sum_range_succ_mk, add_pow, sum_mul],
  apply sum_congr rfl,
  rintros x hx,
  suffices : a^x * b^(n - x) * (algebra_map ℚ A (1 / ↑(x.factorial)) * algebra_map ℚ A
    (1 / ↑((n - x).factorial))) =
    a^x * b^(n - x) * ((↑(n.choose x) * (algebra_map ℚ A) (1 / ↑(n.factorial)))),
  { convert this using 1; ring },
  congr' 1,
  rw [←map_nat_cast (algebra_map ℚ A) (n.choose x), ←map_mul, ←map_mul],
  refine ring_hom.congr_arg _ _,
  rw [mul_one_div ↑(n.choose x) _, one_div_mul_one_div],
  symmetry,
  rw [div_eq_iff, div_mul_eq_mul_div, one_mul, choose_eq_factorial_div_factorial],
  norm_cast,
  rw cast_dvd_char_zero,
  { apply factorial_mul_factorial_dvd_factorial (mem_range_succ_iff.1 hx), },
  { apply mem_range_succ_iff.1 hx, },
  { rintros h, apply factorial_ne_zero n, rw cast_eq_zero.1 h, },
end

/-- Shows that $e^{x} * e^{-x} = 1$ -/
theorem exp_mul_exp_neg_eq_one [algebra ℚ A] : exp A * eval_neg_hom (exp A) = 1 :=
by convert exp_mul_exp_eq_exp_add (1 : A) (-1); simp

/-- Shows that $(e^{X})^k = e^{kX}$. -/
theorem exp_pow_eq_rescale_exp [algebra ℚ A] (k : ℕ) : (exp A)^k = rescale (k : A) (exp A) :=
begin
  induction k with k h,
  { simp only [rescale_zero, constant_coeff_exp, function.comp_app, map_one, cast_zero,
      pow_zero, coe_comp], },
  simpa only [succ_eq_add_one, cast_add, ←exp_mul_exp_eq_exp_add (k : A), ←h, cast_one,
    id_apply, rescale_one] using pow_succ' (exp A) k,
end

/-- Shows that
$\sum_{k = 0}^{n - 1} (e^{X})^k = \sum_{p = 0}^{\infty} \sum_{k = 0}^{n - 1} \frac{k^p}{p!}X^p$. -/
theorem exp_pow_sum [algebra ℚ A] (n : ℕ) : (finset.range n).sum (λ k, (exp A)^k) =
  power_series.mk (λ p, (finset.range n).sum (λ k, k^p * algebra_map ℚ A p.factorial⁻¹)) :=
begin
  simp only [exp_pow_eq_rescale_exp, rescale],
  ext,
  simp only [one_div, coeff_mk, coe_mk, coeff_exp, factorial, linear_map.map_sum],
end

end power_series
