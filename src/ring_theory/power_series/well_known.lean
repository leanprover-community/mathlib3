/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
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

@[simp] lemma constant_coeff_exp : constant_coeff A (exp A) = 1 := ring_hom.map_one _

@[simp] lemma map_exp : map (f : A →+* A') (exp A) = exp A' := by { ext, simp }

@[simp] lemma map_sin : map f (sin A) = sin A' := by { ext, simp [sin, apply_ite f] }

@[simp] lemma map_cos : map f (cos A) = cos A' := by { ext, simp [cos, apply_ite f] }

end field

open ring_hom
open finset nat

variables (A : Type*) [comm_ring A]

noncomputable def eval_mul_hom (a : A) : power_series A →+* power_series A :=
{ to_fun :=   λ f, mk $ λ n, a^n * (coeff A n f),
  map_zero' := by { ext, simp only [linear_map.map_zero, coeff_mk, mul_zero], },
  map_one' := by { ext1, simp only [mul_boole, coeff_mk, coeff_one], split_ifs,
                rw [h, pow_zero], refl, },
  map_add' := by {intros, ext, norm_num, rw mul_add, },
  map_mul' := by {intros, ext, rw [coeff_mul, coeff_mk, coeff_mul, finset.mul_sum],
                apply sum_congr rfl, norm_num, intros b c H, rw [<-H, pow_add], ring, }, }

/-- Shows that `e^(aX) * e^(bX) = e^((a + b)X) ` -/
theorem exp_mul_exp_eq_exp_add [algebra ℚ A] (a b : A) :
  (eval_mul_hom A a (exp A)) * (eval_mul_hom A b (exp A)) = (eval_mul_hom A (a + b) (exp A)) :=
begin
  ext, rw [coeff_mul, exp, eval_mul_hom, eval_mul_hom, eval_mul_hom],
  simp only [coeff_mk, coe_mk, factorial], rw nat.sum_antidiagonal_eq_sum_range_succ_mk,
  simp only [factorial], rw [add_pow, sum_mul], apply sum_congr, { refl },
  { rintros x hx,
    rw [mul_assoc (a^x * b ^ (n - x)) _ _, mul_assoc (a^x) _ _, ←mul_assoc _  (b ^ (n - x)) _,
    mul_comm _ (b^(n - x)), ←mul_assoc (a^x) _ _, ←mul_assoc (a^x) _ _],
    suffices f : (algebra_map ℚ A) (1 / ↑(x.factorial)) * (algebra_map ℚ A)
     (1 / ↑((n - x).factorial)) = (↑(n.choose x) * (algebra_map ℚ A) (1 / ↑(n.factorial))),
      { rw [←f, mul_assoc], },
    rw [←map_nat_cast (algebra_map ℚ A) (n.choose x), ←map_mul, ←map_mul],
    refine ring_hom.congr_arg _ _, rw [mul_one_div ↑(n.choose x) _, one_div_mul_one_div],
    symmetry, rw [div_eq_iff, div_mul_eq_mul_div, one_mul, choose_eq_factorial_div_factorial],
    norm_cast, rw cast_dvd_char_zero,
    { apply factorial_mul_factorial_dvd_factorial (mem_range_succ_iff.1 hx), },
    { apply mem_range_succ_iff.1 hx, },
    { rintros h, apply factorial_ne_zero n, rw cast_eq_zero.1 h, },
  },
end

lemma eval_mul_hom_zero [algebra ℚ A] (f : power_series A) :
  eval_mul_hom A 0 f = (C A ((constant_coeff A) f) ) :=
begin
  rw [eval_mul_hom, coe_mk], ext, rw [coeff_mk, power_series.coeff_C], split_ifs,
  { rw h, simp only [one_mul, coeff_zero_eq_constant_coeff, pow_zero], },
  { rw [zero_pow' n h, zero_mul], },
end

lemma eval_mul_hom_one [algebra ℚ A] (f : power_series A) :
  eval_mul_hom A 1 f = f :=
  by { rw eval_mul_hom, ext, simp only [one_pow, coeff_mk, one_mul, coe_mk], }

noncomputable def eval_neg_hom : power_series A →+* power_series A :=
  eval_mul_hom A (-1 : A)

/-- Shows that `e^{x} * e^{-x} = 1` -/
theorem exp_mul_exp_neg_eq_one [algebra ℚ A] : (exp A) * (eval_neg_hom A (exp A)) = 1 :=
begin
  rw eval_neg_hom,
  conv_lhs { congr, rw ←eval_mul_hom_one A (exp A), },
  rw exp_mul_exp_eq_exp_add, simp, rw eval_mul_hom_zero, simp,
end

@[simp] lemma eval_neg_hom_X : eval_neg_hom A X = -X :=
begin
  rw eval_neg_hom, ext, simp only [linear_map.map_neg], rw coeff_X, split_ifs,
  { rw [h, eval_mul_hom], simp only [coeff_mk, mul_one, coe_mk, coeff_one_X, pow_one], },
  { rw eval_mul_hom, simp, suffices f : (coeff A n) X = 0, {rw f, rw mul_zero,},
    rw coeff_X, split_ifs, refl, },
end

end power_series
