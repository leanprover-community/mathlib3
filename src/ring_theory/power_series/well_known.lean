/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import ring_theory.power_series.basic
import data.nat.parity

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

@[simp] lemma map_exp : map (f : A →+* A') (exp A) = exp A' := by { ext, simp }

@[simp] lemma map_sin : map f (sin A) = sin A' := by { ext, simp [sin, apply_ite f] }

@[simp] lemma map_cos : map f (cos A) = cos A' := by { ext, simp [cos, apply_ite f] }

open finset nat

variables (B : Type*) [comm_ring B] [algebra ℚ B]

noncomputable def eval_mul_hom (a : B) : power_series B →+* power_series B :=
{
  to_fun :=   λ f, mk $ λ n, a^n * (coeff B n f),
  map_zero' := by {simp, ext, simp, },
  map_one' := by { simp, ext1, simp, split_ifs, rw [h, pow_zero], refl, },
  map_add' := by {intros, ext, norm_num, rw mul_add, },
  map_mul' := by {intros, ext, rw coeff_mul, simp, rw coeff_mul, rw mul_sum, apply sum_congr rfl,
            norm_num, intros b c H, rw <-H, rw pow_add, rw mul_assoc, rw ←mul_assoc (a^c) _ _,
            rw mul_comm (a^c) _, rw mul_assoc _ (a^c) _, ring, },
}

theorem exp_mul_exp_eq_exp_add (a b : B) :
  (eval_mul_hom B a (exp B)) * (eval_mul_hom B b (exp B)) = (eval_mul_hom B (a + b) (exp B)) :=
begin
  ext,
  rw [coeff_mul, exp, eval_mul_hom, eval_mul_hom, eval_mul_hom],
  simp only [coeff_mk, coe_mk, factorial],
  { rw sum_antidiagonal_eq_sum_range_succ_mk, simp only [factorial], rw add_pow,
  rw sum_mul, apply sum_congr, refl, rintros x hx,
  rw mul_assoc (a^x * b ^ (n - x)) _ _, rw mul_assoc (a^x) _ _, rw ←mul_assoc _  (b ^ (n - x)) _,
  rw mul_comm _ (b^(n - x)), rw ←mul_assoc (a^x) _ _, rw ←mul_assoc (a^x) _ _,
  suffices f : (algebra_map ℚB) (1 / ↑(x.factorial)) * (algebra_map ℚ B) (1 / ↑((n - x).factorial))
   = (↑(n.choose x) * (algebra_map ℚ B) (1 / ↑(n.factorial))),
  { rw ←f, rw mul_assoc, },
  rw ←map_nat_cast (algebra_map ℚ B) (n.choose x), rw ←map_mul, rw ←map_mul,
  refine ring_hom.congr_arg _ _, rw mul_one_div ↑(n.choose x) _, rw one_div_mul_one_div,
   symmetry, rw div_eq_iff, rw div_mul_eq_mul_div, rw one_mul, rw choose_eq_factorial_div_factorial,
   norm_cast, rw cast_dvd_char_zero,
   { apply factorial_mul_factorial_dvd_factorial (mem_range_succ_iff.1 hx), },
   { apply mem_range_succ_iff.1 hx, },
   { rintros h, apply factorial_ne_zero n, rw cast_eq_zero.1 h, },
 },
end

lemma eval_mul_hom_zero (f : power_series B) :
  eval_mul_hom B 0 f = (C B ((constant_coeff B) f) ) :=
begin
  rw eval_mul_hom, simp, ext, simp, rw power_series.coeff_C, split_ifs,
  rw h, simp,
  rw zero_pow' n h, rw zero_mul,
end

lemma eval_mul_hom_one (f : power_series B) :
  eval_mul_hom B 1 f = f :=
begin
  rw eval_mul_hom, simp, ext, simp,
end

noncomputable def eval_neg_hom : power_series B →+* power_series B :=
  eval_mul_hom B (-1 : B)

@[simp] lemma constant_coeff_exp : constant_coeff B (exp B) = 1 := sorry

theorem exp_mul_exp_neg_eq_one : (exp B) * (eval_neg_hom B (exp B)) = 1 :=
begin
  rw eval_neg_hom,
  conv_lhs { congr, rw ←eval_mul_hom_one B (exp B), },
  rw exp_mul_exp_eq_exp_add, simp, rw eval_mul_hom_zero, simp,
end

@[simp] lemma eval_neg_hom_X : eval_neg_hom ℚ X = -X :=
begin
  rw eval_neg_hom, ext, simp, rw coeff_X, split_ifs, rw h, rw eval_mul_hom, simp,
  rw eval_mul_hom, simp, right, rw coeff_X, split_ifs, refl,
end

end field

end power_series
