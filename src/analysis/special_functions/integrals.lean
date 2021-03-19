/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
import measure_theory.interval_integral

/-!
# Integration of specific interval integrals

This file contains proofs of the integrals of various simple functions, including `pow`, `exp`,
`inv`/`one_div`, `sin`, `cos`, and `λ x, 1 / (1 + x^2)`.

There are also facts about more complicated integrals:
* `sin x ^ n`: We prove a recursive formula for `sin x ^ (n + 2)` in terms of `sin x ^ n`,
  along with explicit product formulas for even and odd `n`.

With these lemmas, many simple integrals can be computed by `simp` or `norm_num`. Scroll to the
bottom of the file for examples.

This file is incomplete; we are working on expanding it.
-/

open real set interval_integral filter
open_locale real big_operators topological_space
variables {a b : ℝ}

namespace interval_integral
variable {f : ℝ → ℝ}

@[simp]
lemma integral_const_mul (c : ℝ) : ∫ x in a..b, c * f x = c * ∫ x in a..b, f x :=
integral_smul c

@[simp]
lemma integral_mul_const (c : ℝ) : ∫ x in a..b, f x * c = (∫ x in a..b, f x) * c :=
by simp only [mul_comm, integral_const_mul]

@[simp]
lemma integral_div (c : ℝ) : ∫ x in a..b, f x / c = (∫ x in a..b, f x) / c :=
integral_mul_const c⁻¹

@[simp]
lemma integral_pow (n : ℕ) : ∫ x in a..b, x ^ n = (b^(n+1) - a^(n+1)) / (n + 1) :=
begin
  have hderiv : deriv (λ x : ℝ, x^(n + 1) / (n + 1)) = λ x, x ^ n,
  { have hne : (n + 1 : ℝ) ≠ 0 := by exact_mod_cast nat.succ_ne_zero n,
    ext,
    simp [mul_div_assoc, mul_div_cancel' _ hne] },
  rw integral_deriv_eq_sub' _ hderiv;
  norm_num [div_sub_div_same, (continuous_pow n).continuous_on],
end

@[simp]
lemma integral_id : ∫ x in a..b, x = (b^2 - a^2) / 2 :=
by simpa using integral_pow 1

@[simp]
lemma integral_one : ∫ x in a..b, (1:ℝ) = b - a :=
by simp

@[simp]
lemma integral_exp : ∫ x in a..b, exp x = exp b - exp a :=
by rw integral_deriv_eq_sub'; norm_num [continuous_exp.continuous_on]

@[simp]
lemma integral_inv (h : (0:ℝ) ∉ interval a b) : ∫ x in a..b, x⁻¹ = log (b / a) :=
begin
  have h' := λ x hx, ne_of_mem_of_not_mem hx h,
  rw [integral_deriv_eq_sub' _ deriv_log' (λ x hx, differentiable_at_log (h' x hx))
        (continuous_on_inv'.mono (subset_compl_singleton_iff.mpr h)),
      log_div (h' b right_mem_interval) (h' a left_mem_interval)],
end

@[simp]
lemma integral_inv_of_pos (ha : 0 < a) (hb : 0 < b) : ∫ x in a..b, x⁻¹ = log (b / a) :=
integral_inv $ not_mem_interval_of_lt ha hb

@[simp]
lemma integral_inv_of_neg (ha : a < 0) (hb : b < 0) : ∫ x in a..b, x⁻¹ = log (b / a) :=
integral_inv $ not_mem_interval_of_gt ha hb

lemma integral_one_div (h : (0:ℝ) ∉ interval a b) : ∫ x : ℝ in a..b, 1/x = log (b / a) :=
by simp only [one_div, integral_inv h]

lemma integral_one_div_of_pos (ha : 0 < a) (hb : 0 < b) : ∫ x : ℝ in a..b, 1/x = log (b / a) :=
by simp only [one_div, integral_inv_of_pos ha hb]

lemma integral_one_div_of_neg (ha : a < 0) (hb : b < 0) : ∫ x : ℝ in a..b, 1/x = log (b / a) :=
by simp only [one_div, integral_inv_of_neg ha hb]

@[simp]
lemma integral_sin : ∫ x in a..b, sin x = cos a - cos b :=
by rw integral_deriv_eq_sub' (λ x, -cos x); norm_num [continuous_on_sin]

lemma integral_sin_pow_aux (n : ℕ) : ∫ x in 0..π, sin x ^ (n + 2) =
  ((n + 1) * ∫ x in 0..π, sin x ^ n) - (n + 1) * ∫ x in 0..π, sin x ^ (n + 2) :=
begin
  have hv : ∀ x ∈ interval 0 π, has_deriv_at (-cos) (sin x) x,
  { intros, convert (has_deriv_at_cos x).neg, rw neg_neg },
  have hu : ∀ x ∈ interval 0 π, has_deriv_at (λ x, sin x ^ (n + 1)) ((n + 1) * cos x * sin x ^ n) x,
  { intros,
    convert (has_deriv_at_pow (n + 1) (sin x)).comp x (has_deriv_at_sin x) using 1,
    simp [mul_right_comm], },
  calc ∫ (x : ℝ) in 0..π, sin x ^ (n + 2)
      = ∫ (x : ℝ) in 0..π, sin x ^ (n + 1) * sin x : by { congr, ext, ring }
  ... = ∫ (x : ℝ) in 0..π, cos x * (λ (x : ℝ), (↑n + 1) * cos x * sin x ^ n) x : by
  { simp [integral_mul_deriv_eq_deriv_mul hu hv (by continuity : continuous _).continuous_on
      (by continuity : continuous _).continuous_on] }
  ... = (↑n + 1) * ∫ (x : ℝ) in 0..π, cos x ^ 2 * sin x ^ n : by
  { rw ← integral_const_mul, congr, ext, simp only, ring }
  ... = (↑n + 1) * ∫ (x : ℝ) in 0..π, sin x ^ n - sin x ^ (n + 2) : by
  { simp [integral_const_mul, cos_square', sub_mul, ← pow_add, add_comm] }
  ... = _ - _ : by { rw [integral_sub, mul_sub],
    { exact ((continuous_pow n).comp continuous_sin).interval_integrable 0 π },
    { exact ((continuous_pow (n + 2)).comp continuous_sin).interval_integrable 0 π } },
end

lemma integral_sin_pow_succ_succ (n : ℕ) :
  ∫ x in 0..π, sin x ^ (n + 2) = (n + 1) / (n + 2) * ∫ x in 0..π, sin x ^ n :=
begin
  have : (n:ℝ) + 2 ≠ 0 := by { norm_cast, norm_num },
  field_simp,
  convert eq_sub_iff_add_eq.mp (integral_sin_pow_aux n),
  ring
end

theorem integral_sin_pow_odd (n : ℕ) :
  ∫ x in 0..π, sin x ^ (2 * n + 1) = 2 * ∏ i in finset.range n, (2 * i + 2) / (2 * i + 3) :=
begin
  induction n with k ih,
  { norm_num, },
  rw [finset.prod_range_succ, ← mul_assoc, mul_comm (2:ℝ) ((2 * k + 2) / (2 * k + 3)),
    mul_assoc, ← ih],
  have h₁ : 2 * k.succ + 1 = 2 * k + 1 + 2, { ring },
  have h₂ : (2:ℝ) * k + 1 + 1 = 2 * k + 2, { norm_cast, },
  have h₃ : (2:ℝ) * k + 1 + 2 = 2 * k + 3, { norm_cast, },
  simp [h₁, h₂, h₃, integral_sin_pow_succ_succ (2 * k + 1)]
end

theorem integral_sin_pow_even (n : ℕ) :
  ∫ x in 0..π, sin x ^ (2 * n) = π * ∏ i in finset.range n, (2 * i + 1) / (2 * i + 2) :=
begin
  induction n with k ih,
  { norm_num, },
  rw [finset.prod_range_succ, ← mul_assoc, mul_comm π ((2 * k + 1) / (2 * k + 2)), mul_assoc, ← ih],
  simp [nat.succ_eq_add_one, mul_add, mul_one, integral_sin_pow_succ_succ _],
end

lemma integral_sin_pow_pos (n : ℕ) : 0 < ∫ x in 0..π, sin x ^ n :=
begin
  rcases nat.even_or_odd' n with ⟨k, h, h⟩;
  simp only [h, integral_sin_pow_even, integral_sin_pow_odd];
  refine mul_pos (by norm_num [pi_pos]) (finset.prod_pos (λ n hn, div_pos _ _));
  norm_cast;
  linarith
end

@[simp]
lemma integral_cos : ∫ x in a..b, cos x = sin b - sin a :=
by rw integral_deriv_eq_sub'; norm_num [continuous_on_cos]

@[simp]
lemma integral_inv_one_add_sq : ∫ x : ℝ in a..b, (1 + x^2)⁻¹ = arctan b - arctan a :=
begin
  simp only [← one_div],
  refine integral_deriv_eq_sub' _ _ _ (continuous_const.div _ (λ x, _)).continuous_on;
  norm_num,
  { continuity },
  { nlinarith },
end

lemma integral_one_div_one_add_sq : ∫ x : ℝ in a..b, 1 / (1 + x^2) = arctan b - arctan a :=
by simp

end interval_integral
