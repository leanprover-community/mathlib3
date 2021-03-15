/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Benjamin Davidson
-/
import measure_theory.interval_integral

/-!
# Integration of specific interval integrals

This file contains proofs of the integrals of various simple functions, including `pow`, `exp`,
`inv`/`one_div`, `sin`, `cos`, and `λ x, 1 / (1 + x^2)`.

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

lemma integral_sin_pow (n : ℕ) : ∫ x in 0..π, sin x ^ (n + 2) =
  ((n + 1) * ∫ x in 0..π, sin x ^ n) - (n + 1) * ∫ x in 0..π, sin x ^ (n + 2) :=
begin
  have h : (λ x, sin x ^ (n + 2)) = λ x, sin x ^ (n + 1) * sin x, { funext, ring },
  have hv : ∀ x ∈ interval 0 π, has_deriv_at (-cos) (sin x) x,
  { intros, convert (has_deriv_at_cos x).neg, rw neg_neg },
  have hu : ∀ x ∈ interval 0 π, has_deriv_at (λ x, sin x ^ (n + 1)) ((n + 1) * cos x * sin x ^ n) x,
  { intros,
    convert (has_deriv_at_pow (n + 1) (sin x)).comp x (has_deriv_at_sin x) using 1,
    simp [mul_right_comm], },
  have : (λ x, cos x * ((n + 1) * cos x * sin x ^ n)) = λ x, (↑n + 1) * (cos x ^ 2 * sin x ^ n),
  { funext, ring },
  conv_lhs { rw h },
  rw integral_mul_deriv_eq_deriv_mul hu hv _ _,
  { simp only [neg_mul_eq_neg_mul_symm, sin_zero, sin_pi, zero_mul, pi.neg_apply, sub_zero,
      add_eq_zero_iff, ne.def, zero_add, not_false_iff, one_ne_zero, integral_neg, and_false,
      zero_pow', sub_neg_eq_add, this, integral_const_mul (↑n + 1)],
    simp only [cos_square', sub_mul, mul_sub, one_mul, ← pow_add _ 2 n, add_comm 2 n],
    rw [integral_sub, mul_sub] },
  { exact ((continuous_pow n).comp continuous_sin).interval_integrable 0 π },
  { exact ((continuous_pow (n + 2)).comp continuous_sin).interval_integrable 0 π },
  { apply continuous.continuous_on, continuity },
  apply continuous.continuous_on, continuity,
end

lemma integral_sin_pow_succ_succ (n : ℕ) :
  ∫ x in 0..π, sin x ^ (n + 2) = (n + 1) / (n + 2) * ∫ x in 0..π, sin x ^ n :=
begin
  field_simp,
  have := eq_sub_iff_add_eq.mp (integral_sin_pow n),
  rwa [eq_div_iff, mul_comm, bit0, ← add_assoc, add_mul, one_mul, add_comm],
  norm_cast, norm_num,
end

theorem integral_sin_pow_odd (n : ℕ) :
  ∫ x in 0..π, sin x ^ (2 * n + 1) = 2 * ∏ i in finset.range n, (2 * i + 2) / (2 * i + 3) :=
begin
  induction n with k ih,
  { norm_num, },
  rw [finset.prod_range_succ, ← mul_assoc, mul_comm (2:ℝ) ((2 * k + 2) / (2 * k + 3)),
    mul_assoc, ← ih],
  have h₁ : 2 * k.succ + 1 = 2 * k + 1 + 2, { rw nat.succ_eq_add_one k, rw mul_add, rw mul_one },
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
  rcases nat.even_or_odd' n with ⟨k, h, h⟩,
  { rw [h, integral_sin_pow_even],
    refine mul_pos pi_pos (finset.prod_pos (λ n hn, div_pos _ _)),
    norm_cast, linarith, norm_cast, linarith },
  { rw [h, integral_sin_pow_odd],
    refine mul_pos (by norm_num) (finset.prod_pos (λ n hn, div_pos _ _)),
    norm_cast, linarith, norm_cast, linarith }
end

lemma integral_sin_pow_anti_mono (n : ℕ) :
  ∫ (x : ℝ) in 0..π, sin x ^ (n + 1) ≤ ∫ (x : ℝ) in 0..π, sin x ^ n :=
begin
  refine integral_mono_on _ _ pi_pos.le (λ x hx, _),
  { exact ((continuous_pow (n + 1)).comp continuous_sin).interval_integrable 0 π },
  { exact ((continuous_pow n).comp continuous_sin).interval_integrable 0 π },
  refine pow_le_pow_of_le_one _ (sin_le_one x) (nat.le_add_right n 1),
  rw interval_of_le pi_pos.le at hx,
  exact sin_nonneg_of_mem_Icc hx,
end

lemma integral_sin_pow_div_tendsto_one :
  tendsto (λ k, (∫ x in 0..π, sin x ^ (2 * k + 1)) / ∫ x in 0..π, sin x ^ (2 * k)) at_top (𝓝 1) :=
begin
  have h₃ : ∀ n, (∫ x in 0..π, sin x ^ (2 * n + 1)) / ∫ x in 0..π, sin x ^ (2 * n) ≤ 1 :=
    λ n, (div_le_one (integral_sin_pow_pos _)).mpr (integral_sin_pow_anti_mono _),
  have h₄ :
    ∀ n, (∫ x in 0..π, sin x ^ (2 * n + 1)) / ∫ x in 0..π, sin x ^ (2 * n) ≥ 2 * n / (2 * n + 1),
  { intro, cases n,
    { have : 0 ≤ (1 + 1) / π, exact div_nonneg (by norm_num) pi_pos.le,
      simp [this] },
    calc (∫ x in 0..π, sin x ^ (2 * n.succ + 1)) / ∫ x in 0..π, sin x ^ (2 * n.succ) ≥
      (∫ x in 0..π, sin x ^ (2 * n.succ + 1)) / ∫ x in 0..π, sin x ^ (2 * n + 1) :
      by { refine div_le_div (integral_sin_pow_pos _).le (le_refl _) (integral_sin_pow_pos _) _,
        convert integral_sin_pow_anti_mono (2 * n + 1) using 1 }
    ... = 2 * ↑(n.succ) / (2 * ↑(n.succ) + 1) :
      by { symmetry, rw [eq_div_iff, nat.succ_eq_add_one],
        convert (integral_sin_pow_succ_succ (2 * n + 1)).symm using 3,
        simp [mul_add], ring, simp [mul_add], ring,
        exact norm_num.ne_zero_of_pos  _ (integral_sin_pow_pos (2 * n + 1)) } },
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le _ _ (λ n, (h₄ n).le) (λ n, (h₃ n)),
  { refine metric.tendsto_at_top.mpr (λ ε hε, ⟨nat_ceil (1 / ε), λ n hn, _⟩),
    have h : (2:ℝ) * n / (2 * n + 1) - 1 = -1 / (2 * n + 1),
    { conv_lhs { congr, skip, rw ← @div_self _ _ ((2:ℝ) * n + 1) (by { norm_cast, linarith }), },
      rw [← sub_div, ← sub_sub, sub_self, zero_sub] },
    have hpos : (0:ℝ) < 2 * n + 1, { norm_cast, norm_num },
    rw [real.dist_eq, h, abs_div, abs_neg, abs_one, abs_of_pos hpos, one_div_lt hpos hε],
    calc 1 / ε ≤ nat_ceil (1 / ε) : le_nat_ceil _
          ... ≤ n : by exact_mod_cast hn.le
          ... < 2 * n + 1 : by { norm_cast, linarith } },
  exact tendsto_const_nhds,
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
