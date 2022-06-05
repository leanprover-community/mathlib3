/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import number_theory.bernoulli_polynomials
import analysis.fourier

/-!
# Critical values of the Riemann zeta function

In this file we give explicit evaluations of the sums `ζ(k) = ∑ (n : ℕ) 1 / n ^ k` for positive even
integers `k`.
-/

open_locale real complex_conjugate classical
open real complex measure_theory algebra submodule set interval_integral

noncomputable theory

section baselproblem

/-! ### The Basel problem: evaluating `∑ 1 / n ^ 2` using Parseval's formula -/

def B1 (x : ℝ) : ℂ := x - π

lemma B1_mem_Lp : mem_ℒp B1 2 fourier_line.μ₀ :=
begin
  have : continuous B1,
  { rw continuous_iff_continuous_at,
    intro x, refine continuous_at.sub _ continuous_at_const,
    exact complex.continuous_of_real.continuous_at },
  rw [mem_ℒp_two_iff_integrable_sq_norm, ←integrable_on, ←integrable_on_Icc_iff_integrable_on_Ioc],
  apply continuous.integrable_on_Icc,
  exact (continuous_norm.comp this).pow 2,
  exact this.ae_strongly_measurable,
end

lemma norm_B1 : 1 / (2 * π) * ∫ x in 0..(2 * π), ∥B1 x∥ ^ 2 = π ^ 2 / 3 :=
begin
  dsimp only [B1],
  simp_rw [complex.norm_eq_abs, ←of_real_sub, abs_of_real, _root_.sq_abs, sub_sq],
  rw interval_integral.integral_add,
  rw interval_integral.integral_sub,
  simp only [integral_pow, zero_pow', ne.def, nat.succ_ne_zero, not_false_iff,
    sub_zero, nat.cast_bit0, nat.cast_one, integral_mul_const, integral_const_mul, integral_id,
    interval_integral.integral_const, id.smul_eq_mul],
  norm_num, field_simp [two_pi_pos.ne'], ring,
  all_goals { apply continuous.interval_integrable, continuity },
end

lemma coeff_B1 (n : ℤ) : 1 / (2 * (π : ℂ)) * ∫ x in 0..(2 * π), exp (-n * I * x) * B1 x = I / n :=
begin
  dsimp only [B1],
  rcases eq_or_ne n 0 with hn|hn,
  { rw hn,
    simp only [one_div, mul_inv_rev, int.cast_zero, neg_zero', zero_mul, complex.exp_zero, one_mul,
      div_zero, mul_eq_zero, inv_eq_zero, of_real_eq_zero, bit0_eq_zero, one_ne_zero, or_false],
    right,
    have : ∫ (x : ℝ) in 0..2 * π, x - π = 0 := by { simp, ring, },
    simp_rw ←of_real_sub,
    rw integral_of_le (by linarith [pi_pos] : 0 ≤ 2 * π) at this ⊢,
    rw integral_of_real, rw this, refl },
  { have d1a: ∀ x:ℂ, has_deriv_at (λ x, x - π : ℂ → ℂ) (1 : ℂ) x,
    { intro x, exact (has_deriv_at_id x).sub_const _, },
    have d1 : ∀ x:ℝ, has_deriv_at (λ y, y - π : ℝ → ℂ) ((1 : ℝ → ℂ) x) x,
    { intro x, simpa using has_deriv_at.comp x (d1a x) of_real_clm.has_deriv_at },
    have d2a : ∀ x:ℂ, has_deriv_at (λ y, I / n * exp (-n * I * y) : ℂ → ℂ) (exp (-n * I * x)) x,
    { intro x,
      suffices : has_deriv_at (λ y, exp (-n * I * y) : ℂ → ℂ) (exp (-n * I * x) * (-n * I)) x,
      { convert has_deriv_at.const_mul (I / n) this, ring_nf,
        rw mul_inv_cancel, rw I_sq, ring, exact int.cast_ne_zero.mpr hn },
      refine has_deriv_at.comp x (complex.has_deriv_at_exp (-n * I * x)) _,
      simpa using (has_deriv_at_const x (-↑n * I)).mul (has_deriv_at_id x), },
    have d2 : ∀ x:ℝ, has_deriv_at (λ y, I / n * exp (-n * I * y) : ℝ → ℂ)
      (exp (-n * I * x)) x,
    { intro x, simpa using has_deriv_at.comp x (d2a x) of_real_clm.has_deriv_at },
    have d := λ x (hx : x ∈ interval 0 (2 * π)), (d2 x).mul (d1 x),
    have int_ev := integral_eq_sub_of_has_deriv_at d _,
    rw interval_integral.integral_add at int_ev,
    rw eq_sub_of_add_eq int_ev, clear int_ev,
    simp only [of_real_mul, of_real_bit0, of_real_one, of_real_zero, mul_zero,
      complex.exp_zero, mul_one, zero_sub, sub_neg_eq_add, pi.one_apply,
      integral_const_mul],
    have : (-↑n * I * (2 * ↑π)) = ↑(-n) * (2 * π * I) := by { simp, ring, },
    rw [this, exp_int_mul_two_pi_mul_I, integral_exp_mul_complex],
    have : (-↑n * I * ↑(2 * π)) = ↑(-n) * (2 * π * I) := by { simp, ring, },
    rw [this, exp_int_mul_two_pi_mul_I],
    norm_num, field_simp [of_real_ne_zero.mpr pi_pos.ne', int.cast_ne_zero.mpr hn], ring,
    { refine mul_ne_zero _ I_ne_zero, rwa [neg_ne_zero, int.cast_ne_zero], },
    { apply continuous.interval_integrable, continuity },
    all_goals { apply continuous.interval_integrable, simp only [pi.one_apply], continuity } },
end


lemma basel_sum_Z : has_sum (λ n:ℤ, 1 / (n : ℝ) ^ 2) (π ^ 2 / 3) :=
begin
  have t := fourier_line.parseval_line B1 B1_mem_Lp,
  simp_rw [norm_B1, coeff_B1] at t,
  have : ∀ (n : ℤ), ∥I / n∥ ^ 2 = 1 / n ^ 2,
  { intro n,
    simp only [complex.norm_eq_abs, complex.abs_div, abs_I, one_div, inv_pow₀, inv_inj],
    norm_cast, simp },
  simp_rw this at t,
  exact t,
end

lemma basel_sum : has_sum (λ n:ℕ, 1 / ((n + 1) : ℝ) ^ 2) (π ^ 2 / 6) :=
begin
  have := basel_sum_Z.sum_ℕ_of_sum_ℤ,
  simp only [int.cast_add, int.cast_coe_nat, int.cast_one, int.cast_sub, int.cast_neg,
  int.cast_zero, zero_pow', ne.def, bit0_eq_zero, nat.one_ne_zero, not_false_iff,
  div_zero, sub_zero] at this,
  have aux : ∀ (n:ℕ), (-(n:ℝ) - 1) ^ 2 = ((n:ℝ) + 1) ^ 2,
  { intro n, rw [neg_sub_left, neg_sq, add_comm],},
  simp_rw [aux, ←mul_two] at this,
  convert (has_sum.div_const this 2) using 1,
  { ext1, simp, },
  { field_simp, norm_num, }
end

end baselproblem
