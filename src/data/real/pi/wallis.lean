/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import analysis.special_functions.integrals

/-! # The Wallis formula for Pi

This file establishes the Wallis product for `π` (`real.tendsto_prod_pi_div_two`). Our proof is
largely about analyzing the behaviour of the sequence `∫ x in 0..π, sin x ^ n` as `n → ∞`.
See: https://en.wikipedia.org/wiki/Wallis_product

The proof can be broken down into two pieces. The first step (carried out in
`analysis.special_functions.integrals`) is to use repeated integration by parts to obtain an
explicit formula for this integra, which is rational if `n` is odd and a rational multiple of `π`
if `n` is even.

The second step, carried out here, is to estimate the ratio
`∫ (x : ℝ) in 0..π, sin x ^ (2 * k + 1) / ∫ (x : ℝ) in 0..π, sin x ^ (2 * k)` and prove that
it converges to one using the squeeze theorem. The final product for `π` is obtained after some
algebraic manipulation. -/

open_locale real topological_space big_operators nat
open filter finset interval_integral

namespace real

namespace wallis

/-- The product of the first `k` terms in Wallis' formula for `π`. -/
noncomputable def W (k : ℕ) : ℝ :=
  ∏ i in range k, (2 * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3))

lemma W_succ (k : ℕ) :
  W (k + 1) = W k * ((2 * k + 2) / (2 * k + 1) * ((2 * k + 2) / (2 * k + 3))) :=
prod_range_succ _ _

lemma W_pos (k : ℕ) : 0 < W k :=
begin
  induction k with k hk,
  { unfold W, simp },
  { rw W_succ,
    refine mul_pos hk (mul_pos (div_pos _ _) (div_pos _ _)),
    all_goals { linarith [(nat.cast_nonneg k : 0 ≤ (k:ℝ))] } }
end

lemma W_eq_factorial_ratio (n : ℕ) :
  W n = (2 ^ (4 * n) * n! ^ 4) / ((2 * n)!^ 2 * (2 * n + 1)) :=
begin
  induction n with n IH,
  { simp only [W, prod_range_zero, nat.factorial_zero, mul_zero, pow_zero, algebra_map.coe_one,
      one_pow, mul_one, algebra_map.coe_zero, zero_add, div_self, ne.def, one_ne_zero,
      not_false_iff] },
  { unfold W at ⊢ IH,
    rw [prod_range_succ, IH, _root_.div_mul_div_comm, _root_.div_mul_div_comm],
    refine (div_eq_div_iff _ _).mpr _,
    any_goals { exact ne_of_gt (by positivity) },
    simp_rw [nat.mul_succ, nat.factorial_succ, pow_succ],
    push_cast,
    ring_nf }
end

lemma W_eq_integral_sin_pow_div_integral_sin_pow (k : ℕ) :
  (π/2)⁻¹ * W k = (∫ (x : ℝ) in 0..π, sin x ^ (2 * k + 1)) / ∫ (x : ℝ) in 0..π, sin x ^ (2 * k) :=
begin
  rw [integral_sin_pow_even, integral_sin_pow_odd, mul_div_mul_comm, ←prod_div_distrib, inv_div],
  simp_rw [div_div_div_comm, div_div_eq_mul_div, mul_div_assoc],
  refl,
end

lemma W_le (k : ℕ) : W k ≤ π / 2 :=
begin
  rw [←div_le_one pi_div_two_pos, div_eq_inv_mul],
  rw [W_eq_integral_sin_pow_div_integral_sin_pow, div_le_one (integral_sin_pow_pos _)],
  apply integral_sin_pow_succ_le,
end

lemma W_ge (k : ℕ) : ((2:ℝ) * k + 1) / (2 * k + 2) * (π / 2) ≤ W k :=
begin
  rw [←le_div_iff pi_div_two_pos, div_eq_inv_mul (W k) _],
  rw [W_eq_integral_sin_pow_div_integral_sin_pow, le_div_iff (integral_sin_pow_pos _)],
  convert integral_sin_pow_succ_le (2 * k + 1),
  rw [integral_sin_pow (2 * k)],
  simp only [sin_zero, zero_pow', ne.def, nat.succ_ne_zero, not_false_iff, zero_mul, sin_pi,
    tsub_zero, nat.cast_mul, nat.cast_bit0, algebra_map.coe_one, zero_div, zero_add],
end

lemma tendsto_W_nhds_pi_div_two : tendsto W at_top (𝓝 $ π / 2) :=
begin
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le _ tendsto_const_nhds W_ge W_le,
  have : 𝓝 (π / 2) = 𝓝 ((1 - 0) * (π / 2)) := by rw [sub_zero, one_mul], rw this,
  refine tendsto.mul _ tendsto_const_nhds,
  have h : ∀ (n:ℕ), ((2:ℝ) * n + 1) / (2 * n + 2) = 1 - 1 / (2 * n + 2),
  { intro n,
    rw [sub_div' _ _ _ (ne_of_gt (add_pos_of_nonneg_of_pos
      (mul_nonneg ((two_pos : 0 < (2:ℝ)).le) (nat.cast_nonneg _)) two_pos)), one_mul],
    congr' 1, ring },
  simp_rw h,
  refine (tendsto_const_nhds.div_at_top _).const_sub _,
  refine tendsto.at_top_add _ tendsto_const_nhds,
  exact tendsto_coe_nat_at_top_at_top.const_mul_at_top two_pos,
end

lemma W_eq_mul_sq (k : ℕ) :
  W k = (2 * k + 1) * (∏ i in range k, ((2:ℝ) * i + 2) / (2 * i + 3)) ^ 2 :=
begin
  induction k with k hk,
  { simp [W], },
  { unfold W at *,
    rw [prod_range_succ, prod_range_succ, hk],
    suffices : ∀ (α : ℝ),
      (2 * ↑k + 1) * α ^ 2 * ((2 * ↑k + 2) / (2 * ↑k + 1) * ((2 * ↑k + 2) / (2 * ↑k + 3))) =
      (2 * ↑(k.succ) + 1) * (α * ((2 * ↑k + 2) / (2 * ↑k + 3))) ^ 2,
    { rw this },
    intro α,
    have a : (2 * ↑k + 1 : ℝ) ≠ 0 := by positivity,
    have b : (2 * ↑k + 3 : ℝ) ≠ 0 := by positivity,
    field_simp, ring }
end

lemma integral_sin_pow_odd_sq_eq (k : ℕ) :
  (∫ x in 0..π, sin x ^ (2 * k + 1)) ^ 2 = 4 * W k / (2 * k + 1) :=
begin
  rw integral_sin_pow_odd,
  have B := W_eq_mul_sq k,
  rw [mul_comm (2 * (k:ℝ) + 1) _, ←div_eq_iff] at B,
  rw [mul_pow, ←B],
  ring,
  linarith [(nat.cast_nonneg k : 0 ≤ (k:ℝ))],
end

lemma integral_sin_pow_even_sq_eq (k : ℕ) :
  (∫ x in 0..π, sin x ^ (2 * k)) ^ 2 = π ^ 2 / (2 * k + 1) / W k :=
begin
  induction k with k hk,
  { dsimp only [W],
    simp },
  { have np : 0 < 2 * (k:ℝ) + 1 := by linarith [(nat.cast_nonneg k : 0 ≤ (k:ℝ))],
    rw [nat.succ_eq_add_one, mul_add 2 k 1, mul_one, integral_sin_pow, sin_zero, sin_pi,
      zero_pow (nat.add_pos_right _ zero_lt_one), zero_mul, zero_mul, sub_zero, zero_div, zero_add,
      mul_pow, hk, W_succ, nat.cast_add_one, nat.cast_mul, mul_add, mul_one,
      add_assoc (2 * (k:ℝ)) 2 1, (by ring : (2:ℝ) + 1 = 3), sq],
    have np2 : 2 * (k:ℝ) + 2 ≠ 0 := by linarith,
    have np3 : 2 * (k:ℝ) + 3 ≠ 0 := by linarith,
    field_simp [np.ne', (W_pos k).ne'],
    ring }
end

end wallis

end real

open real real.wallis

section integral_sin_pow_bounds
/-! ## Bounds for integrals of `sin x ^ n`

Explicit `O(1/√n)` bounds for `∫ x in 0..π, sin x ^ n`, as a by-product of the proof of Wallis'
formula for `π`. -/

lemma integral_sin_pow_odd_le (n : ℕ) :
  ∫ x in 0..π, sin x ^ (2 * n + 1) ≤ sqrt (2 * π / (2 * n + 1)) :=
begin
  have np : 0 < 2 * (n:ℝ) + 1 := by linarith [(nat.cast_nonneg n : 0 ≤ (n:ℝ))],
  rw [le_sqrt (integral_sin_pow_pos _).le (div_pos two_pi_pos np).le, integral_sin_pow_odd_sq_eq],
  apply div_le_div_of_le np.le,
  rw ←le_div_iff' (by linarith : 0 < (4:ℝ)),
  convert W_le n using 1,
  ring,
end

lemma integral_sin_pow_even_le (n : ℕ) :
  ∫ x in 0..π, sin x ^ (2 * n) ≤ sqrt (2 * π * (2 * n + 2) / (2 * n + 1) ^ 2) :=
begin
  have np : 0 < 2 * (n:ℝ) + 1 := by linarith [(nat.cast_nonneg n : 0 ≤ (n:ℝ))],
  have np' : 0 < 2 * (n:ℝ) + 2 := by linarith,
  rw le_sqrt (integral_sin_pow_pos _).le,
  swap, { refine div_nonneg _ (sq_nonneg _), exact mul_nonneg (two_pi_pos).le np'.le },
  rw [integral_sin_pow_even_sq_eq, div_le_iff (W_pos n), ←div_le_iff'],
  swap, { refine div_pos _ (sq_pos_of_pos np), exact mul_pos two_pi_pos np' },
  convert W_ge n,
  field_simp [np.ne', np'.ne', pi_pos.ne'],
  ring,
end

lemma integral_sin_pow_le {n : ℕ} (hn : n ≠ 0) : ∫ x in 0..π, sin x ^ n ≤ sqrt (2 * π / n) :=
begin
  -- this is a slightly weaker bound than `integral_sin_pow_even_le` for even `n`, but uniform in
  -- its statement
  obtain ⟨k, hk⟩ := nat.even_or_odd' n,
  rcases hk with rfl | rfl,
  { refine le_trans (integral_sin_pow_even_le k) _,
    apply sqrt_le_sqrt,
    rw [div_le_div_iff, mul_assoc, mul_le_mul_left two_pi_pos],
    rotate, { positivity }, { positivity },
    have : (2 * (k:ℝ) + 2) * ((2 * k : ℕ) : ℝ) = (2 * k + 1) ^ 2 - 1,
    { push_cast, ring, },
    rw [this, sub_le_self_iff],
    exact zero_le_one },
  { convert integral_sin_pow_odd_le k using 3,
    rw [nat.cast_add, nat.cast_mul, nat.cast_two, nat.cast_one] },
end

lemma integral_sin_pow_ge (n : ℕ) : sqrt (2 * π / (n + 1)) ≤ ∫ x in 0..π, sin x ^ n :=
begin
  refine sqrt_le_iff.mpr ⟨(integral_sin_pow_pos _).le, _⟩,
  obtain ⟨k, hk⟩ := nat.even_or_odd' n,
  have np : 0 < 2 * (k:ℝ) + 1 := by positivity,
  have np' : 2 * (k:ℝ) + 2 ≠ 0 := by positivity,
  rcases hk with rfl | rfl,
  { rw [integral_sin_pow_even_sq_eq, le_div_iff (W_pos _), nat.cast_mul, nat.cast_two,
      ←le_div_iff' (div_pos two_pi_pos np)],
    convert W_le k using 1,
    field_simp [np.ne', np', pi_pos.ne'],
    ring },
  { rw [nat.cast_add, nat.cast_mul, nat.cast_two, nat.cast_one,
      (by ring : (2:ℝ) * k + 1 + 1 = 2 * k + 2), integral_sin_pow_odd_sq_eq, le_div_iff np,
      ←div_le_iff' (by positivity : 0 < (4:ℝ))],
    convert W_ge k,
    field_simp [np.ne', np'],
    ring },
end

end integral_sin_pow_bounds

/-- Wallis' product formula for `π / 2`. -/
theorem real.tendsto_prod_pi_div_two :
  tendsto
  (λ k, ∏ i in range k, (((2:ℝ) * i + 2) / (2 * i + 1)) * ((2 * i + 2) / (2 * i + 3)))
  at_top (𝓝 (π/2)) :=
tendsto_W_nhds_pi_div_two
