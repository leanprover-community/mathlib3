/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import analysis.special_functions.integrals
import analysis.special_functions.trigonometric.bounds
import data.real.pi.wallis

/-! # Euler's infinite product for the sine function

This file proves the infinite product formula

$$ \sin \pi z = \pi z \prod_{n = 1}^\infty \left(1 - \frac{z ^ 2}{n ^ 2}\right) $$

for any real or complex `z`. Our proof closely follows the article
[Salwinski, *Euler's Sine Product Formula: An Elementary Proof*][salwinski2018]: the basic strategy
is to prove a recurrence relation for the integrals `∫ x in 0..π/2, cos 2 z x * cos x ^ (2 * n)`,
generalising the arguments used to prove Wallis' limit formula for `π`.
-/

open_locale real topological_space big_operators
open real set filter interval_integral measure_theory.measure_space

namespace euler_sine

section integral_recursion

/-! ## Recursion formula for the integral of `cos (2 * z * x) * cos x ^ n`

We evaluate the integral of `cos (2 * z * x) * cos x ^ n`, for any complex `z` and even integers
`n`, via repeated integration by parts. -/

variables {z : ℂ} {n : ℕ}

lemma antideriv_cos_comp_const_mul (hz : z ≠ 0) (x : ℝ) :
  has_deriv_at (λ y:ℝ, complex.sin (2 * z * y)  / (2 * z)) (complex.cos (2 * z * x)) x :=
begin
  have a : has_deriv_at _ _ ↑x := has_deriv_at_mul_const _,
  have b : has_deriv_at (λ (y : ℂ), complex.sin (y * (2 * z))) _ ↑x :=
    has_deriv_at.comp x (complex.has_deriv_at_sin (x * (2 * z))) a,
  convert (b.comp_of_real).div_const (2 * z),
  { ext1 x, rw mul_comm _ (2 * z) },
  { field_simp, rw mul_comm _ (2 * z) },
end

lemma antideriv_sin_comp_const_mul (hz : z ≠ 0) (x : ℝ) :
  has_deriv_at (λ y:ℝ, -complex.cos (2 * z * y)  / (2 * z)) (complex.sin (2 * z * x)) x :=
begin
  have a : has_deriv_at _ _ ↑x := has_deriv_at_mul_const _,
  have b : has_deriv_at (λ (y : ℂ), complex.cos (y * (2 * z))) _ ↑x :=
    has_deriv_at.comp x (complex.has_deriv_at_cos (x * (2 * z))) a,
  convert ((b.comp_of_real).div_const (2 * z)).neg,
  { ext1 x, rw mul_comm _ (2 * z), field_simp },
  { field_simp, rw mul_comm _ (2 * z) },
end

lemma integral_cos_mul_cos_pow_aux (hn : 2 ≤ n) (hz : z ≠ 0):
  (∫ x:ℝ in 0..π/2, complex.cos (2 * z * x) * cos x ^ n) =
  n / (2 * z) * ∫ x:ℝ in 0..π/2, complex.sin (2 * z * x) * sin x * cos x ^ (n - 1) :=
begin
  have der1 : ∀ (x : ℝ), (x ∈ uIcc 0 (π/2)) → has_deriv_at (λ y, (↑(cos y)) ^ n : ℝ → ℂ)
    (-n * sin x * cos x ^ (n - 1)) x,
  { intros x hx,
    have b : has_deriv_at (λ y, ↑(cos y) : ℝ → ℂ) (-sin x) x,
      by simpa using (has_deriv_at_cos x).of_real_comp,
    convert has_deriv_at.comp x (has_deriv_at_pow _ _) b using 1,
    ring, },
  convert integral_mul_deriv_eq_deriv_mul der1 (λ x hx, antideriv_cos_comp_const_mul hz x) _ _,
  { ext1 x, rw mul_comm },
  { rw [complex.of_real_zero, mul_zero, complex.sin_zero, zero_div, mul_zero, sub_zero,
      cos_pi_div_two, complex.of_real_zero, zero_pow (by positivity : 0 < n), zero_mul, zero_sub,
      ←integral_neg, ←integral_const_mul],
    refine integral_congr (λ x hx, _),
    field_simp, ring },
  { apply continuous.interval_integrable,
    exact (continuous_const.mul (complex.continuous_of_real.comp continuous_sin)).mul
      ((complex.continuous_of_real.comp continuous_cos).pow (n - 1)) },
  { apply continuous.interval_integrable,
    exact complex.continuous_cos.comp (continuous_const.mul complex.continuous_of_real) }
end

lemma integral_sin_mul_sin_mul_cos_pow_eq (hn : 2 ≤ n) (hz : z ≠ 0) :
  ∫ x:ℝ in 0..π/2, complex.sin (2 * z * x) * sin x * cos x ^ (n - 1) =
  n / (2 * z) * (∫ x:ℝ in 0..π/2, complex.cos (2 * z * x) * cos x ^ n) -
  (n - 1) / (2 * z) * (∫ x:ℝ in 0..π/2, complex.cos (2 * z * x) * cos x ^ (n - 2)) :=
begin
  have der1 : ∀ (x : ℝ), (x ∈ uIcc 0 (π/2)) →
    has_deriv_at (λ y, (sin y) * (cos y) ^ (n - 1) : ℝ → ℂ)
    (cos x ^ n - (n - 1) * sin x ^ 2 * cos x ^ (n - 2)) x,
  { intros x hx,
    have c := has_deriv_at.comp (x:ℂ) (has_deriv_at_pow (n - 1) _) (complex.has_deriv_at_cos x),
    convert ((complex.has_deriv_at_sin x).mul c).comp_of_real using 1,
    { ext1 y, simp only [complex.of_real_sin, complex.of_real_cos] },
    { simp only [complex.of_real_cos, complex.of_real_sin],
      rw [mul_neg, mul_neg, ←sub_eq_add_neg, function.comp_app],
      congr' 1,
      { rw [←pow_succ, nat.sub_add_cancel (by linarith : 1 ≤ n)] },
      { have : ((n - 1 : ℕ) : ℂ) = (n:ℂ) - 1,
        { rw [nat.cast_sub (one_le_two.trans hn), nat.cast_one] },
        rw [nat.sub_sub, this],
        ring } } },
  convert integral_mul_deriv_eq_deriv_mul der1 (λ x hx, antideriv_sin_comp_const_mul hz x) _ _
    using 1,
  { refine integral_congr (λ x hx, _),
    ring_nf },
  { -- now a tedious rearrangement of terms
    -- gather into a single integral, and deal with continuity subgoals:
    rw [sin_zero, cos_pi_div_two, complex.of_real_zero, zero_pow, zero_mul, mul_zero, zero_mul,
      zero_mul, sub_zero, zero_sub, ←integral_neg, ←integral_const_mul,  ←integral_const_mul,
      ←integral_sub],
    rotate,
    { apply continuous.interval_integrable,
      exact continuous_const.mul ((complex.continuous_cos.comp (continuous_const.mul
        complex.continuous_of_real)).mul ((complex.continuous_of_real.comp
        continuous_cos).pow n)) },
    { apply continuous.interval_integrable,
      exact continuous_const.mul
        ((complex.continuous_cos.comp (continuous_const.mul complex.continuous_of_real)).mul
        ((complex.continuous_of_real.comp continuous_cos).pow (n - 2))), },
    { apply nat.sub_pos_of_lt, exact one_lt_two.trans_le hn },
    refine integral_congr (λ x hx, _),
    dsimp only,
    -- get rid of real trig functions and divions by 2 * z:
    rw [complex.of_real_cos, complex.of_real_sin, complex.sin_sq, ←mul_div_right_comm,
      ←mul_div_right_comm, ←sub_div, mul_div, ←neg_div],
    congr' 1,
    have : complex.cos ↑x ^ n = complex.cos ↑x ^ (n - 2) * complex.cos ↑x ^ 2,
    { conv_lhs { rw [←nat.sub_add_cancel hn, pow_add] } },
    rw this,
    ring },
  { apply continuous.interval_integrable,
    exact ((complex.continuous_of_real.comp continuous_cos).pow n).sub
      ((continuous_const.mul ((complex.continuous_of_real.comp continuous_sin).pow 2)).mul
      ((complex.continuous_of_real.comp continuous_cos).pow (n - 2))) },
  { apply continuous.interval_integrable,
    exact complex.continuous_sin.comp (continuous_const.mul complex.continuous_of_real) },
end

/-- Note this also holds for `z = 0`, but we do not need this case for `sin_pi_mul_eq`.  -/
lemma integral_cos_mul_cos_pow (hn : 2 ≤ n) (hz : z ≠ 0) :
  (1 - 4 * z ^ 2 / n ^ 2) * (∫ x:ℝ in 0..π/2, complex.cos (2 * z * x) * cos x ^ n) =
  (n - 1 : ℂ) / n * ∫ x:ℝ in 0..π/2, complex.cos (2 * z * x) * cos x ^ (n - 2) :=
begin
  have nne : (n : ℂ) ≠ 0,
  { contrapose! hn, rw nat.cast_eq_zero at hn, rw hn, exact zero_lt_two },
  have := integral_cos_mul_cos_pow_aux hn hz,
  rw [integral_sin_mul_sin_mul_cos_pow_eq hn hz, sub_eq_neg_add, mul_add, ←sub_eq_iff_eq_add]
    at this,
  convert congr_arg (λ u:ℂ, -u * (2 * z) ^ 2 / n ^ 2) this using 1;
  { field_simp, ring },
end

/-- Note this also holds for `z = 0`, but we do not need this case for `sin_pi_mul_eq`. -/
lemma integral_cos_mul_cos_pow_even (n : ℕ) (hz : z ≠ 0) :
  (1 - z ^ 2 / (n + 1) ^ 2) * (∫ x:ℝ in 0..π/2, complex.cos (2 * z * x) * cos x ^ (2 * n + 2)) =
  (2 * n + 1 : ℂ) / (2 * n + 2) * ∫ x:ℝ in 0..π/2, complex.cos (2 * z * x) * cos x ^ (2 * n) :=
begin
  convert integral_cos_mul_cos_pow (by linarith : 2 ≤ 2 * n + 2) hz using 3,
  { simp only [nat.cast_add, nat.cast_mul, nat.cast_two],
    nth_rewrite_rhs 2 ←mul_one (2:ℂ),
    rw [←mul_add, mul_pow, ←div_div],
    ring },
  { push_cast, ring },
  { push_cast, ring },
end

/-- Relate the integral `cos x ^ n` over `[0, π/2]` to the integral of `sin x ^ n` over `[0, π]`,
which is studied in `data.real.pi.wallis` and other places. -/
lemma integral_cos_pow_eq (n : ℕ) :
  (∫ (x:ℝ) in 0..π/2, cos x ^ n) = 1 / 2 * (∫ (x:ℝ) in 0..π, (sin x) ^ n) :=
begin
  rw [mul_comm (1/2 : ℝ), ←div_eq_iff (one_div_ne_zero (two_ne_zero' ℝ)), ←div_mul, div_one,
    mul_two],
  have L : interval_integrable _ volume 0 (π / 2) := (continuous_sin.pow n).interval_integrable _ _,
  have R : interval_integrable _ volume (π / 2) π := (continuous_sin.pow n).interval_integrable _ _,
  rw ←integral_add_adjacent_intervals L R,
  congr' 1,
  { nth_rewrite 0 (by ring : 0 = π/2 - π/2),
    nth_rewrite 2 (by ring : π/2 = π/2 - 0),
    rw ←integral_comp_sub_left,
    refine integral_congr (λ x _, _),
    dsimp only,
    rw cos_pi_div_two_sub },
  { nth_rewrite 2 (by ring : π = π/2 + π/2),
    nth_rewrite 1 (by ring : π/2 = 0 + π/2),
    rw ←integral_comp_add_right,
    refine integral_congr (λ x _, _),
    dsimp only,
    rw sin_add_pi_div_two },
end

lemma integral_cos_pow_pos (n : ℕ) : 0 < (∫ (x:ℝ) in 0..π/2, cos x ^ n) :=
(integral_cos_pow_eq n).symm ▸ (mul_pos one_half_pos (integral_sin_pow_pos _))

/-- Finite form of Euler's sine product, with remainder term expressed as a ratio of cosine
integrals. -/
lemma sin_pi_mul_eq (z : ℂ) (n : ℕ) :
  complex.sin (π * z) = π * z * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2)) *
  (∫ x in 0..π/2, complex.cos (2 * z * x) * cos x ^ (2 * n)) / ↑∫ x in 0..π/2, cos x ^ (2 * n) :=
begin
  rcases eq_or_ne z 0 with rfl | hz,
  { simp },
  induction n with n hn,
  { simp_rw [mul_zero, pow_zero, mul_one, finset.prod_range_zero, mul_one, integral_one, sub_zero],
    rw [integral_cos_mul_complex (mul_ne_zero two_ne_zero hz), complex.of_real_zero, mul_zero,
      complex.sin_zero, zero_div, sub_zero,
      (by { push_cast, field_simp, ring } : 2 * z * ↑(π / 2) = π * z)],
    field_simp [complex.of_real_ne_zero.mpr pi_pos.ne'],
    ring },
  { rw [hn, finset.prod_range_succ],
    set A := ∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2),
    set B := ∫ x:ℝ in 0..π/2, complex.cos (2 * z * x) * cos x ^ (2 * n),
    set C := ∫ x:ℝ in 0..π/2, cos x ^ (2 * n),
    have aux' : 2 * n.succ = 2 * n + 2,
    { rw [nat.succ_eq_add_one, mul_add, mul_one], },
    have : ∫ x:ℝ in 0..π/2, cos x ^ (2 * n.succ) = (2 * (n:ℝ) + 1) / (2 * n + 2) * C,
    { rw integral_cos_pow_eq,
      dsimp only [C],
      rw [integral_cos_pow_eq, aux', integral_sin_pow, sin_zero, sin_pi, pow_succ, zero_mul,
        zero_mul, zero_mul, sub_zero, zero_div, zero_add, ←mul_assoc, ←mul_assoc,
        mul_comm (1 / 2 : ℝ) _, nat.cast_mul, nat.cast_bit0, nat.cast_one] },
    rw this,
    change ↑π * z * A * B / ↑C =
      (↑π * z * (A * (1 - z ^ 2 / (↑n + 1) ^ 2)) *
       ∫ (x : ℝ) in 0..π / 2, complex.cos (2 * z * ↑x) * ↑(cos x) ^ (2 * n.succ)) /
    ↑((2 * ↑n + 1) / (2 * ↑n + 2) * C),
    have : ↑π * z * (A * (1 - z ^ 2 / (↑n + 1) ^ 2)) *
      ∫ (x : ℝ) in 0..π / 2, complex.cos (2 * z * ↑x) * ↑(cos x) ^ (2 * n.succ)
    = ↑π * z * A * ((1 - z ^ 2 / (↑n.succ) ^ 2) *
      ∫ (x : ℝ) in 0..π / 2, complex.cos (2 * z * ↑x) * ↑(cos x) ^ (2 * n.succ)),
    { nth_rewrite_rhs 0 nat.succ_eq_add_one,
      rw nat.cast_add_one,
      ring },
    rw this,
    suffices : (1 - z ^ 2 / ↑(n.succ) ^ 2) *
      ∫ (x : ℝ) in 0..π / 2, complex.cos (2 * z * ↑x) * ↑(cos x) ^ (2 * n.succ) =
      (2 * n + 1) / (2 * n + 2) * B,
    { rw [this, complex.of_real_mul, complex.of_real_div],
      have : (C:ℂ) ≠ 0 := complex.of_real_ne_zero.mpr (integral_cos_pow_pos _).ne',
      have : 2 * (n:ℂ) + 1 ≠ 0,
      { convert (nat.cast_add_one_ne_zero (2 * n) : (↑(2 * n) + 1 : ℂ) ≠ 0),
        simp },
      have : 2 * (n:ℂ) + 2 ≠ 0,
      { convert (nat.cast_add_one_ne_zero (2 * n + 1) : (↑(2 * n + 1) + 1 : ℂ) ≠ 0) using 1,
        push_cast, ring },
      field_simp, ring },
    convert integral_cos_mul_cos_pow_even n hz,
    rw nat.cast_succ }
end

end integral_recursion

section cos_pow_kernel

/-! ## Integration against `cos x ^ n`

The next few lemmas can be interpreted as stating that the distribution on `[0, π/2]` given by
integrating against `cos x ^ n` converges, after a suitable normalisation, to a Dirac distribution
at 0. -/

/-- If `f` has continuous derivative `f'` on `[a, b]`, then it satisfies a Lipschitz continuity
condition at `a`. (This is a simple special case of
`convex.lipschitz_on_with_of_nnnorm_has_deriv_within_le`.) -/
lemma norm_sub_le_mul_of_cont_diff {f f' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
  (hfd : ∀ (x:ℝ), x ∈ Icc a b → has_deriv_within_at f (f' x) (Icc a b) x)
  (hfc : continuous_on f' (Icc a b)) :
  ∃ (M : ℝ), ∀ (x : ℝ), x ∈ Icc a b → ‖f x - f a‖ ≤ M * (x - a) :=
begin
  obtain ⟨M, hM⟩ := is_compact.exists_bound_of_continuous_on is_compact_Icc hfc,
  have hM' : 0 ≤ M := le_trans (norm_nonneg _) (hM a (left_mem_Icc.mpr hab)),
  refine ⟨M, _⟩,
  have := convex.lipschitz_on_with_of_nnnorm_has_deriv_within_le (convex_Icc a b) hfd _,
  show nnreal, exact ‖M‖₊,
  { intros x hx,
    specialize this hx (left_mem_Icc.mpr hab),
    simp_rw edist_eq_coe_nnnorm_sub at this,
    rw [←ennreal.coe_mul, ennreal.coe_le_coe, ←nnreal.coe_le_coe, coe_nnnorm] at this,
    convert this,
    { rw [coe_nnnorm, norm_of_nonneg hM'] },
    { rw [coe_nnnorm, norm_of_nonneg (by linarith [hx.1] : 0 ≤ x - a)] } },
  { intros x hx,
    rw ←nnreal.coe_le_coe,
    simp_rw coe_nnnorm,
    convert hM x hx,
    exact norm_of_nonneg hM' }
end

/-- Bound for the integral of `x / (x ^ 2 + 1) ^ t`, for `t < 2`. -/
lemma integral_div_rpow_sq_add_one_le {t : ℝ} (y : ℝ) (ht : 2 < t) :
  ∫ (u : ℝ) in 0..y, u / (u ^ 2 + 1) ^ (t / 2) ≤ 1 / (t - 2) :=
begin
  calc ∫ u in 0..y, u / (u ^ 2 + 1) ^ (t / 2) = ∫ u in 0..y, u * (u ^ 2 + 1) ^ (-t / 2) :
    begin
      refine integral_congr (λ u hu, _),
      dsimp only,
      rw [div_eq_mul_inv, ←rpow_neg (add_nonneg (sq_nonneg u) zero_le_one), neg_div],
    end
  ... = ((1 + y ^ 2) ^ (-t / 2 + 1) / (2 * (-t / 2 + 1)) - 1 / (2 * (-t / 2 + 1))) :
    begin
      conv in (_ ^ 2 + _) { rw add_comm },
      rw [integral_mul_rpow_one_add_sq (by linarith : -t / 2 ≠ -1), zero_pow zero_lt_two,
        add_zero, one_rpow],
    end
  ... = (1 / (t - 2) - (1 + y ^ 2) ^ (-t / 2 + 1) / (t - 2)) :
    begin
      have : ∀ u:ℝ, u / (2 * (-t / 2 + 1)) = -u / (t - 2),
      { intro u,
        rw [mul_add, mul_one, ←mul_div_assoc, mul_div_cancel_left, neg_div, ←div_neg],
        congr' 1, ring,
        exact two_ne_zero },
      simp_rw this,
      rw [sub_eq_add_neg _ ((-1 : ℝ) / _), ←neg_div, neg_neg, add_comm _ (1 / (t - 2)),
        neg_div, ←sub_eq_add_neg],
    end
  ... ≤ 1 / (t - 2) :
    begin
      apply sub_le_self,
      refine div_nonneg (rpow_nonneg_of_nonneg _ _) _,
      linarith [sq_nonneg y],
      linarith,
    end
end

/-- If `f` is integrable on `[0, π/2]`, and `f x` satisfies a Lipschitz-continuity condition at `0`,
then the integral `∫ x in 0..π/2, f x * cos x ^ n` differs from `f 0 * ∫ x in 0..π/2, cos x ^ n` by
an `O(1 / n)` error. -/
lemma abs_integral_mul_cos_pow_sub_le
  {f : ℝ → ℂ} (hfi : interval_integrable f volume 0 (π/2))
  {M : ℝ} (hm : ∀ (x : ℝ), x ∈ Icc (0:ℝ) (π/2) → ‖f x - f 0‖ ≤ M * x) {n : ℕ} (hn : 2 < n) :
  ‖(∫ (x:ℝ) in 0..π/2, f x * cos x ^ n) - f 0 * (∫ (x:ℝ) in 0..π/2, cos x ^ n)‖
  ≤ M / (n - 2) :=
begin
  have m_nn : 0 ≤ M,
  { replace hm := (norm_nonneg _).trans (hm (π/2) (right_mem_Icc.mpr pi_div_two_pos.le)),
    rwa mul_nonneg_iff_left_nonneg_of_pos pi_div_two_pos at hm, },
  rw [sub_eq_add_neg, ←neg_mul, ←integral_const_mul, ←integral_add],
  swap, { apply hfi.mul_continuous_on (continuous.continuous_on _),
    exact (complex.continuous_of_real.comp continuous_cos).pow n},
  swap, { apply continuous.interval_integrable,
    exact continuous_const.mul ((complex.continuous_of_real.comp continuous_cos).pow n)},
  refine (norm_integral_le_integral_norm pi_div_two_pos.le).trans _,
  -- Bound the LHS above by the integral of (M * x) / (x ^ 2 + 1) ^ (n / 2).
  -- (This creates several integrability side-goals.)
  refine (integral_mono_on pi_div_two_pos.le _ _ _).trans _,
  { exact λ x:ℝ, M * x / (x ^ 2 + 1) ^ (n / 2 : ℝ) },
  { refine (interval_integrable.add _ _).norm,
    { apply hfi.mul_continuous_on (continuous.continuous_on _),
      exact (complex.continuous_of_real.comp continuous_cos).pow n},
    { apply continuous.interval_integrable,
      exact continuous_const.mul ((complex.continuous_of_real.comp continuous_cos).pow n)} },
  { apply continuous_on.interval_integrable,
    refine continuous_at.continuous_on (λ x hx, _),
    have : 0 < x ^ 2 + 1 := by { linarith [sq_nonneg x], },
    apply continuous_at.div,
    { exact continuous_at_id.const_mul _ },
    { apply continuous_at.rpow_const,
      { apply continuous.continuous_at,
        exact (continuous_pow 2).add continuous_const },
      { left, exact this.ne' } },
    { exact (rpow_pos_of_pos this _).ne', } },
  { intros x hx,
    have a1 : 0 ≤ cos x,
    { refine cos_nonneg_of_mem_Icc ⟨_, _⟩; linarith [pi_div_two_pos, hx.1, hx.2] },
    have a2 : 0 < x ^ 2 + 1 := by linarith [sq_nonneg x],
    have a3 : cos x ≤ 1 / sqrt (x ^ 2 + 1),
    { refine cos_le_one_div_sqrt_sq_add_one _ _; linarith [pi_div_two_pos, hx.1, hx.2] },
    rw [neg_mul, ←sub_eq_add_neg, ←sub_mul, norm_mul],
    refine le_trans (mul_le_mul_of_nonneg_right (hm x hx) (norm_nonneg _)) _,
    refine mul_le_mul_of_nonneg_left _ (mul_nonneg m_nn hx.1),
    rw [norm_pow, complex.norm_eq_abs, complex.abs_of_nonneg a1],
    convert pow_le_pow_of_le_left a1 a3 n,
    rw [←inv_rpow a2.le, ←rpow_nat_cast _ n],
    nth_rewrite 1 (by { field_simp, ring } : (n:ℝ) = 2 * (n / 2 : ℝ)),
    rw [rpow_mul (one_div_nonneg.mpr $ sqrt_nonneg _), one_div, inv_rpow (sqrt_nonneg _) 2],
    nth_rewrite 3 ←nat.cast_two,
    rw [rpow_nat_cast _ 2, sq_sqrt a2.le] },
  simp_rw [←mul_div, integral_const_mul],
  refine mul_le_mul_of_nonneg_left _ m_nn,
  rw ←one_div,
  refine integral_div_rpow_sq_add_one_le _ (_ : 2 < (n:ℝ)),
  rwa [←nat.cast_two, nat.cast_lt],
end

lemma le_integral_cos_pow (n : ℕ) :
  sqrt (π / 2 / (n + 1)) ≤ ∫ (x:ℝ) in 0..π/2, cos x ^ n :=
begin
  have nn : 0 < (n : ℝ) + 1 := by linarith [(nat.cast_nonneg _ : 0 ≤ (n:ℝ))],
  rw [integral_cos_pow_eq, ←div_le_iff' (by simp : 0 < (1 / 2 : ℝ)), ←div_mul, div_one],
  convert le_integral_sin_pow n,
  rw [←sq_eq_sq (mul_nonneg (sqrt_nonneg _) zero_le_two) (sqrt_nonneg _), mul_pow,
    sq_sqrt (div_pos pi_div_two_pos nn).le, sq_sqrt (div_pos two_pi_pos nn).le],
  field_simp [nn.ne'],
  ring,
end

lemma abs_integral_mul_cos_pow_div_sub_le
  {f : ℝ → ℂ} (hfi : interval_integrable f volume 0 (π/2))
  {M : ℝ} (hm : ∀ (x : ℝ), x ∈ Icc (0:ℝ) (π/2) → ‖f x - f 0‖ ≤ M * x) {n : ℕ} (hn : 2 < n) :
  ‖(∫ (x:ℝ) in 0..π/2, f x * cos x ^ n) / (∫ (x:ℝ) in 0..π/2, cos x ^ n) - f 0‖
  ≤ M / (n - 2) * sqrt (2 * (n + 1) / π) :=
begin
  have : ‖(∫ (x:ℝ) in 0..π/2, f x * cos x ^ n) / (∫ (x:ℝ) in 0..π/2, cos x ^ n) - f 0‖
    ≤ M / (n - 2) / (∫ (x:ℝ) in 0..π/2, cos x ^ n),
  { rw [le_div_iff (integral_cos_pow_pos n), ←norm_of_nonneg (integral_cos_pow_pos n).le,
    real.norm_eq_abs, ←complex.abs_of_real, ←complex.norm_eq_abs, ←norm_mul,
    ←interval_integral.integral_of_real],
    have : ∫ (x : ℝ) in 0..π/2, ((cos x ^ n : ℝ) : ℂ) = ∫ (x : ℝ) in 0..π/2, ((cos x : ℝ) : ℂ) ^ n,
    { simp_rw complex.of_real_pow },
    rw [this, sub_mul],
    convert abs_integral_mul_cos_pow_sub_le hfi hm hn,
    apply div_mul_cancel,
    rw [←this, interval_integral.integral_of_real, complex.of_real_ne_zero],
    exact (integral_cos_pow_pos n).ne' },
  refine this.trans _,
  have m_nn : 0 ≤ M,
  { replace hm := (norm_nonneg _).trans (hm (π/2) (right_mem_Icc.mpr pi_div_two_pos.le)),
    rwa mul_nonneg_iff_left_nonneg_of_pos pi_div_two_pos at hm, },
  conv_lhs { rw div_eq_mul_inv },
  refine mul_le_mul_of_nonneg_left _ (div_nonneg m_nn _),
  swap, { rw [sub_nonneg, ←nat.cast_two, nat.cast_le], exact hn.le },
  rw inv_le,
  { convert le_integral_cos_pow n,
    { rw ←sqrt_inv,
      congr' 1,
      rw [inv_div, div_div] } },
  { apply integral_cos_pow_pos },
  { apply sqrt_pos_of_pos,
    refine div_pos (mul_pos (zero_lt_two' ℝ) _) pi_pos,
    rw [←nat.cast_add_one, nat.cast_pos],
    linarith }
end

lemma tendsto_integral_mul_cos_pow_div
  {f : ℝ → ℂ} (hfi : interval_integrable f volume 0 (π/2))
  {M : ℝ} (hm : ∀ (x : ℝ), x ∈ Icc (0:ℝ) (π/2) → ‖f x - f 0‖ ≤ M * x) :
  tendsto (λ n:ℕ, (∫ (x:ℝ) in 0..π/2, f x * cos x ^ n) / (∫ (x:ℝ) in 0..π/2, cos x ^ n))
  at_top (𝓝 $ f 0) :=
begin
  have m_nn : 0 ≤ M,
  { replace hm := (norm_nonneg _).trans (hm (π/2) (right_mem_Icc.mpr pi_div_two_pos.le)),
    rwa mul_nonneg_iff_left_nonneg_of_pos pi_div_two_pos at hm, },
  rw tendsto_iff_norm_tendsto_zero,
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds _
    (eventually_of_forall (λ n, norm_nonneg _))
    ((eventually_gt_at_top 2).mp
      (eventually_of_forall (λ n hn, abs_integral_mul_cos_pow_div_sub_le hfi hm hn))),
  { have : tendsto (λ n:ℕ, (1:ℝ) / (n - 2) + (3:ℝ) / (n - 2) ^ 2) at_top (𝓝 0),
    { rw (by ring : (0:ℝ) = 0 + 0),
      refine tendsto.add (tendsto_const_nhds.div_at_top _) _,
      { exact tendsto_at_top_add_const_right _ _ tendsto_coe_nat_at_top_at_top },
      refine tendsto_const_nhds.div_at_top _,
      refine (tendsto_pow_at_top two_ne_zero).comp _,
      exact tendsto_at_top_add_const_right _ _ tendsto_coe_nat_at_top_at_top },
    replace this := (tendsto.comp (continuous_at_id.sqrt) this).const_mul (M * sqrt (2 / π)),
    convert tendsto.congr' _ this using 1,
    { rw [id.def, sqrt_zero, mul_zero] },
    rw [eventually_eq, eventually_at_top],
    refine ⟨3, λ n hn, _⟩,
    rw ge_iff_le at hn,
    have : 0 < (n:ℝ) - 2,
    { replace hn := (nat.cast_le.mpr hn : ((3:ℕ):ℝ) ≤ (n:ℝ)),
      rw [nat.cast_bit1, nat.cast_one] at hn,
      linarith },
    dsimp only [id.def],
    rw ←sq_eq_sq,
    rw [mul_pow, mul_pow, mul_pow, sq_sqrt, sq_sqrt, sq_sqrt, div_pow],
    { field_simp [this.ne', pi_pos.ne'],
      ring },
    { refine div_nonneg (mul_nonneg zero_le_two _) pi_pos.le,
      linarith },
    { refine add_nonneg (div_nonneg _ this.le) (div_nonneg _ (sq_pos_of_pos this).le); linarith },
    { exact (div_pos (zero_lt_two' ℝ) pi_pos).le },
    { refine mul_nonneg (mul_nonneg m_nn (sqrt_nonneg _)) (sqrt_nonneg _), },
    { exact mul_nonneg (div_nonneg m_nn this.le) (sqrt_nonneg _) } },
end

lemma tendsto_integral_cos_mul_cos_pow_div (z : ℂ) :
  tendsto (λ n:ℕ,
  (∫ x:ℝ in 0..π/2, complex.cos (2 * z * x) * cos x ^ n) / (∫ x:ℝ in 0..π/2, cos x ^ n))
  at_top (𝓝 1) :=
begin
  have der : ∀ (x : ℝ), has_deriv_at (λ t:ℝ, complex.cos (2 * z * t))
    (-2 * z * complex.sin (2 * z * x)) x,
  { intro x,
    rw (λ α, by ring : ∀ (α : ℂ), (-2 * z * α) = (-α) * (2 * z)),
    refine has_deriv_at.comp x (complex.has_deriv_at_cos _) (has_deriv_at.comp_of_real _),
    convert (has_deriv_at_id (x:ℂ)).const_mul (2 * z) using 1,
    ring },
  have ct_der : continuous (λ t:ℝ, -2 * z * complex.sin (2 * z * t)),
  { exact continuous_const.mul (complex.continuous_sin.comp (continuous_const.mul
      complex.continuous_of_real)) },
  obtain ⟨C, hC⟩ := norm_sub_le_mul_of_cont_diff pi_div_two_pos.le
    (λ x hx, (der x).has_deriv_within_at) (continuous.continuous_on ct_der),
  convert tendsto_integral_mul_cos_pow_div _ _ using 1,
  { rw [complex.of_real_zero, mul_zero, complex.cos_zero], },
  { apply continuous.interval_integrable,
    exact complex.continuous_cos.comp (continuous_const.mul complex.continuous_of_real), },
  { exact C },
  { simpa only [sub_zero] using hC }
end

end cos_pow_kernel


/-! ## Conclusion of the proof

The main theorem `complex.tendsto_euler_sin_prod`, and its real variant
`real.tendsto_euler_sin_prod`, now follow by combining `sin_pi_mul_eq` and
`tendsto_integral_cos_mul_cos_pow_div`-/

/-- Euler's infinite product formula for the complex sine function. -/
lemma _root_.complex.tendsto_euler_sin_prod (z : ℂ) :
  tendsto (λ n:ℕ, ↑π * z * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2)))
  at_top (𝓝 $ complex.sin (π * z)) :=
begin
  have A : tendsto (λ n:ℕ, ↑π * z * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2)) *
    (∫ x in 0..π / 2, complex.cos (2 * z * x) * cos x ^ (2 * n)) /
    ↑∫ x in 0..π / 2, cos x ^ (2 * n))
    at_top (𝓝 $ _) := tendsto.congr (λ n, (sin_pi_mul_eq z n)) tendsto_const_nhds,
  have : 𝓝 (complex.sin (π * z)) = 𝓝 (complex.sin (π * z) * 1) := by rw mul_one,
  simp_rw [this, mul_div_assoc] at A,
  convert (tendsto_mul_iff_of_ne_zero _ one_ne_zero).mp A,
  convert (tendsto_integral_cos_mul_cos_pow_div z).comp (tendsto_id.const_mul_at_top' zero_lt_two),
  ext1 n,
  simp_rw [function.comp_app, id.def, ←interval_integral.integral_of_real, complex.of_real_pow],
end

/-- Euler's infinite product formula for the real sine function. -/
lemma _root_.real.tendsto_euler_sin_prod (x : ℝ) :
  tendsto (λ n:ℕ, π * x * (∏ j in finset.range n, (1 - x ^ 2 / (j + 1) ^ 2)))
  at_top (𝓝 $ sin (π * x)) :=
begin
  convert (complex.continuous_re.tendsto _).comp (complex.tendsto_euler_sin_prod x),
  { ext1 n,
    rw [function.comp_app, ←complex.of_real_mul, complex.of_real_mul_re],
    suffices : ∏ (j : ℕ) in finset.range n, (1 - (x:ℂ) ^ 2 / (↑j + 1) ^ 2) =
      ↑∏ (j : ℕ) in finset.range n, (1 - x ^ 2 / (↑j + 1) ^ 2), by rw [this, complex.of_real_re],
    rw complex.of_real_prod,
    refine finset.prod_congr (by refl) (λ n hn, _),
    norm_cast },
  { rw [←complex.of_real_mul, ←complex.of_real_sin, complex.of_real_re] }
end

end euler_sine
