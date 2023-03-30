/-
Copyright (c) 2022. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Fabian Kruse, Nikolas Kuhn
-/
import analysis.p_series
import analysis.special_functions.log.deriv
import tactic.positivity
import data.real.pi.wallis

/-!
# Stirling's formula

This file proves Stirling's formula for the factorial.
It states that $n!$ grows asymptotically like $\sqrt{2\pi n}(\frac{n}{e})^n$.

## Proof outline

The proof follows: <https://proofwiki.org/wiki/Stirling%27s_Formula>.

We proceed in two parts.

**Part 1**: We consider the sequence $a_n$ of fractions $\frac{n!}{\sqrt{2n}(\frac{n}{e})^n}$
and prove that this sequence converges to a real, positive number $a$. For this the two main
ingredients are
 - taking the logarithm of the sequence and
 - using the series expansion of $\log(1 + x)$.

**Part 2**: We use the fact that the series defined in part 1 converges againt a real number $a$
and prove that $a = \sqrt{\pi}$. Here the main ingredient is the convergence of Wallis' product
formula for `π`.
-/

open_locale topology real big_operators nat
open finset filter nat real

namespace stirling
/-!
 ### Part 1
 https://proofwiki.org/wiki/Stirling%27s_Formula#Part_1
-/

/--
Define `stirling_seq n` as $\frac{n!}{\sqrt{2n}(\frac{n}{e})^n}$.
Stirling's formula states that this sequence has limit $\sqrt(π)$.
-/
noncomputable def stirling_seq (n : ℕ) : ℝ :=
n! / (sqrt (2 * n) * (n / exp 1) ^ n)

@[simp] lemma stirling_seq_zero : stirling_seq 0 = 0 :=
by rw [stirling_seq, cast_zero, mul_zero, real.sqrt_zero, zero_mul, div_zero]

@[simp] lemma stirling_seq_one : stirling_seq 1 = exp 1 / sqrt 2 :=
by rw [stirling_seq, pow_one, factorial_one, cast_one, mul_one, mul_one_div, one_div_div]

/--
We have the expression
`log (stirling_seq (n + 1)) = log(n + 1)! - 1 / 2 * log(2 * n) - n * log ((n + 1) / e)`.
-/
lemma log_stirling_seq_formula (n : ℕ) : log (stirling_seq n.succ) =
  log n.succ!- 1 / 2 * log (2 * n.succ) - n.succ * log (n.succ / exp 1) :=
by rw [stirling_seq, log_div, log_mul, sqrt_eq_rpow, log_rpow, real.log_pow, tsub_tsub];
  try { apply ne_of_gt }; positivity -- TODO: Make `positivity` handle `≠ 0` goals

/--
The sequence `log (stirling_seq (m + 1)) - log (stirling_seq (m + 2))` has the series expansion
   `∑ 1 / (2 * (k + 1) + 1) * (1 / 2 * (m + 1) + 1)^(2 * (k + 1))`
-/
lemma log_stirling_seq_diff_has_sum (m : ℕ) :
  has_sum (λ k : ℕ, (1 : ℝ) / (2 * k.succ + 1) * ((1 / (2 * m.succ + 1)) ^ 2) ^ k.succ)
  (log (stirling_seq m.succ) - log (stirling_seq m.succ.succ)) :=
begin
  change has_sum ((λ b : ℕ, 1 / (2 * (b : ℝ) + 1) * ((1 / (2 * m.succ + 1)) ^ 2) ^ b) ∘ succ) _,
  refine (has_sum_nat_add_iff 1).mpr _,
  convert (has_sum_log_one_add_inv $ cast_pos.mpr (succ_pos m)).mul_left ((m.succ : ℝ) + 1 / 2),
  { ext k,
    rw [← pow_mul, pow_add],
    push_cast,
    have : 2 * (k : ℝ) + 1 ≠ 0, {norm_cast, exact succ_ne_zero (2*k)},
    have : 2 * ((m : ℝ) + 1) + 1 ≠ 0, {norm_cast, exact succ_ne_zero (2*m.succ)},
    field_simp,
    ring },
  { have h : ∀ (x : ℝ) (hx : x ≠ 0), 1 + x⁻¹ = (x + 1) / x,
    { intros, rw [_root_.add_div, div_self hx, inv_eq_one_div], },
    simp only [log_stirling_seq_formula, log_div, log_mul, log_exp, factorial_succ, cast_mul,
      cast_succ, cast_zero, range_one, sum_singleton, h] { discharger :=
      `[norm_cast, apply_rules [mul_ne_zero, succ_ne_zero, factorial_ne_zero, exp_ne_zero]] },
    ring },
end

/-- The sequence `log ∘ stirling_seq ∘ succ` is monotone decreasing -/
lemma log_stirling_seq'_antitone : antitone (real.log ∘ stirling_seq ∘ succ) :=
antitone_nat_of_succ_le $ λ n, sub_nonneg.mp $ (log_stirling_seq_diff_has_sum n).nonneg $ λ m,
  by positivity

/--
We have a bound for successive elements in the sequence `log (stirling_seq k)`.
-/
lemma log_stirling_seq_diff_le_geo_sum (n : ℕ) :
  log (stirling_seq n.succ) - log (stirling_seq n.succ.succ) ≤
  (1 / (2 * n.succ + 1)) ^ 2 / (1 - (1 / (2 * n.succ + 1)) ^ 2) :=
begin
  have h_nonneg : 0 ≤ ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) := sq_nonneg _,
  have g : has_sum (λ k : ℕ, ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) ^ k.succ)
    ((1 / (2 * n.succ + 1)) ^ 2 / (1 - (1 / (2 * n.succ + 1)) ^ 2)),
  { have := (has_sum_geometric_of_lt_1 h_nonneg _).mul_left ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2),
    { simp_rw ←pow_succ at this,
      exact this, },
    rw [one_div, inv_pow],
    exact inv_lt_one (one_lt_pow ((lt_add_iff_pos_left 1).mpr $ by positivity) two_ne_zero) },
  have hab : ∀ (k : ℕ), (1 / (2 * (k.succ : ℝ) + 1)) * ((1 / (2 * n.succ + 1)) ^ 2) ^ k.succ ≤
    ((1 / (2 * n.succ + 1)) ^ 2) ^ k.succ,
  { refine λ k, mul_le_of_le_one_left (pow_nonneg h_nonneg k.succ) _,
    rw one_div,
    exact inv_le_one (le_add_of_nonneg_left $ by positivity) },
  exact has_sum_le hab (log_stirling_seq_diff_has_sum n) g,
end

/--
We have the bound  `log (stirling_seq n) - log (stirling_seq (n+1))` ≤ 1/(4 n^2)
-/
lemma log_stirling_seq_sub_log_stirling_seq_succ (n : ℕ) :
  log (stirling_seq n.succ) - log (stirling_seq n.succ.succ) ≤ 1 / (4 * n.succ ^ 2) :=
begin
  have h₁ : 0 < 4 * ((n : ℝ) + 1) ^ 2 := by positivity,
  have h₃ : 0 < (2 * ((n : ℝ) + 1) + 1) ^ 2 := by positivity,
  have h₂ : 0 < 1 - (1 / (2 * ((n : ℝ) + 1) + 1)) ^ 2,
  { rw ← mul_lt_mul_right h₃,
    have H : 0 < (2 * ((n : ℝ) + 1) + 1) ^ 2 - 1 := by nlinarith [@cast_nonneg ℝ _ n],
    convert H using 1; field_simp [h₃.ne'] },
  refine (log_stirling_seq_diff_le_geo_sum n).trans _,
  push_cast,
  rw div_le_div_iff h₂ h₁,
  field_simp [h₃.ne'],
  rw div_le_div_right h₃,
  ring_nf,
  norm_cast,
  linarith,
end

/-- For any `n`, we have `log_stirling_seq 1 - log_stirling_seq n ≤ 1/4 * ∑' 1/k^2`  -/
lemma log_stirling_seq_bounded_aux :
  ∃ (c : ℝ), ∀ (n : ℕ), log (stirling_seq 1) - log (stirling_seq n.succ) ≤ c :=
begin
  let d := ∑' k : ℕ, (1 : ℝ) / k.succ ^ 2,
  use (1 / 4 * d : ℝ),
  let log_stirling_seq' : ℕ → ℝ := λ k, log (stirling_seq k.succ),
  intro n,
  have h₁ : ∀ k, log_stirling_seq' k - log_stirling_seq' (k + 1) ≤ 1 / 4 * (1 / k.succ ^ 2) :=
  by { intro k, convert log_stirling_seq_sub_log_stirling_seq_succ k using 1, field_simp, },
  have h₂ : ∑ (k : ℕ) in range n, (1 : ℝ) / (k.succ) ^ 2 ≤ d := by
  { exact sum_le_tsum (range n) (λ k _, by positivity)
      ((summable_nat_add_iff 1).mpr $ real.summable_one_div_nat_pow.mpr one_lt_two) },
  calc
  log (stirling_seq 1) - log (stirling_seq n.succ) = log_stirling_seq' 0 - log_stirling_seq' n : rfl
  ... = ∑ k in range n, (log_stirling_seq' k - log_stirling_seq' (k + 1)) : by
    rw ← sum_range_sub' log_stirling_seq' n
  ... ≤ ∑ k in range n, (1/4) * (1 / k.succ^2) : sum_le_sum (λ k _, h₁ k)
  ... = 1 / 4 * ∑ k in range n, 1 / k.succ ^ 2 : by rw mul_sum
  ... ≤ 1 / 4 * d : mul_le_mul_of_nonneg_left h₂ $ by positivity,
end

/-- The sequence `log_stirling_seq` is bounded below for `n ≥ 1`. -/
lemma log_stirling_seq_bounded_by_constant : ∃ c, ∀ (n : ℕ), c ≤ log (stirling_seq n.succ) :=
begin
  obtain ⟨d, h⟩ := log_stirling_seq_bounded_aux,
  exact ⟨log (stirling_seq 1) - d, λ n, sub_le_comm.mp (h n)⟩,
end

/-- The sequence `stirling_seq` is positive for `n > 0`  -/
lemma stirling_seq'_pos (n : ℕ) : 0 < stirling_seq n.succ := by { unfold stirling_seq, positivity }

/--
The sequence `stirling_seq` has a positive lower bound.
-/
lemma stirling_seq'_bounded_by_pos_constant : ∃ a, 0 < a ∧ ∀ n : ℕ, a ≤ stirling_seq n.succ :=
begin
  cases log_stirling_seq_bounded_by_constant with c h,
  refine ⟨exp c, exp_pos _, λ n, _⟩,
  rw ← le_log_iff_exp_le (stirling_seq'_pos n),
  exact h n,
end

/-- The sequence `stirling_seq ∘ succ` is monotone decreasing -/
lemma stirling_seq'_antitone : antitone (stirling_seq ∘ succ) :=
λ n m h, (log_le_log (stirling_seq'_pos m) (stirling_seq'_pos n)).mp (log_stirling_seq'_antitone h)

/-- The limit `a` of the sequence `stirling_seq` satisfies `0 < a` -/
lemma stirling_seq_has_pos_limit_a :
  ∃ (a : ℝ), 0 < a ∧ tendsto stirling_seq at_top (𝓝 a) :=
begin
  obtain ⟨x, x_pos, hx⟩ := stirling_seq'_bounded_by_pos_constant,
  have hx' : x ∈ lower_bounds (set.range (stirling_seq ∘ succ)) := by simpa [lower_bounds] using hx,
  refine ⟨_, lt_of_lt_of_le x_pos (le_cInf (set.range_nonempty _) hx'), _⟩,
  rw ←filter.tendsto_add_at_top_iff_nat 1,
  exact tendsto_at_top_cinfi stirling_seq'_antitone ⟨x, hx'⟩,
end

/-!
 ### Part 2
 https://proofwiki.org/wiki/Stirling%27s_Formula#Part_2
-/

/-- The sequence `n / (2 * n + 1)` tends to `1/2` -/
lemma tendsto_self_div_two_mul_self_add_one :
  tendsto (λ (n : ℕ), (n : ℝ) / (2 * n + 1)) at_top (𝓝 (1 / 2)) :=
begin
  conv { congr, skip, skip, rw [one_div, ←add_zero (2 : ℝ)] },
  refine (((tendsto_const_div_at_top_nhds_0_nat 1).const_add (2 : ℝ)).inv₀
    ((add_zero (2 : ℝ)).symm ▸ two_ne_zero)).congr' (eventually_at_top.mpr ⟨1, λ n hn, _⟩),
  rw [add_div' (1 : ℝ) 2 n (cast_ne_zero.mpr (one_le_iff_ne_zero.mp hn)), inv_div],
end

/-- For any `n ≠ 0`, we have the identity
`(stirling_seq n)^4 / (stirling_seq (2*n))^2 * (n / (2 * n + 1)) = W n`, where `W n` is the
`n`-th partial product of Wallis' formula for `π / 2`. -/
lemma stirling_seq_pow_four_div_stirling_seq_pow_two_eq (n : ℕ) (hn : n ≠ 0) :
  ((stirling_seq n) ^ 4 / (stirling_seq (2 * n)) ^ 2) * (n / (2 * n + 1)) = wallis.W n :=
begin
  rw [bit0_eq_two_mul, stirling_seq, pow_mul, stirling_seq, wallis.W_eq_factorial_ratio],
  simp_rw [div_pow, mul_pow],
  rw [sq_sqrt, sq_sqrt],
  any_goals { positivity },
  have : (n : ℝ) ≠ 0, from cast_ne_zero.mpr hn,
  have : (exp 1) ≠ 0, from exp_ne_zero 1,
  have : ((2 * n)!: ℝ) ≠ 0, from cast_ne_zero.mpr (factorial_ne_zero (2 * n)),
  have : 2 * (n : ℝ) + 1 ≠ 0, by {norm_cast, exact succ_ne_zero (2*n)},
  field_simp,
  simp only [mul_pow, mul_comm 2 n, mul_comm 4 n, pow_mul],
  ring,
end

/--
Suppose the sequence `stirling_seq` (defined above) has the limit `a ≠ 0`.
Then the Wallis sequence `W n` has limit `a^2 / 2`.
-/
lemma second_wallis_limit (a : ℝ) (hane : a ≠ 0) (ha : tendsto stirling_seq at_top (𝓝 a)) :
  tendsto wallis.W at_top (𝓝 (a ^ 2 / 2)):=
begin
  refine tendsto.congr' (eventually_at_top.mpr ⟨1, λ n hn,
    stirling_seq_pow_four_div_stirling_seq_pow_two_eq n (one_le_iff_ne_zero.mp hn)⟩) _,
  have h : a ^ 2 / 2 = (a ^ 4 / a ^ 2) * (1 / 2),
  { rw [mul_one_div, ←mul_one_div (a ^ 4) (a ^ 2), one_div, ←pow_sub_of_lt a],
    norm_num },
  rw h,
  exact ((ha.pow 4).div ((ha.comp (tendsto_id.const_mul_at_top' two_pos)).pow 2)
    (pow_ne_zero 2 hane)).mul tendsto_self_div_two_mul_self_add_one,
end

/-- **Stirling's Formula** -/
theorem tendsto_stirling_seq_sqrt_pi : tendsto (λ (n : ℕ), stirling_seq n) at_top (𝓝 (sqrt π)) :=
begin
  obtain ⟨a, hapos, halimit⟩ := stirling_seq_has_pos_limit_a,
  have hπ : π / 2 = a ^ 2 / 2 := tendsto_nhds_unique wallis.tendsto_W_nhds_pi_div_two
    (second_wallis_limit a hapos.ne' halimit),
  rwa [(div_left_inj' (two_ne_zero' ℝ)).mp hπ, sqrt_sq hapos.le],
end

end stirling
