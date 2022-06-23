/-
Copyright (c) 2022. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Fabian Kruse, Nikolas Kuhn
-/
import analysis.p_series
import analysis.special_functions.log.deriv
import analysis.special_functions.pow
import data.real.pi.wallis

/-!
# Stirling's formula

This file proves Theorem 90 from the [100 Theorem List] <https://www.cs.ru.nl/~freek/100/>.
It states that $n!$ grows asymptotically like $\sqrt{2\pi n}(\frac{n}{e})^n$.

## Proof outline

The proof follows: <https://proofwiki.org/wiki/Stirling%27s_Formula>.

We proceed in two parts.

### Part 1
We consider the fraction sequence $a_n$ of fractions $n!$ over $\sqrt{2n}(\frac{n}{e})^n$ and
proves that this sequence converges against a real, positve number $a$. For this the two main
ingredients are
 - taking the logarithm of the sequence and
 - use the series expansion of $\log(1 + x)$.

### Part 2
We use the fact that the series defined in part 1 converges againt a real number $a$ and prove that
$a = \sqrt{\pi}$. Here the main ingredient is the convergence of the Wallis product.
-/

open_locale big_operators real topological_space
open finset filter nat real

namespace stirling

/-!
 ### Part 1
 https://proofwiki.org/wiki/Stirling%27s_Formula#Part_1
-/

/--
Define `stirling_seq n` as $\frac{n!}{\sqrt{2n}/(\frac{n}{e})^n$.
Stirling's formula states that this sequence has limit $\sqrt(π)$.
-/
noncomputable def stirling_seq (n : ℕ) : ℝ :=
n.factorial / (sqrt (2 * n) * (n / exp 1) ^ n)

/-- Define `log_stirling_seq n` as the log of `stirling_seq n`. -/
noncomputable def log_stirling_seq (n : ℕ) : ℝ := log (stirling_seq n)

/--
We have the expression
`log_stirling_seq (n + 1) = log(n + 1)! - 1 / 2 * log(2 * n) - n * log ((n + 1) / e)`.
-/
lemma log_stirling_seq_formula (n : ℕ) : log_stirling_seq n.succ =
  log n.succ.factorial - 1 / 2 * log (2 * n.succ) - n.succ * log (n.succ / exp 1) :=
begin
  have h3, from sqrt_ne_zero'.mpr (mul_pos two_pos $ cast_pos.mpr (succ_pos n)),
  have h4 : 0 ≠ ((n.succ : ℝ) / exp 1) ^ n.succ, from
    ne_of_lt (pow_pos (div_pos (cast_pos.mpr n.succ_pos ) (exp_pos 1)) n.succ),
  rw [log_stirling_seq, stirling_seq, log_div, log_mul, sqrt_eq_rpow, log_rpow, log_pow],
  { linarith },
  { refine (zero_lt_mul_left two_pos).mpr _,
    rw ←cast_zero,
    exact cast_lt.mpr (succ_pos n), },
  { exact h3, },
  { exact h4.symm, },
  { exact cast_ne_zero.mpr n.succ.factorial_ne_zero, },
  { apply (mul_ne_zero h3 h4.symm), },
end

/--
The sequence `log_stirling_seq (m + 1) - log_stirling_seq (m + 2)` has the series expansion
   `∑ 1 / (2 * (k + 1) + 1) * (1 / 2 * (m + 1) + 1)^(2 * (k + 1))`
-/
lemma log_stirling_seq_diff_has_sum (m : ℕ) :
  has_sum (λ k : ℕ, (1 : ℝ) / (2 * k.succ + 1) * ((1 / (2 * m.succ + 1)) ^ 2) ^ k.succ)
  (log_stirling_seq m.succ - log_stirling_seq m.succ.succ) :=
begin
  change
    has_sum ((λ b : ℕ, 1 / (2 * (b : ℝ) + 1) * ((1 / (2 * m.succ + 1)) ^ 2) ^ b) ∘ succ) _,
  rw has_sum_nat_add_iff 1,
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
  { apply_instance }
end

/-- The sequence `log_stirling_seq ∘ succ` is monotone decreasing -/
lemma log_stirling_seq'_antitone : antitone (log_stirling_seq ∘ succ) :=
begin
  apply antitone_nat_of_succ_le,
  intro n,
  rw [← sub_nonneg, ← succ_eq_add_one],
  refine (log_stirling_seq_diff_has_sum n).nonneg _,
  norm_num,
  simp only [one_div],
  intro m,
  refine mul_nonneg _ _,
  all_goals {refine inv_nonneg.mpr _, norm_cast, exact (zero_le _)},
end

/--
We have the bound  `log_stirling_seq n - log_stirling_seq (n+1) ≤ 1/(2n+1)^2* 1/(1-(1/2n+1)^2)`.
-/
lemma log_stirling_seq_diff_le_geo_sum (n : ℕ) :
  log_stirling_seq n.succ - log_stirling_seq n.succ.succ ≤
  (1 / (2 * n.succ + 1)) ^ 2 / (1 - (1 / (2 * n.succ + 1)) ^ 2) :=
begin
  have h_nonneg : 0 ≤ ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2),
  { rw [cast_succ, one_div, inv_pow, inv_nonneg], norm_cast, exact zero_le', },
  have g : has_sum (λ k : ℕ, ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) ^ k.succ)
    ((1 / (2 * n.succ + 1)) ^ 2 / (1 - (1 / (2 * n.succ + 1)) ^ 2)),
  { have h_pow_succ := λ k : ℕ,
      symm (pow_succ ((1 / (2 * ((n : ℝ) + 1) + 1)) ^ 2) k),
    have hlt : (1 / (2 * (n.succ : ℝ) + 1)) ^ 2 < 1,
    { simp only [cast_succ, one_div, inv_pow],
      refine inv_lt_one _,
      norm_cast,
      simp only [nat.one_lt_pow_iff, ne.def, zero_eq_bit0, nat.one_ne_zero, not_false_iff,
        lt_add_iff_pos_left, canonically_ordered_comm_semiring.mul_pos, succ_pos', and_self], },
    exact (has_sum_geometric_of_lt_1 h_nonneg hlt).mul_left ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) },
  have hab : ∀ (k : ℕ), (1 / (2 * (k.succ : ℝ) + 1)) * ((1 / (2 * n.succ + 1)) ^ 2) ^ k.succ ≤
    ((1 / (2 * n.succ + 1)) ^ 2) ^ k.succ,
  { intro k,
    have h_zero_le : 0 ≤ ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) ^ k.succ := pow_nonneg h_nonneg _,
    have h_left : 1 / (2 * (k.succ : ℝ) + 1) ≤ 1,
    { rw [cast_succ, one_div],
      refine inv_le_one _,
      norm_cast,
      exact (le_add_iff_nonneg_left 1).mpr zero_le', },
    exact mul_le_of_le_one_left h_zero_le h_left, },
  exact has_sum_le hab (log_stirling_seq_diff_has_sum n) g,
end

/--
We have the bound  `log_stirling_seq n - log_stirling_seq (n+1)` ≤ 1/(4 n^2)
-/
lemma log_stirling_seq_sub_log_stirling_seq_succ (n : ℕ) :
  log_stirling_seq n.succ - log_stirling_seq n.succ.succ ≤ 1 / (4 * n.succ ^ 2) :=
begin
  have h₁ : 0 < 4 * ((n : ℝ) + 1) ^ 2 := by nlinarith [@cast_nonneg ℝ _ n],
  have h₃ : 0 < (2 * ((n : ℝ) + 1) + 1) ^ 2 := by nlinarith [@cast_nonneg ℝ _ n],
  have h₂ : 0 < 1 - (1 / (2 * ((n : ℝ) + 1) + 1)) ^ 2,
  { rw ← mul_lt_mul_right h₃,
    have H : 0 < (2 * ((n : ℝ) + 1) + 1) ^ 2 - 1 := by nlinarith [@cast_nonneg ℝ _ n],
    convert H using 1; field_simp [h₃.ne'] },
  refine (log_stirling_seq_diff_le_geo_sum n).trans _,
  push_cast at *,
  rw div_le_div_iff h₂ h₁,
  field_simp [h₃.ne'],
  rw div_le_div_right h₃,
  ring_nf,
  norm_cast,
  linarith,
end

/-- For any `n`, we have `log_stirling_seq 1 - log_stirling_seq n ≤ 1/4 * ∑' 1/k^2`  -/
lemma log_stirling_seq_bounded_aux :
  ∃ (c : ℝ), ∀ (n : ℕ), log_stirling_seq 1 - log_stirling_seq n.succ ≤ c :=
begin
  let d := ∑' k : ℕ, (1 : ℝ) / k.succ ^ 2,
  use (1 / 4 * d : ℝ),
  let log_stirling_seq' : ℕ → ℝ := λ k : ℕ, log_stirling_seq k.succ,
  intro n,
  calc
  log_stirling_seq 1 - log_stirling_seq n.succ = log_stirling_seq' 0 - log_stirling_seq' n : rfl
  ... = ∑ k in range n, (log_stirling_seq' k - log_stirling_seq' (k + 1)) : by
    rw ← sum_range_sub' log_stirling_seq' n
  ... ≤ ∑ k in range n, (1/4) * (1 / k.succ^2) : by
  { apply sum_le_sum,
    intros k hk,
    convert log_stirling_seq_sub_log_stirling_seq_succ k using 1,
    field_simp, }
  ... = 1 / 4 * ∑ k in range n, 1 / k.succ ^ 2 : by rw mul_sum
  ... ≤ 1 / 4 * d : by
  { refine (mul_le_mul_left _).mpr _, { exact one_div_pos.mpr four_pos, },
    refine sum_le_tsum (range n) (λ k _, _)
      ((summable_nat_add_iff 1).mpr (real.summable_one_div_nat_pow.mpr one_lt_two)),
    apply le_of_lt,
    rw one_div_pos,
    rw sq_pos_iff,
    exact nonzero_of_invertible ↑(succ k), },
end

/-- The sequence `log_stirling_seq` is bounded below for `n ≥ 1`. -/
lemma log_stirling_seq_bounded_by_constant : ∃ c, ∀ (n : ℕ), c ≤ log_stirling_seq n.succ :=
begin
  obtain ⟨d, h⟩ := log_stirling_seq_bounded_aux,
  use log_stirling_seq 1 - d,
  intro n,
  exact sub_le.mp (h n),
end

/-- The sequence `stirling_seq` is positive for `n > 0`  -/
lemma stirling_seq'_pos (n : ℕ) : 0 < stirling_seq n.succ :=
begin
  dsimp only [stirling_seq],
  apply_rules [div_pos, cast_pos.mpr, mul_pos, factorial_pos, exp_pos, pow_pos, real.sqrt_pos.mpr,
    two_pos, succ_pos] 7 {md := reducible}; apply_instance,
end

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

/--
Define `wallis_inside_prod n` as `2 * n / (2 * n - 1) * 2 * n / (2 * n + 1)`.
This is the term appearing inside the Wallis product
-/
noncomputable def wallis_inside_prod (n : ℕ) : ℝ :=
  (((2 : ℝ) * n) / (2 * n - 1)) * ((2 * n) / (2 * n + 1))

/-- The Wallis product $\prod_{n=1}^k \frac{2n}{2n-1}\frac{2n}{2n+1}$
  converges to `π/2` as `k → ∞` -/
lemma equality1 :
  tendsto (λ (k : ℕ), ∏ i in Ico 1 k.succ, wallis_inside_prod i) at_top (𝓝 (π / 2)) :=
begin
  convert tendsto_prod_pi_div_two,
  funext,
  rw [range_eq_Ico, ← prod_Ico_add _ 0 k 1],
  congr,
  funext,
  rw wallis_inside_prod,
  push_cast,
  rw [zero_add, mul_add, mul_one, add_comm, ← add_sub, add_assoc],
  congr,
  linarith,
end

/-- For `n : ℕ`, define `w n` as `2^(4*n) * n!^4 / ((2*n)!^2 * (2*n + 1))` -/
noncomputable def w (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (4 * n) * (n.factorial) ^ 4) / ((((2 * n).factorial) ^ 2) * (2 * (n : ℝ) + 1))

/-- The sequence `w n` converges to `π/2` -/
lemma wallis_consequence : tendsto (λ (n : ℕ), w n) at_top (𝓝 (π/2)) :=
begin
  convert equality1,
  ext n,
  induction n with d hd,
  { rw [w, Ico_self, cast_zero, prod_empty, mul_zero, mul_zero, pow_zero, factorial_zero, cast_one,
      one_pow, one_pow, mul_zero, zero_add, mul_one, div_one], },
  rw [prod_Ico_succ_top, ← hd, w, w, wallis_inside_prod],
  repeat {rw mul_succ},
  rw [factorial_succ, factorial_succ, factorial_succ],
  push_cast,
  rw [zero_add, one_add_one_eq_two],
  rw [pow_two, pow_two, pow_add],
  have : 2 * ((d : ℝ) + 1) + 1 ≠ 0, by {norm_cast, exact succ_ne_zero _},
  have : 2 * (d : ℝ) + 1 ≠ 0, by {norm_cast, exact succ_ne_zero _},
  have : 2 * ((d : ℝ) + 1) - 1 ≠ 0, by {ring_nf, norm_cast, exact succ_ne_zero _},
  have : 2 * (d : ℝ) + 1 + 1 ≠ 0, by {norm_cast, exact succ_ne_zero _},
  have : (_ ≠ (0 : ℝ)) := cast_ne_zero.mpr (factorial_ne_zero (2 * d)),
  have : ((2 * d).factorial : ℝ) * ((2 * d).factorial : ℝ) * (2 * (d : ℝ) + 1) ≠ 0, by
    apply_rules [mul_ne_zero],
  have : (2 * (d : ℝ) + 1 + 1) * ((2 * ↑d + 1) * ↑((2 * d).factorial)) *
        ((2 * ↑d + 1 + 1) * ((2 * ↑d + 1) * ↑((2 * d).factorial))) * (2 * (↑d + 1) + 1) ≠ 0, by
    apply_rules [mul_ne_zero],
  field_simp,
  ring_nf,
  exact succ_le_succ (zero_le d),
end

/-- For `n : ℕ`, define `c n` as
$\sqrt{2n}(\frac{n}{e})^{4n}*\frac{2^{4n}}{(\sqrt{4n}(\frac{2n}{e})^(2n))^2 * (2n+1)}$ -/
noncomputable def c (n : ℕ) : ℝ := ((sqrt (2 * n) * ((n / (exp 1)) ^ n)) ^ 4) * 2 ^ (4 * n) /
  (((sqrt (4 * n) * (((2 * n) / (exp 1))) ^ (2 * n))) ^ 2 * (2 * n + 1))

/-- For any `n : ℕ`, we have `c n` = n / (2 * n + 1) -/
lemma rest_cancel (n : ℕ) : (n : ℝ) / (2 * n + 1) = c n :=
begin
  rw c,
  have h₀ : 4 = 2 * 2, by refl,
  rw [mul_pow, mul_pow, h₀, pow_mul, sq_sqrt, sq_sqrt],
  { cases n,
    { rw [cast_zero, zero_div, mul_zero, zero_pow, zero_mul, zero_mul, zero_div],
    exact two_pos },
    { have h₁ : 2 * (n.succ : ℝ) + 1 ≠ 0,
    by { norm_cast, exact succ_ne_zero (2*n.succ) },
    have h₂ : exp 1 ≠ 0, from exp_ne_zero 1,
    have h₃ : (n.succ : ℝ) ≠ 0, by exact cast_ne_zero.mpr (succ_ne_zero n),
    field_simp,
    repeat {rw [← pow_mul]},
    rw [← h₀, mul_assoc 2 n.succ 2, mul_left_comm 2 n.succ 2, ← h₀],
    rw [mul_pow (2 : ℝ) _ (n.succ * 4), mul_comm 4 n.succ],
    ring_nf }, },
  all_goals {norm_cast, linarith},
end

/-- The sequence `c n` has limit `1/2` -/
lemma rest_has_limit_one_half : tendsto (λ (n : ℕ), c n) at_top (𝓝 (1 / 2)) :=
begin
  apply (tendsto.congr rest_cancel),
  have h : tendsto (λ (k : ℕ), (((k : ℝ) / (2 * (k : ℝ) + 1))⁻¹))
    at_top (𝓝 (((1 : ℝ) / 2))⁻¹),
  { have hsucc : tendsto (λ (k : ℕ), (((k.succ : ℝ) / (2 * (k.succ : ℝ) + 1))⁻¹)) at_top
      (𝓝 (((1 : ℝ) / 2))⁻¹),
    { have hx : ∀ (k : ℕ), (2 : ℝ) + k.succ⁻¹ = ((k.succ : ℝ) / (2 * k.succ + 1))⁻¹, by
      { intro k, have hxne : (k.succ : ℝ) ≠ 0 := nonzero_of_invertible (k.succ : ℝ), field_simp, },
      simp only [one_div, inv_inv],
      apply (tendsto.congr hx),
      have g := tendsto.add tendsto_const_nhds ((tendsto_add_at_top_iff_nat 1).mpr
        (tendsto_inverse_at_top_nhds_0_nat)),
      rw [add_zero] at g,
      exact g, },
    exact (tendsto_add_at_top_iff_nat 1).mp hsucc, },
  have h2: ((1 : ℝ) / 2)⁻¹ ≠ 0, by
    simp only [one_div, inv_inv, ne.def, bit0_eq_zero, one_ne_zero, not_false_iff],
  convert tendsto.inv₀ h h2,
  { simp only [inv_inv, one_div] },
  { rw inv_inv },
end

/--
Suppose the sequence `stirling_seq` (defined above) has a nonzero limit `a ≠ 0`.
Then the sequence `1/(log_stirling_seq n)^2` has the limit `1/a^2`.
-/
lemma stirling_seq_aux3 (a : ℝ) (hane : a ≠ 0)
  (ha : tendsto (λ (n : ℕ), stirling_seq n) at_top (𝓝 a)) :
  tendsto (λ (n : ℕ), (1 / (stirling_seq n)) ^ 2) at_top (𝓝 ((1 / a) ^ 2)) :=
begin
 convert tendsto.pow (tendsto.congr (λ n, (one_div (stirling_seq n)).symm)
   (tendsto.inv₀ ha hane)) 2,
 rw [one_div],
end

/-- For any `n ≠ 0`, we have the identity
`(stirling_seq n)^4/(stirling_seq (2*n))^2 * (c n) = w n`. -/
lemma expand_in_limit (n : ℕ) (hn : n ≠ 0) :
  (stirling_seq n) ^ 4 * (1 / (stirling_seq (2 * n))) ^ 2 * c n = w n :=
begin
  rw [stirling_seq, stirling_seq, c, w],
  have : (4 : ℝ) = (2 : ℝ) * 2, by norm_cast,
  rw this,
  rw [cast_mul 2 n, cast_two, ←mul_assoc],
  rw sqrt_mul (mul_self_nonneg 2) (n : ℝ),
  rw sqrt_mul_self zero_le_two,
  have h₀ : (n : ℝ) ≠ 0, from cast_ne_zero.mpr hn,
  have h₁ : sqrt (2 * (n : ℝ)) ≠ 0, from
    (sqrt_ne_zero'.mpr $ mul_pos two_pos $ cast_pos.mpr (zero_lt_iff.mpr hn)),
  have h₂ : (exp 1) ≠ 0, from exp_ne_zero 1,
  have h₃ : ((2 * n).factorial : ℝ) ≠ 0, from cast_ne_zero.mpr (factorial_ne_zero (2 * n)),
  have h₄ : sqrt (n : ℝ) ≠ 0, from sqrt_ne_zero'.mpr (cast_pos.mpr (zero_lt_iff.mpr hn)),
  have h₅ : (((2 * n) : ℕ) : ℝ) ≠ 0, from
    cast_ne_zero.mpr (mul_ne_zero two_ne_zero hn),
  have h₆ : sqrt (4 * (n : ℝ)) ≠ 0, from
    sqrt_ne_zero'.mpr (mul_pos four_pos $ cast_pos.mpr (zero_lt_iff.mpr hn)),
  have h₇ : 2 * (n : ℝ) + 1 ≠ 0, by {norm_cast, exact succ_ne_zero (2*n)},
  field_simp,
  ring_nf,
end

/-- For any `n : ℕ`, we have the identity
(stirling_seq n+1)^4/ (stirling_seq (2(n+1)))^2 * (c n+1) = w n+1. -/
lemma expand_in_limit' (n : ℕ) :
  (stirling_seq n.succ) ^ 4 * (1 / (stirling_seq (2 * n.succ))) ^ 2 * c n.succ = w n.succ :=
  expand_in_limit n.succ (succ_ne_zero n)

/--
Suppose the sequence `stirling_seq` (defined above) has the limit `a ≠ 0`.
Then the sequence `w` has limit `a^2/2`
-/
lemma second_wallis_limit (a : ℝ) (hane : a ≠ 0) (ha : tendsto stirling_seq at_top (𝓝 a)) :
  tendsto w at_top (𝓝 (a ^ 2 / 2)):=
begin
  rw ←(filter.tendsto_add_at_top_iff_nat 1),
  apply tendsto.congr expand_in_limit',
  let qn := λ (n : ℕ), stirling_seq n ^ 4 * (1 / stirling_seq (2 * n)) ^ 2 * c n,
  have hqn :
    ∀ (n : ℕ), qn n.succ = stirling_seq n.succ ^ 4 * (1 / stirling_seq (2 * n.succ)) ^ 2 * c n.succ
    := by tauto,
  apply tendsto.congr hqn,
  rw filter.tendsto_add_at_top_iff_nat 1,
  have has : tendsto (λ (n : ℕ), stirling_seq n ^ 4 * (1 / stirling_seq (2 * n)) ^ 2)
    at_top (𝓝 (a ^ 2)),
  { convert tendsto.mul (tendsto.pow ha 4)
      ((stirling_seq_aux3 a hane ha).comp (tendsto_id.const_mul_at_top' two_pos)),
    field_simp,
    ring_nf, },
  convert tendsto.mul has rest_has_limit_one_half,
  rw [one_div, div_eq_mul_inv],
end

/-- **Stirling's Formula** -/
theorem stirling_seq_has_limit_sqrt_pi : tendsto (λ (n : ℕ), stirling_seq n) at_top (𝓝 (sqrt π)) :=
begin
  obtain ⟨a, hapos, halimit⟩ := stirling_seq_has_pos_limit_a,
  have hπ : π / 2 = a ^ 2 / 2 := tendsto_nhds_unique wallis_consequence
    (second_wallis_limit a (ne_of_gt hapos) halimit),
  field_simp at hπ,
  rw ← (sq_sqrt (le_of_lt pi_pos)) at hπ,
  have h := (sq_eq_sq (sqrt_nonneg π) (le_of_lt hapos)).mp hπ,
  convert halimit,
end

end stirling
