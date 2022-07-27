/-
Copyright (c) 2022. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Fabian Kruse, Nikolas Kuhn
-/
import analysis.p_series
import analysis.special_functions.log.deriv

/-!
# Stirling's formula

This file proves Theorem 90 from the [100 Theorem List] <https://www.cs.ru.nl/~freek/100/>.
It states that $n!$ grows asymptotically like $\sqrt{2\pi n}(\frac{n}{e})^n$.
TODO: Add Part 2 to complete the proof

## Proof outline

The proof follows: <https://proofwiki.org/wiki/Stirling%27s_Formula>.

### Part 1
We consider the fraction sequence $a_n$ of fractions $\frac{n!}{\sqrt{2n}(\frac{n}{e})^n}$ and
prove that this sequence converges against a real, positive number $a$. For this the two main
ingredients are
 - taking the logarithm of the sequence and
 - use the series expansion of $\log(1 + x)$.
-/

open_locale topological_space big_operators
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

end stirling
