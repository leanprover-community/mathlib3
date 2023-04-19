/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
import data.real.basic
import data.real.sqrt
import data.nat.prime
import number_theory.primes_congruent_one
import number_theory.legendre_symbol.quadratic_reciprocity
import tactic.linear_combination

/-!
# IMO 2008 Q3
Prove that there exist infinitely many positive integers `n` such that `n^2 + 1` has a prime
divisor which is greater than `2n + √(2n)`.

# Solution
We first prove the following lemma: for every prime `p > 20`, satisfying `p ≡ 1 [MOD 4]`,
there exists `n ∈ ℕ` such that `p ∣ n^2 + 1` and `p > 2n + √(2n)`. Then the statement of the
problem follows from the fact that there exist infinitely many primes `p ≡ 1 [MOD 4]`.

To prove the lemma, notice that `p ≡ 1 [MOD 4]` implies `∃ n ∈ ℕ` such that `n^2 ≡ -1 [MOD p]`
and we can take this `n` such that `n ≤ p/2`. Let `k = p - 2n ≥ 0`. Then we have:
`k^2 + 4 = (p - 2n)^2 + 4 ≣ 4n^2 + 4 ≡ 0 [MOD p]`. Then `k^2 + 4 ≥ p` and so `k ≥ √(p - 4) > 4`.
Then `p = 2n + k ≥ 2n + √(p - 4) = 2n + √(2n + k - 4) > √(2n)` and we are done.
-/

open real

lemma p_lemma (p : ℕ) (hpp : nat.prime p) (hp_mod_4_eq_1 : p ≡ 1 [MOD 4]) (hp_gt_20 : p > 20) :
  ∃ n : ℕ, p ∣ n ^ 2 + 1 ∧ (p : ℝ) > 2 * n + sqrt(2 * n) :=
begin
  haveI := fact.mk hpp,
  have hp_mod_4_ne_3 : p % 4 ≠ 3, { linarith [(show p % 4 = 1, by exact hp_mod_4_eq_1)] },
  obtain ⟨y, hy⟩ := zmod.exists_sq_eq_neg_one_iff.mpr hp_mod_4_ne_3,

  let m := zmod.val_min_abs y,
  let n := int.nat_abs m,

  have hnat₁ : p ∣ n ^ 2 + 1,
  { refine int.coe_nat_dvd.mp _,
    simp only [int.nat_abs_sq, int.coe_nat_pow, int.coe_nat_succ, int.coe_nat_dvd.mp],
    refine (zmod.int_coe_zmod_eq_zero_iff_dvd (m ^ 2 + 1) p).mp _,
    simp only [int.cast_pow, int.cast_add, int.cast_one, zmod.coe_val_min_abs],
    rw [pow_two, ← hy], exact add_left_neg 1 },

  have hnat₂ : n ≤ p / 2 := zmod.nat_abs_val_min_abs_le y,
  have hnat₃ : p ≥ 2 * n, { linarith [nat.div_mul_le_self p 2] },

  set k : ℕ := p - 2 * n with hnat₄,

  have hnat₅ : p ∣ k ^ 2 + 4,
  { cases hnat₁ with x hx,
    have : (p:ℤ) ∣ k ^ 2 + 4,
    { use (p:ℤ) - 4 * n + 4 * x,
      have hcast₁ : (k:ℤ) = p - 2 * n, { assumption_mod_cast },
      have hcast₂ : (n:ℤ) ^ 2 + 1 = p * x, { assumption_mod_cast },
      linear_combination ((k:ℤ) + p - 2 * n)*hcast₁ + 4*hcast₂ },
    assumption_mod_cast },

  have hnat₆ : k ^ 2 + 4 ≥ p := nat.le_of_dvd (k ^ 2 + 3).succ_pos hnat₅,

  have hreal₁ : (k:ℝ) = p - 2 * n, { assumption_mod_cast },
  have hreal₂ : (p:ℝ) > 20,        { assumption_mod_cast },
  have hreal₃ : (k:ℝ) ^ 2 + 4 ≥ p, { assumption_mod_cast },

  have hreal₅ : (k:ℝ) > 4,
  { refine lt_of_pow_lt_pow 2 k.cast_nonneg _,
    linarith only [hreal₂, hreal₃] },

  have hreal₆ : (k:ℝ) > sqrt (2 * n),
  { refine lt_of_pow_lt_pow 2 k.cast_nonneg _,
    rw sq_sqrt (mul_nonneg zero_le_two n.cast_nonneg),
    linarith only [hreal₁, hreal₃, hreal₅] },

  exact ⟨n, hnat₁, by linarith only [hreal₆, hreal₁]⟩,
end

theorem imo2008_q3 : ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
  ∃ p : ℕ, nat.prime p ∧ p ∣ n ^ 2 + 1 ∧ (p : ℝ) > 2 * n + sqrt(2 * n) :=
begin
  intro N,
  obtain ⟨p, hpp, hineq₁, hpmod4⟩ := nat.exists_prime_gt_modeq_one (N ^ 2 + 20) four_ne_zero,
  obtain ⟨n, hnat, hreal⟩ := p_lemma p hpp hpmod4 (by linarith [hineq₁, nat.zero_le (N ^ 2)]),

  have hineq₂  : n ^ 2 + 1 ≥ p := nat.le_of_dvd (n ^ 2).succ_pos hnat,
  have hineq₃  : n * n ≥ N * N, { linarith [hineq₁, hineq₂] },
  have hn_ge_N : n ≥ N := nat.mul_self_le_mul_self_iff.mpr hineq₃,

  exact ⟨n, hn_ge_N, p, hpp, hnat, hreal⟩,
end
