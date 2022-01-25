/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
import data.real.basic
import data.real.sqrt
import data.nat.prime
import number_theory.primes_congruent_one
import number_theory.quadratic_reciprocity

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
  obtain ⟨y, hy⟩ := (zmod.exists_sq_eq_neg_one_iff_mod_four_ne_three p).mpr hp_mod_4_ne_3,

  let m := zmod.val_min_abs y,
  let n := int.nat_abs m,

  have hnat₁ : p ∣ n ^ 2 + 1,
  { refine int.coe_nat_dvd.mp _,
    simp only [int.nat_abs_sq, int.coe_nat_pow, int.coe_nat_succ, int.coe_nat_dvd.mp],
    refine (zmod.int_coe_zmod_eq_zero_iff_dvd (m ^ 2 + 1) p).mp _,
    simp only [int.cast_pow, int.cast_add, int.cast_one, zmod.coe_val_min_abs],
    rw hy, exact add_left_neg 1 },

  have hnat₂ : n ≤ p / 2 := zmod.nat_abs_val_min_abs_le y,
  have hnat₃ : p ≥ 2 * n, { linarith [nat.div_mul_le_self p 2] },

  set k : ℕ := p - 2 * n with hnat₄,

  have hnat₅ : p ∣ k ^ 2 + 4,
  { cases hnat₁ with x hx,
    let p₁ := (p : ℤ), let n₁ := (n : ℤ), let k₁ := (k : ℤ), let x₁ := (x : ℤ),
    have : p₁ ∣ k₁ ^ 2 + 4,
    { use p₁ - 4 * n₁ + 4 * x₁,
      have hcast₁ : k₁ = p₁ - 2 * n₁, { assumption_mod_cast },
      have hcast₂ : n₁ ^ 2 + 1 = p₁ * x₁, { assumption_mod_cast },
      calc  k₁ ^ 2 + 4
          = (p₁ - 2 * n₁) ^ 2 + 4                   : by rw hcast₁
      ... = p₁ ^ 2 - 4 * p₁ * n₁ + 4 * (n₁ ^ 2 + 1) : by ring
      ... = p₁ ^ 2 - 4 * p₁ * n₁ + 4 * (p₁ * x₁)    : by rw hcast₂
      ... = p₁ * (p₁ - 4 * n₁ + 4 * x₁)             : by ring },
    assumption_mod_cast },

  have hnat₆ : k ^ 2 + 4 ≥ p := nat.le_of_dvd (k ^ 2 + 3).succ_pos hnat₅,

  let p₀ := (p : ℝ), let n₀ := (n : ℝ), let k₀ := (k : ℝ),

  have hreal₁ : p₀ = 2 * n₀ + k₀, { linarith [(show k₀ = p₀ - 2 * n₀, by assumption_mod_cast)] },
  have hreal₂ : p₀ > 20,          { assumption_mod_cast },
  have hreal₃ : k₀ ^ 2 + 4 ≥ p₀,  { assumption_mod_cast },

  have hreal₄ : k₀ ≥ sqrt(p₀ - 4),
  { calc k₀ = sqrt(k₀ ^ 2) : eq.symm (sqrt_sq (nat.cast_nonneg k))
    ...     ≥ sqrt(p₀ - 4) : sqrt_le_sqrt (by linarith [hreal₃]) },

  have hreal₅ : k₀ > 4,
  { calc k₀ ≥ sqrt(p₀ - 4) : hreal₄
    ...     > sqrt(4 ^ 2)  : sqrt_lt_sqrt (by norm_num) (by linarith [hreal₂])
    ...     = 4            : sqrt_sq zero_lt_four.le },

  have hreal₆ : p₀ > 2 * n₀ + sqrt(2 * n),
  { calc p₀ = 2 * n₀ + k₀                    : hreal₁
    ...     ≥ 2 * n₀ + sqrt(p₀ - 4)          : add_le_add_left hreal₄ _
    ...     = 2 * n₀ + sqrt(2 * n₀ + k₀ - 4) : by rw hreal₁
    ...     > 2 * n₀ + sqrt(2 * n₀) : add_lt_add_left
        (sqrt_lt_sqrt (mul_nonneg zero_le_two n.cast_nonneg) $ by linarith [hreal₅]) (2 * n₀) },

  exact ⟨n, hnat₁, hreal₆⟩,
end

theorem imo2008_q3 : ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
  ∃ p : ℕ, nat.prime p ∧ p ∣ n ^ 2 + 1 ∧ (p : ℝ) > 2 * n + sqrt(2 * n) :=
begin
  intro N,
  obtain ⟨p, hpp, hineq₁, hpmod4⟩ := nat.exists_prime_ge_modeq_one 4 (N ^ 2 + 21) zero_lt_four,
  obtain ⟨n, hnat, hreal⟩ := p_lemma p hpp hpmod4 (by linarith [hineq₁, nat.zero_le (N ^ 2)]),

  have hineq₂  : n ^ 2 + 1 ≥ p := nat.le_of_dvd (n ^ 2).succ_pos hnat,
  have hineq₃  : n * n ≥ N * N, { linarith [hineq₁, hineq₂, (sq n), (sq N)] },
  have hn_ge_N : n ≥ N := nat.mul_self_le_mul_self_iff.mpr hineq₃,

  exact ⟨n, hn_ge_N, p, hpp, hnat, hreal⟩,
end
