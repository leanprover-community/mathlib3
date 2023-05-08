/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
import topology.instances.ennreal
import data.nat.squarefree

/-!
# Divergence of the Prime Reciprocal Series

This file proves Theorem 81 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).
The theorem states that the sum of the reciprocals of all prime numbers diverges.
The formalization follows Erdős's proof by upper and lower estimates.

## Proof outline

1. Assume that the sum of the reciprocals of the primes converges.
2. Then there exists a `k : ℕ` such that, for any `x : ℕ`, the sum of the reciprocals of the primes
   between `k` and `x + 1` is less than 1/2 (`sum_lt_half_of_not_tendsto`).
3. For any `x : ℕ`, we can partition `range x` into two subsets (`range_sdiff_eq_bUnion`):
    * `M x k`, the subset of those `e` for which `e + 1` is a product of powers of primes smaller
      than or equal to `k`;
    * `U x k`, the subset of those `e` for which there is a prime `p > k` that divides `e + 1`.
4. Then `|U x k|` is bounded by the sum over the primes `p > k` of the number of multiples of `p`
   in `(k, x]`, which is at most `x / p`. It follows that `|U x k|` is at most `x` times the sum of
  the reciprocals of the primes between `k` and `x + 1`, which is less than 1/2 as noted in (2), so
  `|U x k| < x / 2` (`card_le_mul_sum`).
5. By factoring `e + 1 = (m + 1)² * (r + 1)`, `r + 1` squarefree and `m + 1 ≤ √x`, and noting that
   squarefree numbers correspond to subsets of `[1, k]`, we find that `|M x k| ≤ 2 ^ k * √x`
   (`card_le_two_pow_mul_sqrt`).
6. Finally, setting `x := (2 ^ (k + 1))²` (`√x = 2 ^ (k + 1)`), we find that
   `|M x k| ≤ 2 ^ k * 2 ^ (k + 1) = x / 2`. Combined with the strict bound for `|U k x|` from (4),
   `x = |M x k| + |U x k| < x / 2 + x / 2 = x`.

## References

https://en.wikipedia.org/wiki/Divergence_of_the_sum_of_the_reciprocals_of_the_primes
-/

open_locale big_operators
open_locale classical
open filter finset

/--
The primes in `(k, x]`.
-/
noncomputable def P (x k : ℕ) := {p ∈ range (x + 1) | k < p ∧ nat.prime p}

/--
The union over those primes `p ∈ (k, x]` of the sets of `e < x` for which `e + 1` is a multiple
of `p`, i.e., those `e < x` for which there is a prime `p ∈ (k, x]` that divides `e + 1`.
-/
noncomputable def U (x k : ℕ) := finset.bUnion (P x k) (λ p, {e ∈ range x | p ∣ e + 1})

/--
Those `e < x` for which `e + 1` is a product of powers of primes smaller than or equal to `k`.
-/
noncomputable def M (x k : ℕ) := {e ∈ range x | ∀ p : ℕ, (nat.prime p ∧ p ∣ e + 1) → p ≤ k}

/--
If the sum of the reciprocals of the primes converges, there exists a `k : ℕ` such that the sum of
the reciprocals of the primes greater than `k` is less than 1/2.

More precisely, for any `x : ℕ`, the sum of the reciprocals of the primes between `k` and `x + 1`
is less than 1/2.
-/
lemma sum_lt_half_of_not_tendsto
  (h : ¬ tendsto (λ n, ∑ p in {p ∈ range n | nat.prime p}, (1 / (p : ℝ))) at_top at_top) :
  ∃ k, ∀ x, ∑ p in P x k, 1 / (p : ℝ) < 1 / 2 :=
begin
  have h0 : (λ n, ∑ p in {p ∈ range n | nat.prime p}, (1 / (p : ℝ)))
          = λ n, ∑ p in range n, ite (nat.prime p) (1 / (p : ℝ)) 0,
  { simp only [sum_filter, filter_congr_decidable, sep_def] },

  have hf : ∀ n : ℕ, 0 ≤ ite (nat.prime n) (1 / (n : ℝ)) 0,
  { intro n, split_ifs,
    { simp only [one_div, inv_nonneg, nat.cast_nonneg] },
    { exact le_rfl } },

  rw [h0, ← summable_iff_not_tendsto_nat_at_top_of_nonneg hf, summable_iff_vanishing] at h,
  obtain ⟨s, h⟩ := h (set.Ioo (-1) (1/2)) (is_open_Ioo.mem_nhds (by norm_num)),
  obtain ⟨k, hk⟩ := exists_nat_subset_range s,
  use k,
  intro x,

  rw [P, sep_def, filter_congr_decidable, ←filter_filter, sum_filter],
  refine (h _ _).2,
  rw disjoint_iff_ne,
  simp_intros a ha b hb only [mem_filter],
  exact ((mem_range.mp (hk hb)).trans ha.2).ne',
end

/--
Removing from {0, ..., x - 1} those elements `e` for which `e + 1` is a product of powers of primes
smaller than or equal to `k` leaves those `e` for which there is a prime `p > k` that divides
`e + 1`, or the union over those primes `p > k` of the sets of `e`s for which `e + 1` is a multiple
of `p`.
-/
lemma range_sdiff_eq_bUnion {x k : ℕ} : range x \ M x k = U x k :=
begin
  ext e,
  simp only [mem_bUnion, not_and, mem_sdiff, sep_def, mem_filter, mem_range, U, M, P],
  push_neg,
  split,
  { rintros ⟨hex, hexh⟩,
    obtain ⟨p, ⟨hpp, hpe1⟩, hpk⟩ := hexh hex,
    refine ⟨p, _, ⟨hex, hpe1⟩⟩,
    exact ⟨(nat.le_of_dvd e.succ_pos hpe1).trans_lt (nat.succ_lt_succ hex), hpk, hpp⟩ },
  { rintros ⟨p, hpfilter, ⟨hex, hpe1⟩⟩,
    rw imp_iff_right hex,
    exact ⟨hex, ⟨p, ⟨hpfilter.2.2, hpe1⟩, hpfilter.2.1⟩⟩ },
end

/--
The number of `e < x` for which `e + 1` has a prime factor `p > k` is bounded by `x` times the sum
of reciprocals of primes in `(k, x]`.
-/
lemma card_le_mul_sum {x k : ℕ} : (card (U x k) : ℝ) ≤ x * ∑ p in P x k, 1 / p :=
begin
  let P := {p ∈ range (x + 1) | k < p ∧ nat.prime p},
  let N := λ p, {e ∈ range x | p ∣ e + 1},
  have h : card (finset.bUnion P N) ≤ ∑ p in P, card (N p) := card_bUnion_le,

  calc  (card (finset.bUnion P N) : ℝ)
      ≤ ∑ p in P, card (N p)  : by assumption_mod_cast
  ... ≤ ∑ p in P, x * (1 / p) : sum_le_sum (λ p hp, _)
  ... = x * ∑ p in P, 1 / p   : mul_sum.symm,
  simp only [mul_one_div, N, sep_def, filter_congr_decidable, nat.card_multiples, nat.cast_div_le],
end

/--
The number of `e < x` for which `e + 1` is a squarefree product of primes smaller than or equal to
`k` is bounded by `2 ^ k`, the number of subsets of `[1, k]`.
-/
lemma card_le_two_pow {x k : ℕ} : card {e ∈ M x k | squarefree (e + 1)} ≤ 2 ^ k :=
begin
  let M₁ := {e ∈ M x k | squarefree (e + 1)},
  let f := λ s, finset.prod s (λ a, a) - 1,
  let K := powerset (image nat.succ (range k)),

  -- Take `e` in `M x k`. If `e + 1` is squarefree, then it is the product of a subset of `[1, k]`.
  -- It follows that `e` is one less than such a product.
  have h : M₁ ⊆ image f K,
  { intros m hm,
    simp only [M₁, M, sep_def, mem_filter, mem_range, mem_powerset, mem_image, exists_prop] at hm ⊢,
    obtain ⟨⟨-, hmp⟩, hms⟩ := hm,
    use (m + 1).factors,
    { rwa [multiset.coe_nodup, ← nat.squarefree_iff_nodup_factors m.succ_ne_zero] },
    refine ⟨λ p, _, _⟩,
    { suffices : p ∈ (m + 1).factors → ∃ a : ℕ, a < k ∧ a.succ = p, { simpa },
      simp_intros hp only [nat.mem_factors m.succ_ne_zero],
      exact ⟨p.pred, (nat.pred_lt (nat.prime.ne_zero hp.1)).trans_le ((hmp p) hp),
            nat.succ_pred_eq_of_pos (nat.prime.pos hp.1)⟩ },
    { simp_rw f, simp [nat.prod_factors m.succ_ne_zero, m.succ_sub_one] } },

  -- The number of elements of `M x k` with `e + 1` squarefree is bounded by the number of subsets
  -- of `[1, k]`.
  calc card M₁ ≤ card (image f K)                    : card_le_of_subset h
  ...          ≤ card K                              : card_image_le
  ...          ≤ 2 ^ card (image nat.succ (range k)) : by simp only [K, card_powerset]
  ...          ≤ 2 ^ card (range k)                  : pow_le_pow one_le_two card_image_le
  ...          = 2 ^ k                               : by rw card_range k,
end

/--
The number of `e < x` for which `e + 1` is a product of powers of primes smaller than or equal to
`k` is bounded by `2 ^ k * nat.sqrt x`.
-/
lemma card_le_two_pow_mul_sqrt {x k : ℕ} : card (M x k) ≤ 2 ^ k * nat.sqrt x :=
begin
  let M₁ := {e ∈ M x k | squarefree (e + 1)},
  let M₂ := M (nat.sqrt x) k,
  let K := M₁ ×ˢ M₂,
  let f : ℕ × ℕ → ℕ := λ mn, (mn.2 + 1) ^ 2 * (mn.1 + 1) - 1,

  -- Every element of `M x k` is one less than the product `(m + 1)² * (r + 1)` with `r + 1`
  -- squarefree and `m + 1 ≤ √x`, and both `m + 1` and `r + 1` still only have prime powers
  -- smaller than or equal to `k`.
  have h1 : M x k ⊆ image f K,
  { intros m hm,
    simp only [M, M₁, M₂, mem_image, exists_prop, prod.exists, mem_product, sep_def, mem_filter,
               mem_range] at hm ⊢,
    have hm' := m.zero_lt_succ,
    obtain ⟨a, b, hab₁, hab₂⟩ := nat.sq_mul_squarefree_of_pos' hm',
    obtain ⟨ham, hbm⟩ := ⟨dvd.intro_left _ hab₁, dvd.intro _ hab₁⟩,
    refine ⟨a, b, ⟨⟨⟨_, λ p hp, _⟩, hab₂⟩, ⟨_, λ p hp, _⟩⟩, by simp_rw [f, hab₁, m.succ_sub_one]⟩,
    { exact (nat.succ_le_succ_iff.mp (nat.le_of_dvd hm' ham)).trans_lt hm.1 },
    { exact hm.2 p ⟨hp.1, hp.2.trans ham⟩ },
    { calc b < b + 1        : lt_add_one b
      ...    ≤ (m + 1).sqrt : by simpa only [nat.le_sqrt, pow_two] using nat.le_of_dvd hm' hbm
      ...    ≤ x.sqrt       : nat.sqrt_le_sqrt (nat.succ_le_iff.mpr hm.1) },
    { exact hm.2 p ⟨hp.1, hp.2.trans (nat.dvd_of_pow_dvd one_le_two hbm)⟩ } },

  have h2 : card M₂ ≤ nat.sqrt x,
  { rw ← card_range (nat.sqrt x), apply card_le_of_subset, simp [M₂, M] },

  calc card (M x k) ≤ card (image f K)   : card_le_of_subset h1
  ...               ≤ card K             : card_image_le
  ...               = card M₁ * card M₂  : card_product M₁ M₂
  ...               ≤ 2 ^ k * x.sqrt     : mul_le_mul' card_le_two_pow h2,
end

theorem real.tendsto_sum_one_div_prime_at_top :
  tendsto (λ n, ∑ p in {p ∈ range n | nat.prime p}, (1 / (p : ℝ))) at_top at_top :=
begin
  -- Assume that the sum of the reciprocals of the primes converges.
  by_contradiction h,

  -- Then there is a natural number `k` such that for all `x`, the sum of the reciprocals of primes
  -- between `k` and `x` is less than 1/2.
  obtain ⟨k, h1⟩ := sum_lt_half_of_not_tendsto h,

  -- Choose `x` sufficiently large for the argument below to work, and use a perfect square so we
  -- can easily take the square root.
  let x := 2 ^ (k + 1) * 2 ^ (k + 1),

  -- We will partition `range x` into two subsets:
  -- * `M`, the subset of those `e` for which `e + 1` is a product of powers of primes smaller
  --   than or equal to `k`;
  set M := M x k with hM,

  -- * `U`, the subset of those `e` for which there is a prime `p > k` that divides `e + 1`.
  let P := {p ∈ range (x + 1) | k < p ∧ nat.prime p},
  set U := U x k with hU,

  -- This is indeed a partition, so `|U| + |M| = |range x| = x`.
  have h2 : x = card U + card M,
  { rw [← card_range x, hU, hM, ← range_sdiff_eq_bUnion],
    exact (card_sdiff_add_card_eq_card (finset.filter_subset _ _)).symm },

  -- But for the `x` we have chosen above, both `|U|` and `|M|` are less than or equal to `x / 2`,
  -- and for U, the inequality is strict.
  have h3 :=
    calc (card U : ℝ) ≤ x * ∑ p in P, 1 / p : card_le_mul_sum
    ...               < x * (1 / 2)         : mul_lt_mul_of_pos_left (h1 x) (by norm_num)
    ...               = x / 2               : mul_one_div x 2,

  have h4 :=
    calc (card M : ℝ) ≤ 2 ^ k * x.sqrt      : by exact_mod_cast card_le_two_pow_mul_sqrt
    ...               = 2 ^ k * ↑(2 ^ (k + 1)) : by rw nat.sqrt_eq
    ...               = x / 2               : by field_simp [x, mul_right_comm, ← pow_succ'],

  refine lt_irrefl (x : ℝ) _,
  calc (x : ℝ) = (card U : ℝ) + (card M : ℝ) : by assumption_mod_cast
  ...          < x / 2 + x / 2               : add_lt_add_of_lt_of_le h3 h4
  ...          = x                           : add_halves ↑x,
end
