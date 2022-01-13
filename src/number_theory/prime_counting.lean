/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import data.nat.prime
import data.nat.totient
import algebra.periodic
import data.finset.locally_finite
import data.nat.count


/-!
# The Prime Counting Function

In this file we define the prime counting function - the function on natural numbers that returns
the number of primes less than or equal to its input.

## Main Results

The main definitions for this file are

- `prime_counting`: The prime counting function π
- `prime_counting'`: π(n - 1)

We then prove that these are monotone. The last main theorem is an upper bound on `π'` which arises
by observing that all numbers greater than `k` and not coprime to `k` are not prime, and so only at
most `φ(k)/k` fraction of the numbers from `k` to `n` are prime.

## Notation

We use the standard notation `π` to represent the prime counting function (and `π'` to represent
the reindexed version).

-/

namespace nat
open finset

-- TODO: Unify the following definitions with those provided in PR #9457

/--
A variant of the traditional prime counting function which gives the number of primes
*strictly* less than the input. More convenient for avoiding off-by-one errors.
-/
def prime_counting' : ℕ → ℕ := nat.count prime

/-- The prime counting function: Returns the number of primes less than or equal to the input. -/
def prime_counting (n : ℕ) : ℕ := prime_counting' (n + 1)

localized "notation `π` := nat.prime_counting" in nat
localized "notation `π'` := nat.prime_counting'" in nat

lemma monotone_prime_counting' : monotone prime_counting' := count_monotone prime

lemma monotone_prime_counting : monotone prime_counting :=
λ a b a_le_b, monotone_prime_counting' (add_le_add_right a_le_b 1)

private lemma filter_coprime_bound (a n : ℕ) (a_pos : 0 < a) :
  (filter (a.coprime) (Ico a n)).card ≤ totient a * (n / a) :=
begin
  conv
  begin
    to_lhs,
    rw ←nat.mod_add_div n a,
  end,
  induction n / a,
  { simp [le_of_lt (mod_lt n a_pos)], },
  { simp only [mul_succ],
    rw ←add_assoc,
    suffices : (filter a.coprime (Ico a (n % a + a * n_1 + a))).card
        ≤ (filter a.coprime (Ico a (n % a + a * n_1))).card + a.totient,
    { exact le_add_of_le_add_right this ih, },
    calc (filter a.coprime (Ico a (n % a + a * n_1 + a))).card
        ≤ (filter a.coprime (Ico a (n % a + a * n_1)
                              ∪ Ico (n % a + a * n_1) (n % a + a * n_1 + a))).card :
          begin
            apply card_le_of_subset,
            apply filter_subset_filter,
            rw [subset_iff],
            intro x,
            simp only [mem_Ico, and_imp, mem_union],
            intros h1 h2,
            by_cases x < n % a + a * n_1,
            { left,
              exact ⟨h1, h⟩, },
            { right,
              exact ⟨le_of_not_lt h, h2⟩, },
          end
    ... ≤ (filter a.coprime (Ico a (n % a + a * n_1))).card + a.totient :
          begin
            rw [filter_union, ←filter_coprime_Ico_eq_totient a (n % a + a * n_1)],
            apply card_union_le,
          end },
end

/-- A linear upper bound on the size of the `prime_counting'` function -/
lemma linear_prime_counting_bound (n k : ℕ) (h0 : 0 < k) :
  π' n ≤ π' k + 1 + nat.totient k * (n / k) :=
begin
  cases lt_or_le k n with k_lt_n n_le_k,
  { calc π' n ≤ ((range k).filter (prime)).card + ((Ico k n).filter (prime)).card :
                begin
                  rw [prime_counting', count_eq_card_filter_range, range_eq_Ico,
                      ←Ico_union_Ico_eq_Ico (zero_le k) (le_of_lt k_lt_n), filter_union],
                  apply card_union_le,
                end
        ... ≤ π' k + ((Ico k n).filter (prime)).card :
                by rw [prime_counting', count_eq_card_filter_range]
        ... ≤ π' k + ((Ico k n).filter (λ i, i = k ∨ coprime k i)).card :
                begin
                  refine add_le_add_left (card_le_of_subset _) k.prime_counting',
                  simp only [subset_iff, and_imp, mem_filter, mem_Ico],
                  intros p succ_k_le_p p_lt_n p_prime,
                  split,
                  { exact ⟨succ_k_le_p, p_lt_n⟩, },
                  { rw coprime_comm,
                    exact eq_or_coprime_of_le_prime h0 succ_k_le_p p_prime, },
                end
        ... = π' k + ({k} ∪ filter k.coprime (Ico k n)).card :
                begin
                  rw [filter_or, filter_eq'],
                  congr,
                  simp only [true_and, le_refl, not_lt, mem_Ico, ite_eq_left_iff],
                  intro n_le_k,
                  exfalso,
                  exact lt_le_antisymm k_lt_n n_le_k,
                end
        ... ≤ π' k + (1 + nat.totient k * (n / k)) :
                begin
                  apply add_le_add_left,
                  apply trans (card_union_le {k} (filter k.coprime (Ico k n))),
                  simp only [add_le_add_iff_left, card_singleton],
                  exact filter_coprime_bound k n h0,
                end
        ... = π' k + 1 + nat.totient k * (n / k) : by rw [add_assoc] },
  { exact le_add_right (le_add_right (monotone_prime_counting' n_le_k))},
end

/-- An explicit linear upper bound on the size of the `prime_counting'` function -/
lemma linear_prime_counting_bound_6 (n : ℕ) :
  π' n ≤ 4 + 2 * (n / 6) :=
begin
  have h := linear_prime_counting_bound n 6 (by linarith),
  suffices : 4 + 2 * (n / 6) = prime_counting' 6 + 1 + totient 6 * (n / 6),
  { rwa this, },
  congr,
  { simp [prime_counting', count_succ],
    norm_num, },
  { have : 6 = 2 * 3 := by norm_num,
    rw [this, totient_mul, totient_prime, totient_prime]; norm_num, },
end

end nat
