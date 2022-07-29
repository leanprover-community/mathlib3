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
import data.nat.nth
import tactic.interval_cases

/-!
# The Prime Counting Function

In this file we define the prime counting function: the function on natural numbers that returns
the number of primes less than or equal to its input.

## Main Results

The main definitions for this file are

- `nat.prime_counting`: The prime counting function π
- `nat.prime_counting'`: π(n - 1)

We then prove that these are monotone in `nat.monotone_prime_counting` and
`nat.monotone_prime_counting'`. The last main theorem `nat.prime_counting'_add_le` is an upper
bound on `π'` which arises by observing that all numbers greater than `k` and not coprime to `k`
are not prime, and so only at most `φ(k)/k` fraction of the numbers from `k` to `n` are prime.

## Notation

We use the standard notation `π` to represent the prime counting function (and `π'` to represent
the reindexed version).

-/

namespace nat
open finset

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

@[simp] lemma prime_counting'_nth_eq (n : ℕ) : π' (nth prime n) = n :=
count_nth_of_infinite _ infinite_set_of_prime _

@[simp] lemma prime_nth_prime (n : ℕ) : prime (nth prime n) :=
nth_mem_of_infinite _ infinite_set_of_prime _

lemma foo (a b c d : ℕ) (h : d ∣ c) : (a + b * c) / d = a / d + b * (c / d) := sorry

lemma totient_six : nat.totient 6 = 2 := sorry

/-- A linear upper bound on the size of the `prime_counting'` function -/
lemma prime_counting'_add_mul_le {a k : ℕ} (h0 : 0 < a) (h1 : a < k) (m : ℕ) :
  π' (k + m * a) ≤ π' k + nat.totient a * (m) :=
calc π' (k + m * a)
    ≤ ((range k).filter (prime)).card + ((Ico k (k + m * a)).filter (prime)).card :
        begin
          rw [prime_counting', count_eq_card_filter_range, range_eq_Ico,
              ←Ico_union_Ico_eq_Ico (zero_le k) (le_self_add), filter_union],
          apply card_union_le,
        end
... ≤ π' k + ((Ico k (k + m * a)).filter (prime)).card :
        by rw [prime_counting', count_eq_card_filter_range]
... ≤ π' k + ((Ico k (k + m * a)).filter (coprime a)).card :
        begin
          refine add_le_add_left (card_le_of_subset _) k.prime_counting',
          simp only [subset_iff, and_imp, mem_filter, mem_Ico],
          intros p succ_k_le_p p_lt_n p_prime,
          split,
          { exact ⟨succ_k_le_p, p_lt_n⟩, },
          { rw coprime_comm,
            exact coprime_of_lt_prime h0 (gt_of_ge_of_gt succ_k_le_p h1) p_prime, },
        end
... ≤ π' k + totient a * (m) :
        begin
          rw [add_le_add_iff_left],
          apply Ico_add_mul_filter_coprime_le,
          exact h0,
        end

set_option profiler true

/-- An explicit instantiation of nat.prime_counting'_add_mul_le  -/
lemma prime_counting'_le_div_3_add_2 (n : ℕ) :
  π' (n) ≤ n / 3 + 2 :=
begin
  rw ←div_add_mod n 6,
  generalize : n / 6 = d,
  have r_lt : n % 6 < 6,
    apply nat.mod_lt,
    norm_num,
  revert r_lt,
  -- nth_rewrite 0 ←div_add_mod n' 2,
  generalize : n % 6 = r,
  intro r_lt,
  cases d,
   {
    interval_cases r,
    all_goals { norm_num },
    all_goals { unfold prime_counting' count, },
    all_goals { simp [list.range_succ], },
    all_goals { simp [list.countp], },
    all_goals { norm_num, },
  },
  cases d,
   {
    interval_cases r,
    all_goals { norm_num },
    all_goals { unfold prime_counting' count, },
    all_goals { simp [list.range_succ], },
    all_goals { simp [list.countp], },
    all_goals { norm_num, },
  },
  {
    simp_rw [nat.mul_succ, nat.add_assoc, add_comm (6 * d) _, mul_comm],
    apply le_trans (prime_counting'_add_mul_le _ _ _),
    {
      rw [foo, totient_six],
      norm_num,
      rw mul_comm 2 d,
      simp_rw add_comm _ (d * 2),
      rw add_assoc,
      simp only [add_le_add_iff_left],
      interval_cases r,
      all_goals { norm_num },
      all_goals { unfold prime_counting' count, },
      all_goals { simp [list.range_succ], },
      all_goals { simp [list.countp], },
      all_goals { norm_num, },
    },
    {
      norm_num,
    },
    linarith,
  },
end

end nat
