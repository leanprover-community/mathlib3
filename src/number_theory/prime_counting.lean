/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import data.nat.prime
import tactic.interval_cases
import tactic.cancel_denoms
import tactic.linarith
import data.nat.totient


/-!
# The Prime Counting Function

In this file we define the prime counting function - the function on natural numbers that returns
the number of primes less than or equal to its input.
-/

namespace nat
open finset

/--
A variant of the traditional prime counting function which gives the number of primes
*strictly* less than the input. More convenient for avoiding off-by-one errors.
-/
def prime_counting' (n : ℕ) : ℕ := ((range n).filter (prime)).card

/-- The prime counting function: Returns the number of primes less than or equal to the input. -/
def prime_counting (n : ℕ) : ℕ := ((range (n + 1)).filter (prime)).card

localized "notation `π` := nat.prime_counting" in nat
localized "notation `π'` := nat.prime_counting'" in nat


-- lemma filter_mod_eq_range_card (a b n : ℕ) :
--   (filter (λ (i : ℕ), i % a = b) (range n)).card = (n - b) / a :=
-- begin
--   sorry,
-- end

lemma monotone_prime_counting : monotone prime_counting :=
begin
  intros a b a_le_b,
  unfold prime_counting,
  apply card_le_of_subset,
  apply monotone_filter_left,
  simp only [le_eq_subset, range_subset, add_le_add_iff_right],
  exact a_le_b,
end

lemma monotone_prime_counting' : monotone prime_counting' :=
begin
  intros a b a_le_b,
  unfold prime_counting',
  apply card_le_of_subset,
  apply monotone_filter_left,
  simp only [le_eq_subset, range_subset],
  exact a_le_b,
end

lemma split_range {n k : ℕ} (k_le_n : k ≤ n) (p : ℕ -> Prop) [decidable_pred p]
  : (range n).filter p = (range k).filter p ∪ (Ico k n).filter p :=
begin
  rw <- filter_union,
  ext,
  simp only [mem_union, mem_filter, mem_range, and.congr_left_iff, mem_Ico],
  intro _,
  split,
  { intros a_le_n,
    cases lt_or_le a k,
    { left, exact h, },
    { right, exact ⟨h, a_le_n⟩, }, },
  { intros hyp,
    cases hyp,
    { exact gt_of_ge_of_gt k_le_n hyp, },
    { exact hyp.2, }, },
end

lemma eq_or_coprime_of_lt_prime {n k : ℕ} (h0 : 0 < n) (hlt : n ≤ k) (is_prime : prime k) : k = n ∨ coprime k n :=
begin
  sorry,
end

lemma Ico_zero : Ico 0 = range :=
begin
  funext,
  rw ext_iff,
  intro a,
  rw [mem_Ico, mem_range],
  simp,
end

lemma filter_mod_eq_range_card (a b n : ℕ) :
  (filter (λ (i : ℕ), a.coprime i) (Ico n (n+a))).card = totient a :=
begin
  induction n,
  -- TODO Ico 0 should simp to range
  { simp [Ico_zero],
    rw totient, },
  {
    rw <-n_ih,
    clear n_ih,
    sorry,
  }
end

-- TODO remove h0 h1 k_le_n assumption
/-- A simple linear bound on the size of the `prime_counting'` function -/
lemma linear_prime_counting_bound (n k : ℕ) (h0 : 0 < k) (k_lt_n : k < n) (k_le_n : k ≤ n) : π' n ≤ π' k + 1 + nat.totient k * (n - k) / k :=
calc π' n ≤ ((range k).filter (prime)).card + ((Ico k n).filter (prime)).card :
            begin
              rw [prime_counting', split_range k_le_n],
              apply card_union_le,
            end
     ... ≤ π' k + ((Ico k n).filter (prime)).card : by rw prime_counting'
     ... ≤ π' k + ((Ico k n).filter (λ i, i = k ∨ coprime i k)).card :
            begin
              apply add_le_add_left,
              apply card_le_of_subset,
              rw subset_iff,
              simp,
              intros p succ_k_le_p p_lt_n p_prime,
              -- have k_lt_p : k < p, linarith,
              split,
              { exact ⟨succ_k_le_p, p_lt_n⟩, },
              { apply eq_or_coprime_of_lt_prime h0 _ p_prime,
                exact succ_k_le_p,
              },
            end
     ... ≤ π' k + nat.totient k * (n - k) / k :
            begin
              apply add_le_add_left,
              rw [filter_or, filter_eq'],
              simp,
              rw if_pos k_lt_n,
              sorry,
            end

end nat
