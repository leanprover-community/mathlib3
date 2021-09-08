/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import data.nat.prime
import tactic.interval_cases
import tactic.cancel_denoms
import tactic.linarith


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

lemma prime_mod_six (p : ℕ) (h : p.prime) : p = 2 ∨ p = 3 ∨ p % 6 = 1 ∨ p % 6 = 5 :=
begin
  have : p % 6 < 6,
    apply mod_lt, dec_trivial,
  interval_cases p % 6,
  { sorry, },
  { finish, },
  { sorry, },
  { sorry, },
  { sorry, },
  { finish, },
end

lemma filter_mod_eq_range_card (a b n : ℕ) :
  (filter (λ (i : ℕ), i % a = b) (range n)).card = (n - b) / a :=
begin
  sorry,
end

/-- A simple linear bound on the size of the prime counting function -/
lemma linear_prime_counting_bound (n : ℕ) : π n ≤ n / 3 + 2 :=
calc π n ≤ ((range (n + 1)).filter (λ i, i = 2 ∨ i = 3 ∨ i % 6 = 1 ∨ i % 6 = 5)).card :
            begin
              rw prime_counting,
              apply card_le_of_subset,
              simp only [subset_iff, and_imp, mem_filter, mem_range],
              intros x hxn hxp,
              exact ⟨hxn, prime_mod_six x hxp⟩,
            end
     ... ≤ 1 + (1 + (n / 6 + n / 6)) :
            begin
              repeat {rw filter_or},
              repeat { transitivity, apply card_union_le, apply add_le_add,},
              { rw filter_eq', simp only [if_congr, finset.mem_range],
                by_cases 2 < n + 1,
                  { rw if_pos, simp, exact h, },
                  { rw if_neg, simp, exact h, }, },
              { rw filter_eq', simp only [if_congr, finset.mem_range],
                by_cases 3 < n + 1,
                  { rw if_pos, simp, exact h, },
                  { rw if_neg, simp, exact h, }, },
              { rw filter_mod_eq_range_card,
                simp, },
              { rw filter_mod_eq_range_card,
                apply nat.div_le_div_right,
                simp, },
            end
     ... ≤ n / 3 + 2 :
            begin
              have : 0 < 6, dec_trivial,
              rw <-mul_le_mul_left this,
              simp only [mul_add],
              sorry,
            end


end nat
