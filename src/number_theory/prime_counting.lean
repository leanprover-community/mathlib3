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


lemma filter_mod_eq_range_card (a b n : ℕ) :
  (filter (λ (i : ℕ), i % a = b) (range n)).card = (n - b) / a :=
begin
  sorry,
end

-- TODO prove π is nondecreasing

/-- A simple linear bound on the size of the `prime_counting'` function -/
lemma linear_prime_counting_bound (n k : ℕ) : π' n ≤ π' k + nat.totient k * (n - k) / k :=
calc π' n ≤ ((range k).filter (prime)).card + ((Ico k n).filter (prime)).card :
            begin
              rw prime_counting',
              have h : (range n).filter prime = (range k).filter prime ∪ (Ico k n).filter prime,
                { sorry, },
              rw h,
              apply card_union_le,
            end
     ... ≤ π' k + ((Ico k n).filter (prime)).card :
            begin
              rw prime_counting',
            end
     ... ≤ π' k + ((Ico k n).filter (λ i, coprime i k)).card :
            begin
              apply add_le_add_left,
              apply card_le_of_subset,
              sorry,
            end
     ... ≤ π' k + nat.totient k * (n - k) / k :
            begin
              apply add_le_add_left,
              sorry,
            end

end nat
