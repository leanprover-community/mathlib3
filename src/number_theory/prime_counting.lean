/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import data.nat.prime

/-!
# The Prime Counting Function

In this file we define the prime counting function - the function on natural numbers that returns
the number of primes less than or equal to its input.
-/

namespace nat
open finset


/--
A variant of the traditional prime counting function which gives the number of primes
*strictly* less than the input
-/
def prime_counting' (n : ℕ) : ℕ := ((range n).filter (prime)).card


/-- The prime counting function: Returns the number of primes less than or equal to the input. -/
def prime_counting (n : ℕ) : ℕ := ((range (n + 1)).filter (prime)).card

localized "notation `π` := nat.prime_counting" in nat

lemma prime_mod_six (p : ℕ) (h : p.prime) : p = 2 ∨ p = 3 ∨ p % 6 = 1 ∨ p % 6 = 5 :=
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
     ... ≤ 2 + n / 6 + n / 6 : sorry
     ... ≤ n / 3 + 2 : sorry


end nat
