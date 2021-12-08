/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/

import data.nat.prime
import data.finset.basic
import data.finsupp.basic
import algebra.big_operators.basic


/-!
# Prime numbers

This file contains theorems about products and sums of `finset`s and `finsupp`s involving
prime numbers.

-/

open nat

namespace finset

lemma dvd_prod_iff {p : ℕ} {S : finset ℕ} (pp : prime p) (g : ℕ → ℕ) :
  p ∣ S.prod g ↔ ∃ (a : ℕ) (H : a ∈ S), p ∣ g a :=
begin
  split,
  { apply @finset.induction_on ℕ (λ S, p ∣ S.prod g → (∃ (a : ℕ) (H : a ∈ S), p ∣ g a)),
    { intros hp,
      refine absurd _ not_prime_one,
      simp only [nat.dvd_one, finset.prod_empty] at hp,
      rwa hp at pp },
    { simp only [exists_prop, mem_insert],
      intros a S haS h1 h2,
      rw prod_insert haS at h2,
      cases (prime.dvd_mul pp).mp h2,
      { use a, simp [h] },
      { rcases h1 h with ⟨a, ha1, ha2⟩, use a, simp [ha1, ha2] } } },
  { rintros ⟨a, ha1, ha2⟩, exact dvd_trans ha2 (dvd_prod_of_mem g ha1) },
end

end finset

namespace finsupp

lemma dvd_prod_iff {p : ℕ} {f: ℕ →₀ ℕ} (pp : prime p) :
  (p ∣ f.prod pow) ↔ ∃ a ∈ f.support, p ∣ a^(f a) :=
begin
  unfold prod,
  exact finset.dvd_prod_iff pp (λ x, x ^ (f x)),
end

end finsupp
