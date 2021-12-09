/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/

import data.nat.prime
import data.finset.basic
import data.finsupp.basic
import algebra.big_operators.basic
import algebra.associated
import ring_theory.int.basic

/-!
# Products and sums involving prime numbers

This file contains theorems about products and sums of `finset`s and `finsupp`s involving
prime numbers.

-/

open finset finsupp

section comm_monoid_with_zero

variables {α M : Type*} [decidable_eq α] [comm_monoid_with_zero M]

lemma prime.dvd_finset_prod_iff {S : finset α} {p : M}  (pp : prime p) (g : α → M) :
  p ∣ S.prod g ↔ ∃ a ∈ S, p ∣ g a :=
begin
  split,
  { apply @finset.induction_on α (λ S, p ∣ S.prod g → (∃ (a : α) (H : a ∈ S), p ∣ g a)),
    { simp only [nat.dvd_one, finset.prod_empty],
      exact λ h, absurd h (prime.not_dvd_one pp) },
    { intros a S haS h1 h2,
      rw prod_insert haS at h2,
      cases (prime.dvd_or_dvd pp) h2,
      { use a, simp [h] },
      { rcases h1 h with ⟨a, ha1, ha2⟩, use a, simp [ha1, ha2] } } },
  { exact λ ⟨a, ha1, ha2⟩, dvd_trans ha2 (dvd_prod_of_mem g ha1) },
end

lemma prime.dvd_finsupp_prod_iff  {f: α →₀ M} {g : α → M → ℕ} {p : ℕ} (pp : prime p) :
  p ∣ f.prod g ↔ ∃ a ∈ f.support, p ∣ g a (f a) :=
prime.dvd_finset_prod_iff pp _

end comm_monoid_with_zero

open nat

lemma nat.prime.dvd_finset_prod_iff {α : Type*} [decidable_eq α] {S : finset α} {p : ℕ}
  (pp : nat.prime p) (g : α → ℕ) : p ∣ S.prod g ↔ ∃ a ∈ S, p ∣ g a :=
prime.dvd_finset_prod_iff (prime_iff.mp pp) _

lemma nat.prime.dvd_finsupp_prod_iff {α M : Type*} [decidable_eq α] [has_zero M] {f: α →₀ M}
  {g : α → M → ℕ} {p : ℕ} (pp : nat.prime p) :
p ∣ f.prod g ↔ ∃ a ∈ f.support, p ∣ g a (f a) :=
nat.prime.dvd_finset_prod_iff pp _
