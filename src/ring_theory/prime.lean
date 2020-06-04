/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import algebra.associated
import algebra.big_operators
/-!
# Prime elements in rings
This file contains lemmas about prime elements of commutative rings.
-/

variables {R : Type*} [integral_domain R]
open finset

open_locale big_operators

lemma mul_eq_mul_prime_prod {α : Type*} [decidable_eq α] {x y a : R} {s : finset α}
  {p : α → R} (hp : ∀ i ∈ s, prime (p i)) (hx : x * y = a * ∏ i in s, p i) :
  ∃ t u b c, t ∪ u = s ∧ disjoint t u ∧ b * c = a ∧
    b * ∏ i in t, p i = x ∧ c * ∏ i in u, p i = y :=
begin
  induction s using finset.induction with i s his ih generalizing x y a,
  { exact ⟨∅, ∅, x, y, by simp [hx]⟩ },
  { rw [prod_insert his, ← mul_assoc] at hx,
    have hpi : prime (p i), { exact hp i (mem_insert_self _ _) },
    rcases ih (λ i hi, hp i (mem_insert_of_mem hi)) hx with
      ⟨t, u, b, c, htus, htu, hbc, rfl, rfl⟩,
    have hpibc : p i ∣ b ∨ p i ∣ c,
      from hpi.div_or_div ⟨a, by rw [hbc, mul_comm]⟩,
    have hit : i ∉ t, from λ hit, his (htus ▸ mem_union_left _ hit),
    have hiu : i ∉ u, from λ hiu, his (htus ▸ mem_union_right _ hiu),
    rcases hpibc with ⟨d, rfl⟩ | ⟨d, rfl⟩,
    { rw [mul_assoc, mul_comm a, domain.mul_right_inj hpi.ne_zero] at hbc,
      exact ⟨insert i t, u, d, c, by rw [insert_union, htus],
        disjoint_insert_left.2 ⟨hiu, htu⟩,
          by simp [← hbc, prod_insert hit, mul_assoc, mul_comm, mul_left_comm]⟩ },
    { rw [← mul_assoc, mul_right_comm b, domain.mul_left_inj hpi.ne_zero] at hbc,
      exact ⟨t, insert i u, b, d, by rw [union_insert, htus],
        disjoint_insert_right.2 ⟨hit, htu⟩,
          by simp [← hbc, prod_insert hiu, mul_assoc, mul_comm, mul_left_comm]⟩ } }
end

lemma mul_eq_mul_prime_pow {x y a p : R} {n : ℕ} (hp : prime p) (hx : x * y = a * p ^ n) :
  ∃ i j b c, i + j = n ∧ b * c = a ∧ b * p ^ i = x ∧ c * p ^ j = y :=
begin
  rcases mul_eq_mul_prime_prod (λ _ _, hp)
    (show x * y = a * (range n).prod (λ _, p), by simpa) with
    ⟨t, u, b, c, htus, htu, rfl, rfl, rfl⟩,
  exact ⟨t.card, u.card, b, c, by rw [← card_disjoint_union htu, htus, card_range], by simp⟩,
end
