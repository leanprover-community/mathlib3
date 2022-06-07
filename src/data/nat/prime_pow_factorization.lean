/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import algebra.is_prime_pow
import data.nat.factorization

/-!
# Prime powers and factorizations

This file deals with factorizations of prime powers.
-/

variables {R : Type*} [comm_monoid_with_zero R] (n p : R) (k : ℕ)

lemma is_prime_pow.min_fac_pow_factorization_eq {n : ℕ} (hn : is_prime_pow n) :
  n.min_fac ^ n.factorization n.min_fac = n :=
begin
  obtain ⟨p, k, hp, hk, rfl⟩ := hn,
  rw ←nat.prime_iff at hp,
  rw [hp.pow_min_fac hk.ne', hp.factorization_pow, finsupp.single_eq_same],
end

lemma is_prime_pow_of_min_fac_pow_factorization_eq {n : ℕ}
  (h : n.min_fac ^ n.factorization n.min_fac = n) (hn : n ≠ 1) :
  is_prime_pow n :=
begin
  rcases eq_or_ne n 0 with rfl | hn',
  { simpa using h },
  refine ⟨_, _, nat.prime_iff.1 (nat.min_fac_prime hn), _, h⟩,
  rw [pos_iff_ne_zero, ←finsupp.mem_support_iff, nat.factor_iff_mem_factorization,
    nat.mem_factors_iff_dvd hn' (nat.min_fac_prime hn)],
  apply nat.min_fac_dvd
end

lemma is_prime_pow_iff_min_fac_pow_factorization_eq {n : ℕ} (hn : n ≠ 1) :
  is_prime_pow n ↔ n.min_fac ^ n.factorization n.min_fac = n :=
⟨λ h, h.min_fac_pow_factorization_eq, λ h, is_prime_pow_of_min_fac_pow_factorization_eq h hn⟩

lemma is_prime_pow_iff_factorization_eq_single {n : ℕ} :
  is_prime_pow n ↔ ∃ p k : ℕ, 0 < k ∧ n.factorization = finsupp.single p k :=
begin
  rw is_prime_pow_nat_iff,
  refine exists₂_congr (λ p k, _),
  split,
  { rintros ⟨hp, hk, hn⟩,
    exact ⟨hk, by rw [←hn, nat.prime.factorization_pow hp]⟩ },
  { rintros ⟨hk, hn⟩,
    have hn0 : n ≠ 0,
    { rintro rfl,
      simpa only [finsupp.single_eq_zero, eq_comm, nat.factorization_zero, hk.ne'] using hn },
    rw nat.eq_pow_of_factorization_eq_single hn0 hn,
    exact ⟨nat.prime_of_mem_factorization
      (by simp [hn, hk.ne'] : p ∈ n.factorization.support), hk, rfl⟩ }
end

lemma is_prime_pow_iff_card_support_factorization_eq_one {n : ℕ} :
  is_prime_pow n ↔ n.factorization.support.card = 1 :=
by simp_rw [is_prime_pow_iff_factorization_eq_single, finsupp.card_support_eq_one', exists_prop,
  pos_iff_ne_zero]
