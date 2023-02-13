/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import algebra.is_prime_pow
import data.nat.factorization.basic

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
  refine ⟨_, _, (nat.min_fac_prime hn).prime, _, h⟩,
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

lemma is_prime_pow.exists_ord_compl_eq_one {n : ℕ} (h : is_prime_pow n) :
  ∃ p : ℕ, p.prime ∧ ord_compl[p] n = 1 :=
begin
  rcases eq_or_ne n 0 with rfl | hn0, { cases not_is_prime_pow_zero h },
  rcases is_prime_pow_iff_factorization_eq_single.mp h with ⟨p, k, hk0, h1⟩,
  rcases em' p.prime with pp | pp,
  { refine absurd _ hk0.ne', simp [←nat.factorization_eq_zero_of_non_prime n pp, h1] },
  refine ⟨p, pp, _⟩,
  refine nat.eq_of_factorization_eq (nat.ord_compl_pos p hn0).ne' (by simp) (λ q, _),
  rw [nat.factorization_ord_compl n p, h1],
  simp,
end

lemma exists_ord_compl_eq_one_iff_is_prime_pow {n : ℕ} (hn : n ≠ 1) :
  is_prime_pow n ↔ ∃ p : ℕ, p.prime ∧ ord_compl[p] n = 1 :=
begin
  refine ⟨λ h, is_prime_pow.exists_ord_compl_eq_one h, λ h, _⟩,
  rcases h with ⟨p, pp, h⟩,
  rw is_prime_pow_nat_iff,
  rw [←nat.eq_of_dvd_of_div_eq_one (nat.ord_proj_dvd n p) h] at ⊢ hn,
  refine ⟨p, n.factorization p, pp, _, by simp⟩,
  contrapose! hn,
  simp [le_zero_iff.1 hn],
end

/-- An equivalent definition for prime powers: `n` is a prime power iff there is a unique prime
dividing it. -/
lemma is_prime_pow_iff_unique_prime_dvd {n : ℕ} :
  is_prime_pow n ↔ ∃! p : ℕ, p.prime ∧ p ∣ n :=
begin
  rw is_prime_pow_nat_iff,
  split,
  { rintro ⟨p, k, hp, hk, rfl⟩,
    refine ⟨p, ⟨hp, dvd_pow_self _ hk.ne'⟩, _⟩,
    rintro q ⟨hq, hq'⟩,
    exact (nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hq') },
  rintro ⟨p, ⟨hp, hn⟩, hq⟩,
  rcases eq_or_ne n 0 with rfl | hn₀,
  { cases (hq 2 ⟨nat.prime_two, dvd_zero 2⟩).trans (hq 3 ⟨nat.prime_three, dvd_zero 3⟩).symm },
  refine ⟨p, n.factorization p, hp, hp.factorization_pos_of_dvd hn₀ hn, _⟩,
  simp only [and_imp] at hq,
  apply nat.dvd_antisymm (nat.ord_proj_dvd _ _),
  -- We need to show n ∣ p ^ n.factorization p
  apply nat.dvd_of_factors_subperm hn₀,
  rw [hp.factors_pow, list.subperm_ext_iff],
  intros q hq',
  rw nat.mem_factors hn₀ at hq',
  cases hq _ hq'.1 hq'.2,
  simp,
end

lemma is_prime_pow_pow_iff {n k : ℕ} (hk : k ≠ 0) :
  is_prime_pow (n ^ k) ↔ is_prime_pow n :=
begin
  simp only [is_prime_pow_iff_unique_prime_dvd],
  apply exists_unique_congr,
  simp only [and.congr_right_iff],
  intros p hp,
  exact ⟨hp.dvd_of_dvd_pow, λ t, t.trans (dvd_pow_self _ hk)⟩,
end

lemma nat.coprime.is_prime_pow_dvd_mul {n a b : ℕ} (hab : nat.coprime a b) (hn : is_prime_pow n) :
  n ∣ a * b ↔ n ∣ a ∨ n ∣ b :=
begin
  rcases eq_or_ne a 0 with rfl | ha,
  { simp only [nat.coprime_zero_left] at hab,
    simp [hab, finset.filter_singleton, not_is_prime_pow_one] },
  rcases eq_or_ne b 0 with rfl | hb,
  { simp only [nat.coprime_zero_right] at hab,
    simp [hab, finset.filter_singleton, not_is_prime_pow_one] },
  refine ⟨_, λ h, or.elim h (λ i, i.trans (dvd_mul_right _ _)) (λ i, i.trans (dvd_mul_left _ _))⟩,
  obtain ⟨p, k, hp, hk, rfl⟩ := (is_prime_pow_nat_iff _).1 hn,
  simp only [hp.pow_dvd_iff_le_factorization (mul_ne_zero ha hb),
    nat.factorization_mul ha hb, hp.pow_dvd_iff_le_factorization ha,
    hp.pow_dvd_iff_le_factorization hb, pi.add_apply, finsupp.coe_add],
  have : a.factorization p = 0 ∨ b.factorization p = 0,
  { rw [←finsupp.not_mem_support_iff, ←finsupp.not_mem_support_iff, ←not_and_distrib,
      ←finset.mem_inter],
    exact λ t, (nat.factorization_disjoint_of_coprime hab).le_bot t },
  cases this;
  simp [this, imp_or_distrib],
end

lemma nat.mul_divisors_filter_prime_pow {a b : ℕ} (hab : a.coprime b) :
  (a * b).divisors.filter is_prime_pow = (a.divisors ∪ b.divisors).filter is_prime_pow :=
begin
  rcases eq_or_ne a 0 with rfl | ha,
  { simp only [nat.coprime_zero_left] at hab,
    simp [hab, finset.filter_singleton, not_is_prime_pow_one] },
  rcases eq_or_ne b 0 with rfl | hb,
  { simp only [nat.coprime_zero_right] at hab,
    simp [hab, finset.filter_singleton, not_is_prime_pow_one] },
  ext n,
  simp only [ha, hb, finset.mem_union, finset.mem_filter, nat.mul_eq_zero, and_true, ne.def,
    and.congr_left_iff, not_false_iff, nat.mem_divisors, or_self],
  apply hab.is_prime_pow_dvd_mul,
end
