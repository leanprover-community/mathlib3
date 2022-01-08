/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import data.nat.factorization

/-!
# Prime powers

This file deals with prime powers: numbers which are positive integer powers of a single prime.
-/

open_locale nat

namespace nat

variables (n : ℕ)

/-- `n` is a prime power if there is a prime `p` and a positive natural `k` such that `n` can be
written as `p^k`. -/
def is_prime_pow : Prop :=
  ∃ (p k : ℕ), p.prime ∧ 0 < k ∧ p ^ k = n

lemma is_prime_pow_def :
  n.is_prime_pow ↔ ∃ (p k : ℕ), p.prime ∧ 0 < k ∧ p ^ k = n := iff.rfl

lemma is_prime_pow_iff_bounded :
  n.is_prime_pow ↔ ∃ (p : ℕ), p ≤ n ∧ ∃ (k : ℕ), k ≤ n ∧ p.prime ∧ 0 < k ∧ p ^ k = n :=
begin
  refine iff.symm ⟨λ ⟨p, _, k, _, hp, hk, hn⟩, ⟨p, k, hp, hk, hn⟩, _⟩,
  rintro ⟨p, k, hp, hk, rfl⟩,
  refine ⟨p, _, k, (lt_pow_self hp.one_lt _).le, hp, hk, rfl⟩,
  simpa using pow_le_pow_of_le_right hp.pos hk,
end

instance {n : ℕ} : decidable n.is_prime_pow :=
decidable_of_iff' _ (is_prime_pow_iff_bounded n)

/-- An equivalent definition for prime powers: `n` is a prime power iff there is a prime `p` and a
natural `k` such that `n` can be written as `p^(k+1)`. -/
lemma is_prime_pow_iff_pow_succ :
  is_prime_pow n ↔ ∃ (p k : ℕ), p.prime ∧ p ^ (k + 1) = n :=
(is_prime_pow_def _).trans
⟨λ ⟨p, k, hp, hk, hn⟩, ⟨_, _, hp, by rwa [nat.sub_add_cancel hk]⟩,
  λ ⟨p, k, hp, hn⟩, ⟨_, _, hp, succ_pos', hn⟩⟩

lemma not_is_prime_pow_zero : ¬ is_prime_pow 0 := dec_trivial
lemma not_is_prime_pow_one : ¬ is_prime_pow 1 := dec_trivial
lemma prime.is_prime_pow {p : ℕ} (hp : p.prime) : is_prime_pow p :=
⟨p, 1, hp, zero_lt_one, by simp⟩

lemma is_prime_pow.min_fac_pow_factorization_eq {n : ℕ} (hn : n.is_prime_pow) :
  n.min_fac ^ n.factorization n.min_fac = n :=
begin
  obtain ⟨p, k, hp, hk, rfl⟩ := hn,
  rw [hp.pow_min_fac hk.ne', hp.factorization_pow, finsupp.single_eq_same],
end

lemma is_prime_pow_of_min_fac_pow_factorization_eq {n : ℕ}
  (h : n.min_fac ^ n.factorization n.min_fac = n) (hn : n ≠ 1) :
  n.is_prime_pow :=
begin
  rcases n.eq_zero_or_pos with rfl | hn',
  { simpa using h },
  refine ⟨_, _, min_fac_prime hn, _, h⟩,
  rw [pos_iff_ne_zero, ←finsupp.mem_support_iff, factor_iff_mem_factorization,
    mem_factors_iff_dvd hn' (min_fac_prime hn)],
  apply min_fac_dvd
end

lemma is_prime_pow_iff_min_fac_pow_factorization_eq (hn : n ≠ 1) :
  n.is_prime_pow ↔ n.min_fac ^ n.factorization n.min_fac = n :=
⟨λ h, h.min_fac_pow_factorization_eq, λ h, is_prime_pow_of_min_fac_pow_factorization_eq h hn⟩

/-- An equivalent definition for prime powers: `n` is a prime power iff there is a unique prime
dividing it. -/
lemma is_prime_pow_iff_unique_prime_dvd :
  n.is_prime_pow ↔ ∃! p : ℕ, p.prime ∧ p ∣ n :=
begin
  rw is_prime_pow_def,
  split,
  { rintro ⟨p, k, hp, hk, rfl⟩,
    refine ⟨p, ⟨hp, dvd_pow_self _ hk.ne'⟩, _⟩,
    rintro q ⟨hq, hq'⟩,
    exact (prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hq') },
  rintro ⟨p, ⟨hp, hn⟩, hq⟩,
  -- Take care of the n = 0 case
  rcases n.eq_zero_or_pos with rfl | hn₀,
  { obtain ⟨q, hq', hq''⟩ := exists_infinite_primes (p + 1),
    cases hq q ⟨hq'', by simp⟩,
    simpa using hq' },
  -- So assume 0 < n
  refine ⟨p, n.factors.count p, hp, _, _⟩,
  { apply list.count_pos.2,
    rwa mem_factors_iff_dvd hn₀ hp },
  simp only [and_imp] at hq,
  apply dvd_antisymm (pow_factors_count_dvd _ _),
  -- We need to show n ∣ p ^ n.factors.count p
  apply dvd_of_factors_subperm hn₀.ne',
  rw [hp.factors_pow, list.subperm_ext_iff],
  intros q hq',
  rw mem_factors hn₀ at hq',
  cases hq _ hq'.1 hq'.2,
  simp,
end

lemma unique_is_prime_pow {p₁ p₂ k₁ k₂ : ℕ}
  (hp₁ : p₁.prime) (hp₂ : p₂.prime) (hk₁ : 0 < k₁) (h : p₁ ^ k₁ = p₂ ^ k₂):
  p₁ = p₂ :=
begin
  have : p₁ ∣ p₂ ^ k₂,
  { rw ←h,
    apply dvd_pow_self _ hk₁.ne' },
  rw ←prime_dvd_prime_iff_eq hp₁ hp₂,
  exact hp₁.dvd_of_dvd_pow this,
end

lemma is_prime_pow.two_le : ∀ {n : ℕ}, n.is_prime_pow → 2 ≤ n
| 0 h := (not_is_prime_pow_zero h).elim
| 1 h := (not_is_prime_pow_one h).elim
| (n+2) _ := le_add_self

theorem is_prime_pow.pos {n : ℕ} (hn : n.is_prime_pow) : 0 < n := zero_lt_two.trans_le hn.two_le

theorem is_prime_pow.ne_zero {n : ℕ} (h : n.is_prime_pow) : n ≠ 0 := h.pos.ne'

theorem is_prime_pow.one_lt {n : ℕ} (h : n.is_prime_pow) : 1 < n := h.two_le

lemma is_prime_pow.ne_one {n : ℕ} (hp : n.is_prime_pow) : n ≠ 1 := hp.one_lt.ne'

lemma is_prime_pow.dvd {n m : ℕ} (hn : n.is_prime_pow) (hm : m ∣ n) (hm₁ : m ≠ 1) :
  m.is_prime_pow :=
begin
  rcases hn with ⟨p, k, hp, hk, rfl⟩,
  obtain ⟨i, hik, rfl⟩ := (dvd_prime_pow hp).1 hm,
  refine ⟨p, i, hp, _, rfl⟩,
  apply nat.pos_of_ne_zero,
  rintro rfl,
  simpa using hm₁,
end

end nat
