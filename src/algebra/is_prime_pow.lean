/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import algebra.associated
import data.nat.factorization

/-!
# Prime powers

This file deals with prime powers: numbers which are positive integer powers of a single prime.
-/

variables {R : Type*} [comm_monoid_with_zero R] (n p : R) (k : ℕ)

/-- `n` is a prime power if there is a prime `p` and a positive natural `k` such that `n` can be
written as `p^k`. -/
def is_prime_pow : Prop :=
∃ (p : R) (k : ℕ), prime p ∧ 0 < k ∧ p ^ k = n

lemma is_prime_pow_def :
  is_prime_pow n ↔ ∃ (p : R) (k : ℕ), prime p ∧ 0 < k ∧ p ^ k = n := iff.rfl

/-- An equivalent definition for prime powers: `n` is a prime power iff there is a prime `p` and a
natural `k` such that `n` can be written as `p^(k+1)`. -/
lemma is_prime_pow_iff_pow_succ :
  is_prime_pow n ↔ ∃ (p : R) (k : ℕ), prime p ∧ p ^ (k + 1) = n :=
(is_prime_pow_def _).trans
⟨λ ⟨p, k, hp, hk, hn⟩, ⟨_, _, hp, by rwa [nat.sub_add_cancel hk]⟩,
  λ ⟨p, k, hp, hn⟩, ⟨_, _, hp, nat.succ_pos', hn⟩⟩

lemma not_is_prime_pow_zero [no_zero_divisors R] :
  ¬ is_prime_pow (0 : R) :=
begin
  simp only [is_prime_pow_def, not_exists, not_and', and_imp],
  intros x n hn hx,
  rw pow_eq_zero hx,
  simp,
end

lemma not_is_prime_pow_one : ¬ is_prime_pow (1 : R) :=
begin
  simp only [is_prime_pow_def, not_exists, not_and', and_imp],
  intros x n hn hx ht,
  exact ht.not_unit (is_unit_of_pow_eq_one x n hx hn),
end

lemma prime.is_prime_pow {p : R} (hp : prime p) : is_prime_pow p :=
⟨p, 1, hp, zero_lt_one, by simp⟩

lemma is_prime_pow.pow {n : R} (hn : is_prime_pow n)
  {k : ℕ} (hk : k ≠ 0) : is_prime_pow (n ^ k) :=
let ⟨p, k', hp, hk', hn⟩ := hn in ⟨p, k * k', hp, mul_pos hk.bot_lt hk', by rw [pow_mul', hn]⟩

theorem is_prime_pow.ne_zero [no_zero_divisors R] {n : R} (h : is_prime_pow n) : n ≠ 0 :=
λ t, eq.rec not_is_prime_pow_zero t.symm h

lemma is_prime_pow.ne_one {n : R} (h : is_prime_pow n) : n ≠ 1 :=
λ t, eq.rec not_is_prime_pow_one t.symm h

section unique_units

lemma eq_of_prime_pow_eq {R : Type*} [cancel_comm_monoid_with_zero R] [unique Rˣ] {p₁ p₂ : R}
  {k₁ k₂ : ℕ} (hp₁ : prime p₁) (hp₂ : prime p₂) (hk₁ : 0 < k₁) (h : p₁ ^ k₁ = p₂ ^ k₂) :
  p₁ = p₂ :=
by { rw [←associated_iff_eq] at h ⊢, apply h.of_pow_associated_of_prime hp₁ hp₂ hk₁ }

lemma eq_of_prime_pow_eq' {R : Type*} [cancel_comm_monoid_with_zero R] [unique Rˣ] {p₁ p₂ : R}
  {k₁ k₂ : ℕ} (hp₁ : prime p₁) (hp₂ : prime p₂) (hk₁ : 0 < k₂) (h : p₁ ^ k₁ = p₂ ^ k₂) :
  p₁ = p₂ :=
by { rw [←associated_iff_eq] at h ⊢, apply h.of_pow_associated_of_prime' hp₁ hp₂ hk₁ }

end unique_units

section nat

lemma is_prime_pow_nat_iff (n : ℕ) :
  is_prime_pow n ↔ ∃ (p k : ℕ), nat.prime p ∧ 0 < k ∧ p ^ k = n :=
by simp only [is_prime_pow_def, nat.prime_iff]

lemma is_prime_pow_nat_iff_bounded (n : ℕ) :
  is_prime_pow n ↔ ∃ (p : ℕ), p ≤ n ∧ ∃ (k : ℕ), k ≤ n ∧ p.prime ∧ 0 < k ∧ p ^ k = n :=
begin
  rw is_prime_pow_nat_iff,
  refine iff.symm ⟨λ ⟨p, _, k, _, hp, hk, hn⟩, ⟨p, k, hp, hk, hn⟩, _⟩,
  rintro ⟨p, k, hp, hk, rfl⟩,
  refine ⟨p, _, k, (nat.lt_pow_self hp.one_lt _).le, hp, hk, rfl⟩,
  simpa using nat.pow_le_pow_of_le_right hp.pos hk,
end

instance {n : ℕ} : decidable (is_prime_pow n) :=
decidable_of_iff' _ (is_prime_pow_nat_iff_bounded n)

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
  rcases n.eq_zero_or_pos with rfl | hn',
  { simpa using h },
  refine ⟨_, _, nat.prime_iff.1 (nat.min_fac_prime hn), _, h⟩,
  rw [pos_iff_ne_zero, ←finsupp.mem_support_iff, nat.factor_iff_mem_factorization,
    nat.mem_factors_iff_dvd hn' (nat.min_fac_prime hn)],
  apply nat.min_fac_dvd
end

lemma is_prime_pow_iff_min_fac_pow_factorization_eq {n : ℕ} (hn : n ≠ 1) :
  is_prime_pow n ↔ n.min_fac ^ n.factorization n.min_fac = n :=
⟨λ h, h.min_fac_pow_factorization_eq, λ h, is_prime_pow_of_min_fac_pow_factorization_eq h hn⟩


lemma is_prime_pow.dvd {n m : ℕ} (hn : is_prime_pow n) (hm : m ∣ n) (hm₁ : m ≠ 1) :
  is_prime_pow m :=
begin
  rw is_prime_pow_nat_iff at hn ⊢,
  rcases hn with ⟨p, k, hp, hk, rfl⟩,
  obtain ⟨i, hik, rfl⟩ := (nat.dvd_prime_pow hp).1 hm,
  refine ⟨p, i, hp, _, rfl⟩,
  apply nat.pos_of_ne_zero,
  rintro rfl,
  simpa using hm₁,
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
  -- Take care of the n = 0 case
  rcases n.eq_zero_or_pos with rfl | hn₀,
  { obtain ⟨q, hq', hq''⟩ := nat.exists_infinite_primes (p + 1),
    cases hq q ⟨hq'', by simp⟩,
    simpa using hq' },
  -- So assume 0 < n
  refine ⟨p, n.factors.count p, hp, _, _⟩,
  { apply list.count_pos.2,
    rwa nat.mem_factors_iff_dvd hn₀ hp },
  simp only [and_imp] at hq,
  apply nat.dvd_antisymm (nat.pow_factors_count_dvd _ _),
  -- We need to show n ∣ p ^ n.factors.count p
  apply nat.dvd_of_factors_subperm hn₀.ne',
  rw [hp.factors_pow, list.subperm_ext_iff],
  intros q hq',
  rw nat.mem_factors hn₀.ne' at hq',
  cases hq _ hq'.1 hq'.2,
  simp,
end

lemma is_prime_pow.two_le : ∀ {n : ℕ}, is_prime_pow n → 2 ≤ n
| 0 h := (not_is_prime_pow_zero h).elim
| 1 h := (not_is_prime_pow_one h).elim
| (n+2) _ := le_add_self

theorem is_prime_pow.pos {n : ℕ} (hn : is_prime_pow n) : 0 < n := pos_of_gt hn.two_le

theorem is_prime_pow.one_lt {n : ℕ} (h : is_prime_pow n) : 1 < n := h.two_le

end nat
