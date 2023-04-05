/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import algebra.associated
import number_theory.divisors

/-!
# Prime powers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

lemma is_prime_pow.not_unit {n : R} (h : is_prime_pow n) : ¬is_unit n :=
let ⟨p, k, hp, hk, hn⟩ := h in hn ▸ (is_unit_pow_iff hk.ne').not.mpr hp.not_unit

lemma is_unit.not_is_prime_pow {n : R} (h : is_unit n) : ¬is_prime_pow n :=
λ h', h'.not_unit h

lemma not_is_prime_pow_one : ¬ is_prime_pow (1 : R) := is_unit_one.not_is_prime_pow

lemma prime.is_prime_pow {p : R} (hp : prime p) : is_prime_pow p :=
⟨p, 1, hp, zero_lt_one, by simp⟩

lemma is_prime_pow.pow {n : R} (hn : is_prime_pow n)
  {k : ℕ} (hk : k ≠ 0) : is_prime_pow (n ^ k) :=
let ⟨p, k', hp, hk', hn⟩ := hn in ⟨p, k * k', hp, mul_pos hk.bot_lt hk', by rw [pow_mul', hn]⟩

theorem is_prime_pow.ne_zero [no_zero_divisors R] {n : R} (h : is_prime_pow n) : n ≠ 0 :=
λ t, eq.rec not_is_prime_pow_zero t.symm h

lemma is_prime_pow.ne_one {n : R} (h : is_prime_pow n) : n ≠ 1 :=
λ t, eq.rec not_is_prime_pow_one t.symm h

section nat

lemma is_prime_pow_nat_iff (n : ℕ) :
  is_prime_pow n ↔ ∃ (p k : ℕ), nat.prime p ∧ 0 < k ∧ p ^ k = n :=
by simp only [is_prime_pow_def, nat.prime_iff]

lemma nat.prime.is_prime_pow {p : ℕ} (hp : p.prime) : is_prime_pow p := hp.prime.is_prime_pow

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

lemma nat.disjoint_divisors_filter_prime_pow {a b : ℕ} (hab : a.coprime b) :
  disjoint (a.divisors.filter is_prime_pow) (b.divisors.filter is_prime_pow) :=
begin
  simp only [finset.disjoint_left, finset.mem_filter, and_imp, nat.mem_divisors, not_and],
  rintro n han ha hn hbn hb -,
  exact hn.ne_one (nat.eq_one_of_dvd_coprimes hab han hbn),
end

lemma is_prime_pow.two_le : ∀ {n : ℕ}, is_prime_pow n → 2 ≤ n
| 0 h := (not_is_prime_pow_zero h).elim
| 1 h := (not_is_prime_pow_one h).elim
| (n+2) _ := le_add_self

theorem is_prime_pow.pos {n : ℕ} (hn : is_prime_pow n) : 0 < n := pos_of_gt hn.two_le

theorem is_prime_pow.one_lt {n : ℕ} (h : is_prime_pow n) : 1 < n := h.two_le

end nat
