/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/

import algebra.is_prime_pow
import set_theory.cardinal.ordinal

/-!
# Cardinal Divisibility

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show basic results about divisibility in the cardinal numbers. This relation can be characterised
in the following simple way: if `a` and `b` are both less than `ℵ₀`, then `a ∣ b` iff they are
divisible as natural numbers. If `b` is greater than `ℵ₀`, then `a ∣ b` iff `a ≤ b`. This
furthermore shows that all infinite cardinals are prime; recall that `a * b = max a b` if
`ℵ₀ ≤ a * b`; therefore `a ∣ b * c = a ∣ max b c` and therefore clearly either `a ∣ b` or `a ∣ c`.
Note furthermore that no infinite cardinal is irreducible
(`cardinal.not_irreducible_of_aleph_0_le`), showing that the cardinal numbers do not form a
`comm_cancel_monoid_with_zero`.

## Main results

* `cardinal.prime_of_aleph_0_le`: a `cardinal` is prime if it is infinite.
* `cardinal.is_prime_iff`: a `cardinal` is prime iff it is infinite or a prime natural number.
* `cardinal.is_prime_pow_iff`: a `cardinal` is a prime power iff it is infinite or a natural number
  which is itself a prime power.

-/

namespace cardinal

open_locale cardinal

universe u
variables {a b : cardinal.{u}} {n m : ℕ}

@[simp] lemma is_unit_iff : is_unit a ↔ a = 1 :=
begin
  refine ⟨λ h, _, by { rintro rfl, exact is_unit_one }⟩,
  rcases eq_or_ne a 0 with rfl | ha,
  { exact (not_is_unit_zero h).elim },
  rw is_unit_iff_forall_dvd at h,
  cases h 1 with t ht,
  rw [eq_comm, mul_eq_one_iff'] at ht,
  { exact ht.1 },
  all_goals { rwa one_le_iff_ne_zero },
  { rintro rfl,
    rw mul_zero at ht,
    exact zero_ne_one ht }
end

instance : unique cardinal.{u}ˣ :=
{ default := 1,
  uniq := λ a, units.coe_eq_one.mp $ is_unit_iff.mp a.is_unit }

theorem le_of_dvd : ∀ {a b : cardinal}, b ≠ 0 → a ∣ b → a ≤ b
| a _ b0 ⟨b, rfl⟩ := by simpa only [mul_one] using mul_le_mul_left'
  (one_le_iff_ne_zero.2 (λ h : b = 0, by simpa only [h, mul_zero] using b0)) a

lemma dvd_of_le_of_aleph_0_le (ha : a ≠ 0) (h : a ≤ b) (hb : ℵ₀ ≤ b) : a ∣ b :=
⟨b, (mul_eq_right hb h ha).symm⟩

@[simp] lemma prime_of_aleph_0_le (ha : ℵ₀ ≤ a) : prime a :=
begin
  refine ⟨(aleph_0_pos.trans_le ha).ne', _, λ b c hbc, _⟩,
  { rw is_unit_iff,
    exact (one_lt_aleph_0.trans_le ha).ne' },
  cases eq_or_ne (b * c) 0 with hz hz,
  { rcases mul_eq_zero.mp hz with rfl | rfl; simp },
  wlog h : c ≤ b,
  { cases le_total c b; [skip, rw or_comm]; apply_assumption, assumption',
    all_goals { rwa mul_comm } },
  left,
  have habc := le_of_dvd hz hbc,
  rwa [mul_eq_max' $ ha.trans $ habc, max_def', if_pos h] at hbc
end

lemma not_irreducible_of_aleph_0_le (ha : ℵ₀ ≤ a) : ¬irreducible a :=
begin
  rw [irreducible_iff, not_and_distrib],
  refine or.inr (λ h, _),
  simpa [mul_aleph_0_eq ha, is_unit_iff, (one_lt_aleph_0.trans_le ha).ne', one_lt_aleph_0.ne']
    using h a ℵ₀
end

@[simp, norm_cast] lemma nat_coe_dvd_iff : (n : cardinal) ∣ m ↔ n ∣ m :=
begin
  refine ⟨_, λ ⟨h, ht⟩, ⟨h, by exact_mod_cast ht⟩⟩,
  rintro ⟨k, hk⟩,
  have : ↑m < ℵ₀ := nat_lt_aleph_0 m,
  rw [hk, mul_lt_aleph_0_iff] at this,
  rcases this with h | h | ⟨-, hk'⟩,
  iterate 2 { simp only [h, mul_zero,  zero_mul, nat.cast_eq_zero] at hk, simp [hk] },
  lift k to ℕ using hk',
  exact ⟨k, by exact_mod_cast hk⟩
end

@[simp] lemma nat_is_prime_iff : prime (n : cardinal) ↔ n.prime :=
begin
  simp only [prime, nat.prime_iff],
  refine and_congr (by simp) (and_congr _ ⟨λ h b c hbc, _, λ h b c hbc, _⟩),
  { simp only [is_unit_iff, nat.is_unit_iff],
    exact_mod_cast iff.rfl },
  { exact_mod_cast h b c (by exact_mod_cast hbc) },
  cases lt_or_le (b * c) ℵ₀ with h' h',
  { rcases mul_lt_aleph_0_iff.mp h' with rfl | rfl | ⟨hb, hc⟩,
    { simp },
    { simp },
    lift b to ℕ using hb,
    lift c to ℕ using hc,
    exact_mod_cast h b c (by exact_mod_cast hbc) },
  rcases aleph_0_le_mul_iff.mp h' with ⟨hb, hc, hℵ₀⟩,
  have hn : (n : cardinal) ≠ 0,
  { intro h,
    rw [h, zero_dvd_iff, mul_eq_zero] at hbc,
    cases hbc; contradiction },
  wlog hℵ₀b : ℵ₀ ≤ b,
  { refine (this h c b _ _ hc hb hℵ₀.symm hn (hℵ₀.resolve_left hℵ₀b)).symm; rwa mul_comm },
  exact or.inl (dvd_of_le_of_aleph_0_le hn ((nat_lt_aleph_0 n).le.trans hℵ₀b) hℵ₀b),
end

lemma is_prime_iff {a : cardinal} : prime a ↔ ℵ₀ ≤ a ∨ ∃ p : ℕ, a = p ∧ p.prime :=
begin
  cases le_or_lt ℵ₀ a with h h,
  { simp [h] },
  lift a to ℕ using id h,
  simp [not_le.mpr h]
end

lemma is_prime_pow_iff {a : cardinal} :
  is_prime_pow a ↔ ℵ₀ ≤ a ∨ ∃ n : ℕ, a = n ∧ is_prime_pow n :=
begin
  by_cases h : ℵ₀ ≤ a,
  { simp [h, (prime_of_aleph_0_le h).is_prime_pow] },
  lift a to ℕ using not_le.mp h,
  simp only [h, nat.cast_inj, exists_eq_left', false_or, is_prime_pow_nat_iff],
  rw is_prime_pow_def,
  refine ⟨_, λ ⟨p, k, hp, hk, h⟩, ⟨p, k, nat_is_prime_iff.2 hp, by exact_mod_cast and.intro hk h⟩⟩,
  rintro ⟨p, k, hp, hk, hpk⟩,
  have key : _ ≤ p ^ k :=
    power_le_power_left hp.ne_zero (show (1 : cardinal) ≤ k, by exact_mod_cast hk),
  rw [power_one, hpk] at key,
  lift p to ℕ using key.trans_lt (nat_lt_aleph_0 a),
  exact ⟨p, k, nat_is_prime_iff.mp hp, hk, by exact_mod_cast hpk⟩
end

end cardinal
