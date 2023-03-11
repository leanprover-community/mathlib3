/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import data.nat.parity
import ring_theory.int.basic

/-!
# Properties of natural numbers
This file describes some properties of natural numbers.

## Tags
Naturals
-/

namespace nat
lemma coprime_sub {n m : ℕ} (h : n.coprime m) (hn : m ≤ n) : (n - m).coprime n :=
begin
  by_contradiction h',
  obtain ⟨p, h1, h2, h3⟩ := nat.prime.not_coprime_iff_dvd.1 h',
  have h4 := nat.dvd_sub (nat.sub_le _ _) h3 h2,
  rw nat.sub_sub_self hn at h4,
  apply nat.prime.not_coprime_iff_dvd.2 ⟨p, h1, h3, h4⟩ h,
end

lemma lt_mul_pow_right {m a b : ℕ} (h1 : 0 < b) (h2 : 1 < a) (h3 : 1 < m) : a < b * a^m :=
lt_of_le_of_lt ((le_mul_iff_one_le_left (lt_trans zero_lt_one h2)).2 h1)
  (mul_lt_mul' le_rfl (lt_pow h2 h3) (nat.zero_le _) h1)

lemma le_mul_pow_right {m a b : ℕ} (h1 : 0 < b) (h2 : 1 < a) (h3 : 1 ≤ m) : a ≤ b * a^m :=
le_trans ((le_mul_iff_one_le_left (lt_trans zero_lt_one h2)).2 h1)
  (mul_le_mul' le_rfl (le_pow (le_of_lt h2) h3))

lemma cast_eq_coe_b (x : ℕ) : @nat.cast ℤ _ x = coe_b x :=
begin
  induction x with d hd,
  { change 0 = @has_coe.coe ℕ ℤ _ 0,
    change _ = int.of_nat 0,
    simp only [int.coe_nat_zero, int.of_nat_eq_coe], },
  { show d.cast + 1 = @has_coe.coe ℕ ℤ _ d.succ,
    change _ = int.of_nat d.succ,
    simp only [int.of_nat_eq_coe, int.coe_nat_succ, add_left_inj],
    change _ = int.of_nat d at hd, simp [hd], },
end

lemma add_sub_pred (n : ℕ) : n + (n - 1) = 2 * n - 1 :=
begin
  cases n,
  { refl, },
  { rw [←nat.add_sub_assoc (nat.succ_le_succ (nat.zero_le _)), nat.succ_mul, one_mul], },
end

lemma two_mul_sub_one_mod_two_eq_one {k : ℕ} (hk : 1 ≤ k) : (2 * k - 1) % 2 = 1 :=
begin
  have : 2 * k - 1 = 2 * k + 1 - 2, { norm_num, },
  rw [this, ←nat.mod_eq_sub_mod (nat.succ_le_succ (one_le_mul one_le_two hk)),
    nat.odd_iff.1 ⟨k, rfl⟩],
end

variables {p : ℕ} [fact p.prime] {d : ℕ}
lemma one_lt_mul_pow_of_ne_one [fact (0 < d)] {k : ℕ} (h : d * p^k ≠ 1) : 1 < d * p^k :=
nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨nat.mul_ne_zero (ne_zero_of_lt' 0)
  (pow_ne_zero _ (nat.prime.ne_zero (fact.out _))), h⟩

lemma mul_pow_eq_one_of_mul_pow_sq_not_one_lt {p : ℕ} [fact p.prime] {d : ℕ} [fact (0 < d)]
  {n : ℕ} (h : ¬ 1 < d * p^(2 * n)) : d * p^n = 1 :=
begin
  rw [not_lt_iff_eq_or_lt, lt_one_iff, nat.mul_eq_zero] at h,
  cases h,
  { have h' := h.symm,
    rw [nat.mul_eq_one_iff, pow_mul', pow_succ, pow_one, nat.mul_eq_one_iff] at h',
    rw [h'.1, h'.2.1, one_mul], },
  { have p2 : p^(2 * n) ≠ 0 := pow_ne_zero _ (nat.prime.ne_zero (fact.out _)),
    simp only [ne_zero_of_lt' 0, p2, or_self] at h,
    exfalso,
    exact h, },
end

instance [fact (0 < d)] {n : ℕ} : fact (0 < d * p^n) :=
fact_iff.2 (mul_pos (fact.out _) (pow_pos (nat.prime.pos (fact.out _)) _))

lemma mul_prime_pow_pos [fact (0 < d)] (m : ℕ) : 0 < d * p^m := fact_iff.1 infer_instance

lemma mul_pow_lt_mul_pow_succ [fact (0 < d)] (m : ℕ) : d * p ^ m < d * p ^ m.succ :=
mul_lt_mul' le_rfl (nat.pow_lt_pow_succ (nat.prime.one_lt (fact_iff.1 infer_instance)) m)
    (nat.zero_le _) (fact_iff.1 infer_instance)

lemma pow_lt_mul_pow_succ_right [fact (0 < d)] (m : ℕ) : p ^ m < d * p ^ m.succ :=
begin
  rw [pow_succ, ←mul_assoc],
  apply lt_mul_of_one_lt_left (pow_pos (nat.prime.pos (fact.out _)) _)
    (one_lt_mul ((nat.succ_le_iff).2 (fact.out _)) (nat.prime.one_lt (fact.out _))),
  all_goals { assumption, },
end
end nat
