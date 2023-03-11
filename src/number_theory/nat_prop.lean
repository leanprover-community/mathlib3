/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
--import data.nat.prime
import data.nat.parity
--import algebra.order.with_zero
--import ring_theory.coprime.lemmas
--import algebra.gcd_monoid.basic
import ring_theory.int.basic

/-!
# Properties of natural numbers
This file describes some properties of natural numbers that are required throughout this project.
In the end, we keep some `helper` lemmas which are specific to this project.

## Tags
Naturals
-/

namespace nat
--lemma dvd_sub_comm {a b n : ℕ} (h : (n : ℤ) ∣ (a : ℤ) - (b : ℤ)) : (n : ℤ) ∣ (b : ℤ) - (a : ℤ) :=
--(dvd_neg ↑n (↑b - ↑a)).mp (by {simp only [h, neg_sub]})

lemma coprime_sub {n m : ℕ} (h : n.coprime m) (hn : m ≤ n) : (n - m).coprime n :=
begin
  by_contradiction h',
  obtain ⟨p, h1, h2, h3⟩ := nat.prime.not_coprime_iff_dvd.1 h',
  have h4 := nat.dvd_sub (nat.sub_le _ _) h3 h2,
  rw nat.sub_sub_self hn at h4,
  apply nat.prime.not_coprime_iff_dvd.2 ⟨p, h1, h3, h4⟩ h,
end

--lemma ne_zero_of_lt' (b : ℕ) {a : ℕ} [fact (b < a)] : a ≠ 0 := @ne_zero_of_lt _ _ b _ (fact.out _)

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

-- lemma lt_pow {n a : ℕ} (h1 : 1 < a) (h2 : 1 < n) : a < a^n :=
-- begin
--   conv { congr, rw ←pow_one a, skip, skip, },
--   apply pow_lt_pow h1 h2,
-- end

-- lemma le_pow {n a : ℕ} (h1 : 1 ≤ a) (h2 : 1 ≤ n) : a ≤ a^n :=
-- begin
--   conv { congr, rw ←pow_one a, skip, skip, },
--   apply pow_le_pow h1 h2,
-- end

lemma pow_lt_mul_pow_succ_right [fact (0 < d)] (m : ℕ) : p ^ m < d * p ^ m.succ :=
begin
  rw [pow_succ, ←mul_assoc],
  apply lt_mul_of_one_lt_left (pow_pos (nat.prime.pos (fact.out _)) _)
    (one_lt_mul ((nat.succ_le_iff).2 (fact.out _)) (nat.prime.one_lt (fact.out _))),
  all_goals { assumption, },
end

lemma lt_mul_pow_right {m a b : ℕ} (h1 : 0 < b) (h2 : 1 < a) (h3 : 1 < m) : a < b * a^m :=
lt_of_le_of_lt ((le_mul_iff_one_le_left (lt_trans zero_lt_one h2)).2 h1)
  (mul_lt_mul' le_rfl (nat.lt_pow h2 h3) (nat.zero_le _) h1)

lemma le_mul_pow_right {m a b : ℕ} (h1 : 0 < b) (h2 : 1 < a) (h3 : 1 ≤ m) : a ≤ b * a^m :=
le_trans ((le_mul_iff_one_le_left (lt_trans zero_lt_one h2)).2 h1)
  (mul_le_mul' le_rfl (nat.le_pow (le_of_lt h2) h3))

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

-- lemma coprime.mul_pow {a b c : ℕ} (n : ℕ) (hc' : c.coprime a) (hc : c.coprime b) :
--   c.coprime (a * b^n) := coprime_mul_iff_right.2 ⟨hc', coprime.pow_right n hc⟩

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

--lemma pred_add_one_eq_self {n : ℕ} (hn : 0 < n) : n.pred + 1 = n := nat.succ_pred_eq_of_pos hn

lemma prime_dvd_of_not_coprime (p : ℕ) [fact p.prime] {n : ℕ} (h : ¬ n.coprime p) : p ∣ n :=
begin
  have := @nat.coprime_or_dvd_of_prime p (fact.out _) n,
  cases this,
  { exfalso, apply h this.symm, },
  { assumption, },
end

lemma eq_zero_of_not_pos {n : ℕ} (hn : ¬ 0 < n) : n = 0 := by finish

lemma coprime_of_dvd_of_coprime {m n x y : ℕ} (h : m.coprime n) (hx : x ∣ m) (hy : y ∣ n) :
  x.coprime y :=
begin
  have : x.coprime n,
  { rw ← nat.is_coprime_iff_coprime,
    apply is_coprime.of_coprime_of_dvd_left (nat.is_coprime_iff_coprime.2 h) _,
    norm_cast, assumption, },
  rw ← nat.is_coprime_iff_coprime,
  apply is_coprime.of_coprime_of_dvd_right (nat.is_coprime_iff_coprime.2 this) _,
  norm_cast, assumption,
end

lemma sub_ne_zero {n k : ℕ} (h : k < n) : n - k ≠ 0 :=
begin
  intro h',
  rw nat.sub_eq_zero_iff_le at h',
  rw ← not_lt at h',
  apply h' h,
end

lemma coprime.sub_self {m n : ℕ} (h : m.coprime n) (h' : m ≤ n) : (n - m).coprime n :=
begin
  contrapose h,
  rw nat.prime.not_coprime_iff_dvd at *,
  rcases h with ⟨p, hp, h1, h2⟩,
  refine ⟨p, hp, _, h2⟩,
  rw ← nat.sub_sub_self h',
  apply nat.dvd_sub (nat.sub_le _ _) h2 h1,
end
end nat

lemma helper_4 {x y : ℕ} (m : ℕ) [fact (0 < m)] : gcd_monoid.lcm (x * y^m) y = x * y^m :=
begin
  rw lcm_eq_left_iff _ _ _,
  apply dvd_mul_of_dvd_right (dvd_pow_self y (nat.ne_zero_of_lt' 0)) x,
  { apply_instance, },
  { rw normalize_eq _, },
end

--variables {p : ℕ} [fact p.prime] {d m : ℕ}
-- lemma helper_5 {k : ℕ} (hk : 1 < k) : (d * p^m)^(k - 1) = (d * p^m) * (d * p^m)^(k - 2) :=
-- begin
--   conv_rhs { congr, rw ←pow_one (d * p^m), },
--   rw [←pow_add],
--   congr,
--   rw add_comm,
--   conv_rhs { rw [nat.sub_succ, ←nat.succ_eq_add_one,
--     nat.succ_pred_eq_of_pos (lt_tsub_iff_right.2 _)], skip, apply_congr hk, },
-- end
