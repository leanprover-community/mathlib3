/-
Copyright (c) 2021 Alex Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Zhao
-/
import tactic.suggest
import tactic.linarith.frontend
import data.rat.basic
import data.nat.prime
import data.int.gcd

/-!
# Chicken McNugget Theorem

In this file we prove the Chicken McNugget Theorem.

## Theorem Statement:
The Chicken McNugget Theorem states,
for two relatively prime integers larger than 1,
the largest integer not expressible as a sum of nonnegative multiples of these two
is m * n - m - n.

## Implementation Notes

This proof uses Bezout's greatest common divisor theorem
to create a construction for all integers greater than the maximal value
m * n - m - n. To show the maximal value doesn't work, it rewrites the equation into a multiple
of m equalling a multiple of n, then uses inequalities to show the multiples get too large.

## Tags

chicken mcnugget, frobenius coin
-/

open nat

/-- Auxiliary lemma for upper bound. -/
lemma chicken_mcnugget_upper_bound_aux (a b m n : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
  (cop : coprime m n) : a * m + b * n ≠ m * n :=
begin
  intro h,
  have h1 : n ∣ a,
  { apply cop.symm.dvd_of_dvd_mul_right,
    rw [nat.dvd_add_iff_left (dvd_mul_left n b), h],
    exact dvd_mul_left n m },
  have h2 : m ∣ b,
  { apply cop.dvd_of_dvd_mul_right,
    rw [nat.dvd_add_iff_right (dvd_mul_left m a), h],
    exact dvd_mul_right m n },
  obtain ⟨x, rfl⟩ := h1,
  obtain ⟨y, rfl⟩ := h2,
  rw [mul_comm n x, mul_comm m y, mul_assoc, mul_assoc, mul_comm n m, ←add_mul] at h,
  rw [mul_comm, mul_ne_zero_iff, ←one_le_iff_ne_zero] at ha hb,
  exact mul_ne_zero hb.2 ha.2 (eq_zero_of_mul_eq_self_left (ne_of_gt (add_le_add ha.1 hb.1)) h),
end

/-- No solution for the maximal value over the natural numbers, cleanly -/
lemma chicken_mcnugget_upper_bound (m n : ℕ) (cop : coprime m n) (hm : 1 < m) (hn : 1 < n) :
  ¬ ∃ (a b : ℕ), a * m + b * n = m * n - m - n :=
begin
  rintro ⟨a, b, h⟩,
  apply chicken_mcnugget_upper_bound_aux _ _ m n (add_one_ne_zero a) (add_one_ne_zero b) cop,
  rw [add_mul, add_mul, one_mul, one_mul, add_assoc, ←add_assoc m, add_comm m, add_assoc,
      ←add_assoc, h, nat.sub_sub, nat.sub_add_cancel (add_le_mul hm hn)],
end

/-- Constructs solutions for values greater than the maximal value over the positive integers. -/
lemma chicken_mcnugget_construction_ints (m n : ℤ) (mlb: m > 1) (nlb: n > 1) (cop: m.gcd n = 1):
  ∀ (k : ℤ), k > m * n - m - n → ∃ (a b : ℤ), a * m + b * n = k ∧ a ≥ 0 ∧ b ≥ 0 :=
begin
  rintro ⟨k, kbound⟩,
  have bezout := int.gcd_eq_gcd_ab m n,
  rw [cop,int.coe_nat_one] at bezout,
  have bezout2 : k*1 = k*(m * m.gcd_a n + n * m.gcd_b n),
  rw bezout,
  rw [mul_one,mul_add] at bezout2,
  repeat {rw [← mul_assoc] at bezout2},
  set p := (k*m.gcd_a n)%n with hp,
  set q := ((k*m.gcd_a n)/n*m)+(k*m.gcd_b n) with hq,
  refine ⟨p,q,_⟩,
  have part1 : p * m + q * n = k,
  rw [hq,hp],
  have claim : n * (k * m.gcd_a n / n) + k * m.gcd_a n % n-n * (k * m.gcd_a n / n)
    = (k * m.gcd_a n) - n * (k * m.gcd_a n / n),
    rw (int.div_add_mod (k*m.gcd_a n) n),

  rw [add_comm, add_sub_cancel] at claim,
  rw [claim,int.sub_mul,add_mul,← add_assoc,mul_comm n _,mul_assoc _ n m, mul_comm n m,
    ← mul_assoc _ m n, sub_add_cancel,mul_assoc k _ m,mul_assoc k _ n,mul_comm _ m,mul_comm _ n,
    ← mul_assoc,← mul_assoc,← bezout2],

  have pnonneg := int.mod_nonneg (k * m.gcd_a n) (ne_of_gt (lt_trans int.zero_lt_one nlb)),
  rw [← hp] at pnonneg,
  split,
  exact part1,
  split,
  exact pnonneg,
  by_contradiction,
  push_neg at h,
  rw [← part1] at kbound,
  have pbound := int.mod_lt_of_pos (k * m.gcd_a n) (lt_trans int.zero_lt_one nlb),
  rw [← hp] at pbound,
  rw [← sub_add_cancel n 1] at pbound,
  have pbound2 := int.lt_add_one_iff.1 pbound,
  have pbound3 := int.mul_le_mul_of_nonneg_right pbound2 (le_of_lt (lt_trans int.zero_lt_one mlb)),
  have qbound := int.sub_lt_sub_of_lt_of_le kbound pbound3,
  rw [add_comm,add_sub_cancel,sub_mul,← sub_add,one_mul] at qbound,
  have qbound3 := int.le_sub_right_of_add_le ((int.lt_iff_add_one_le q 0).1 h),
  have qbound4 := int.mul_le_mul_of_nonneg_right qbound3 (le_of_lt (lt_trans int.zero_lt_one nlb)),
  rw [sub_mul,zero_mul,one_mul] at qbound4,
  have qbound5 := int.add_le_add_right qbound4 n,
  rw sub_add_cancel at qbound5,
  repeat {rw sub_sub at qbound},
  rw [add_comm n _, ← add_assoc, add_comm m _, add_assoc, add_comm m n, ← add_assoc, ← sub_sub,
    ← sub_sub, mul_comm n m, sub_add_cancel] at qbound,
  have contra := int.add_lt_add_right qbound n,
  rw sub_add_cancel at contra,
  rw (int.sub_self (m*n)) at contra,
  exact not_lt_of_le qbound5 contra,
end

/-- Constructs solutions to values greater than the maximal value over the natural numbers. -/
lemma chicken_mcnugget_construction (m n: ℕ) (mpos: m>1) (npos: n>1) (cop: m.gcd n=1):
  ∀ (k:ℕ), k>m*n-m-n → ∃ (a b : ℕ), a*m+b*n=k :=
begin
  intros k kbound,
  have intcop : (m:ℤ).gcd(n:ℤ) = 1,
  { rw int.coe_nat_gcd,
    exact cop },

  have intkbound := lt_of_le_of_lt (int.sub_le_sub_right (int.coe_sub_ge (m*n) m) n)
    (lt_of_le_of_lt (int.coe_sub_ge (m*n-m) n) (int.coe_nat_lt.2 kbound)),
  rw int.coe_nat_mul at intkbound,

  -- "importing" the result from the ints
  have thing := chicken_mcnugget_construction_ints (m : ℤ) (n : ℤ)
    (int.coe_nat_lt.2 mpos) (int.coe_nat_lt.2 npos) intcop (k : ℤ) intkbound,
  rcases thing with ⟨a, b, relation, bounds⟩,
  cases bounds with anonneg bnonneg,

  -- ready to
  refine ⟨int.nat_abs a, int.nat_abs b, _⟩,
  have nat_relation : int.nat_abs (a*(m:ℤ)+b*(n:ℤ)) = int.nat_abs(k : ℤ),
  rw relation,
  rw int.nat_abs_of_nat at nat_relation,
  have left_nonneg := int.mul_le_mul anonneg (int.coe_nat_nonneg m) (le_of_eq (refl 0)) anonneg,
  have right_nonneg := int.mul_le_mul bnonneg (int.coe_nat_nonneg n) (le_of_eq (refl 0)) bnonneg,
  rw mul_zero at left_nonneg right_nonneg,
  rw (int.nat_abs_add_nonneg left_nonneg right_nonneg) at nat_relation,
  repeat {rw int.nat_abs_mul at nat_relation},
  have thingm := int.nat_abs_of_nat_core m,
  have thingn := int.nat_abs_of_nat_core n,
  rw int.of_nat_eq_coe at thingm,
  rw int.of_nat_eq_coe at thingn,
  rw [thingm, thingn] at nat_relation,
  exact nat_relation,
end

/-- This theorem combines both sublemmas in a single claim. -/
theorem chicken_mcnugget (m n: ℕ) (mlb: m > 1) (nlb: n > 1) (cop: m.gcd n = 1):
  (¬ ∃ (a b : ℕ), a * m + b * n = m * n - m - n) ∧
    ∀ (k : ℕ), k > m * n - m - n → ∃ (a b : ℕ), a * m + b * n = k :=
begin
  split,
  exact (chicken_mcnugget_upper_bound m n cop mlb nlb),
  exact (chicken_mcnugget_construction m n mlb nlb cop),
end
