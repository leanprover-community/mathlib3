/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import algebra.group_power.basic
import algebra.group_with_zero.commute
import algebra.hom.ring
import algebra.ring.commute
import algebra.group_with_zero.divisibility
import algebra.ring.divisibility
import data.nat.order.basic

/-!
# Power operations on monoids with zero, semirings, and rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides additional lemmas about the natural power operator on rings and semirings.
Further lemmas about ordered semirings and rings can be found in `algebra.group_power.lemmas`.

-/

variables {R S M : Type*}

section monoid_with_zero
variables [monoid_with_zero M]

lemma zero_pow : ∀ {n : ℕ}, 0 < n → (0 : M) ^ n = 0
| (n+1) _ := by rw [pow_succ, zero_mul]

@[simp] lemma zero_pow' : ∀ n : ℕ, n ≠ 0 → (0 : M) ^ n = 0
| 0     h := absurd rfl h
| (k+1) h := by { rw [pow_succ], exact zero_mul _ }

lemma zero_pow_eq (n : ℕ) : (0 : M)^n = if n = 0 then 1 else 0 :=
begin
  split_ifs with h,
  { rw [h, pow_zero], },
  { rw [zero_pow (nat.pos_of_ne_zero h)] },
end

lemma pow_eq_zero_of_le {x : M} {n m : ℕ}
  (hn : n ≤ m) (hx : x^n = 0) : x^m = 0 :=
by rw [← tsub_add_cancel_of_le hn, pow_add, hx, mul_zero]

theorem pow_eq_zero [no_zero_divisors M] {x : M} {n : ℕ} (H : x^n = 0) :
  x = 0 :=
begin
  induction n with n ih,
  { rw pow_zero at H,
    rw [← mul_one x, H, mul_zero] },
  { rw pow_succ at H,
    exact or.cases_on (mul_eq_zero.1 H) id ih }
end

@[simp] lemma pow_eq_zero_iff [no_zero_divisors M]
  {a : M} {n : ℕ} (hn : 0 < n) :
  a ^ n = 0 ↔ a = 0 :=
begin
  refine ⟨pow_eq_zero, _⟩,
  rintros rfl,
  exact zero_pow hn,
end

lemma pow_eq_zero_iff' [no_zero_divisors M] [nontrivial M]
  {a : M} {n : ℕ} :
  a ^ n = 0 ↔ a = 0 ∧ n ≠ 0 :=
by cases (zero_le n).eq_or_gt; simp [*, ne_of_gt]

lemma pow_ne_zero_iff [no_zero_divisors M] {a : M} {n : ℕ} (hn : 0 < n) :
  a ^ n ≠ 0 ↔ a ≠ 0 :=
(pow_eq_zero_iff hn).not

lemma ne_zero_pow {a : M} {n : ℕ} (hn : n ≠ 0) : a ^ n ≠ 0 → a ≠ 0 :=
by { contrapose!, rintro rfl, exact zero_pow' n hn }

@[field_simps] theorem pow_ne_zero [no_zero_divisors M]
  {a : M} (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 :=
mt pow_eq_zero h

instance ne_zero.pow [no_zero_divisors M] {x : M} [ne_zero x] {n : ℕ} :
  ne_zero (x ^ n) := ⟨pow_ne_zero n ne_zero.out⟩

theorem sq_eq_zero_iff [no_zero_divisors M] {a : M} : a ^ 2 = 0 ↔ a = 0 :=
pow_eq_zero_iff two_pos

@[simp] lemma zero_pow_eq_zero [nontrivial M] {n : ℕ} : (0 : M) ^ n = 0 ↔ 0 < n :=
begin
  split; intro h,
  { rw [pos_iff_ne_zero], rintro rfl, simpa using h },
  { exact zero_pow' n h.ne.symm }
end

lemma ring.inverse_pow (r : M) : ∀ (n : ℕ), ring.inverse r ^ n = ring.inverse (r ^ n)
| 0 := by rw [pow_zero, pow_zero, ring.inverse_one]
| (n + 1) := by rw [pow_succ, pow_succ', ring.mul_inverse_rev' ((commute.refl r).pow_left n),
                    ring.inverse_pow]

end monoid_with_zero

section comm_monoid_with_zero
variables [comm_monoid_with_zero M] {n : ℕ} (hn : 0 < n)
include M hn

/-- We define `x ↦ x^n` (for positive `n : ℕ`) as a `monoid_with_zero_hom` -/
def pow_monoid_with_zero_hom : M →*₀ M :=
{ map_zero' := zero_pow hn,
  ..pow_monoid_hom n }

@[simp]
lemma coe_pow_monoid_with_zero_hom : (pow_monoid_with_zero_hom hn : M → M) = (^ n) := rfl

@[simp]
lemma pow_monoid_with_zero_hom_apply (a : M) : pow_monoid_with_zero_hom hn a = a ^ n := rfl

end comm_monoid_with_zero

lemma pow_dvd_pow_iff [cancel_comm_monoid_with_zero R]
  {x : R} {n m : ℕ} (h0 : x ≠ 0) (h1 : ¬ is_unit x) :
  x ^ n ∣ x ^ m ↔ n ≤ m :=
begin
  split,
  { intro h, rw [← not_lt], intro hmn, apply h1,
    have : x ^ m * x ∣ x ^ m * 1,
    { rw [← pow_succ', mul_one], exact (pow_dvd_pow _ (nat.succ_le_of_lt hmn)).trans h },
    rwa [mul_dvd_mul_iff_left, ← is_unit_iff_dvd_one] at this, apply pow_ne_zero m h0 },
  { apply pow_dvd_pow }
end

section semiring
variables [semiring R] [semiring S]

protected lemma ring_hom.map_pow (f : R →+* S) (a) :
  ∀ n : ℕ, f (a ^ n) = (f a) ^ n :=
map_pow f a

lemma min_pow_dvd_add {n m : ℕ} {a b c : R} (ha : c ^ n ∣ a) (hb : c ^ m ∣ b) :
  c ^ (min n m) ∣ a + b :=
begin
  replace ha := (pow_dvd_pow c (min_le_left n m)).trans ha,
  replace hb := (pow_dvd_pow c (min_le_right n m)).trans hb,
  exact dvd_add ha hb
end

end semiring

section comm_semiring
variables [comm_semiring R]

lemma add_sq (a b : R) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
by simp only [sq, add_mul_self_eq]

lemma add_sq' (a b : R) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b :=
by rw [add_sq, add_assoc, add_comm _ (b ^ 2), add_assoc]

alias add_sq ← add_pow_two

end comm_semiring

section has_distrib_neg
variables [monoid R] [has_distrib_neg R]

variables (R)
theorem neg_one_pow_eq_or : ∀ n : ℕ, (-1 : R)^n = 1 ∨ (-1 : R)^n = -1
| 0     := or.inl (pow_zero _)
| (n+1) := (neg_one_pow_eq_or n).swap.imp
  (λ h, by rw [pow_succ, h, neg_one_mul, neg_neg])
  (λ h, by rw [pow_succ, h, mul_one])
variables {R}

theorem neg_pow (a : R) (n : ℕ) : (- a) ^ n = (-1) ^ n * a ^ n :=
(neg_one_mul a) ▸ (commute.neg_one_left a).mul_pow n

@[simp] theorem neg_pow_bit0 (a : R) (n : ℕ) : (- a) ^ (bit0 n) = a ^ (bit0 n) :=
by rw [pow_bit0', neg_mul_neg, pow_bit0']

@[simp] theorem neg_pow_bit1 (a : R) (n : ℕ) : (- a) ^ (bit1 n) = - a ^ (bit1 n) :=
by simp only [bit1, pow_succ, neg_pow_bit0, neg_mul_eq_neg_mul]

@[simp] lemma neg_sq (a : R) : (-a) ^ 2 = a ^ 2 := by simp [sq]
@[simp] lemma neg_one_sq : (-1 : R) ^ 2 = 1 := by rw [neg_sq, one_pow]

alias neg_sq ← neg_pow_two
alias neg_one_sq ← neg_one_pow_two

end has_distrib_neg

section ring
variables [ring R] {a b : R}

protected lemma commute.sq_sub_sq (h : commute a b) : a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
by rw [sq, sq, h.mul_self_sub_mul_self_eq]

@[simp]
lemma neg_one_pow_mul_eq_zero_iff {n : ℕ} {r : R} : (-1)^n * r = 0 ↔ r = 0 :=
by rcases neg_one_pow_eq_or R n; simp [h]

@[simp]
lemma mul_neg_one_pow_eq_zero_iff {n : ℕ} {r : R} : r * (-1)^n = 0 ↔ r = 0 :=
by rcases neg_one_pow_eq_or R n; simp [h]

variables [no_zero_divisors R]

protected lemma commute.sq_eq_sq_iff_eq_or_eq_neg (h : commute a b) :
  a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b :=
by rw [←sub_eq_zero, h.sq_sub_sq, mul_eq_zero, add_eq_zero_iff_eq_neg, sub_eq_zero, or_comm]

@[simp] lemma sq_eq_one_iff : a^2 = 1 ↔ a = 1 ∨ a = -1 :=
by rw [←(commute.one_right a).sq_eq_sq_iff_eq_or_eq_neg, one_pow]

lemma sq_ne_one_iff : a^2 ≠ 1 ↔ a ≠ 1 ∧ a ≠ -1 := sq_eq_one_iff.not.trans not_or_distrib

end ring

section comm_ring
variables [comm_ring R]

lemma sq_sub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := (commute.all a b).sq_sub_sq

alias sq_sub_sq ← pow_two_sub_pow_two

lemma sub_sq (a b : R) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 :=
by rw [sub_eq_add_neg, add_sq, neg_sq, mul_neg, ← sub_eq_add_neg]

alias sub_sq ← sub_pow_two

lemma sub_sq' (a b : R) : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b :=
by rw [sub_eq_add_neg, add_sq', neg_sq, mul_neg, ← sub_eq_add_neg]

variables [no_zero_divisors R] {a b : R}

lemma sq_eq_sq_iff_eq_or_eq_neg : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b :=
(commute.all a b).sq_eq_sq_iff_eq_or_eq_neg

lemma eq_or_eq_neg_of_sq_eq_sq (a b : R) : a ^ 2 = b ^ 2 → a = b ∨ a = -b :=
sq_eq_sq_iff_eq_or_eq_neg.1

/- Copies of the above comm_ring lemmas for `units R`. -/
namespace units

protected lemma sq_eq_sq_iff_eq_or_eq_neg {a b : Rˣ} : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b :=
by simp_rw [ext_iff, coe_pow, sq_eq_sq_iff_eq_or_eq_neg, units.coe_neg]

protected lemma eq_or_eq_neg_of_sq_eq_sq (a b : Rˣ) (h : a ^ 2 = b ^ 2) : a = b ∨ a = -b :=
units.sq_eq_sq_iff_eq_or_eq_neg.1 h

end units

end comm_ring
