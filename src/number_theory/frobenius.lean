/-
Copyright (c) 2021 Alex Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Zhao
-/
import data.nat.modeq
import group_theory.submonoid.basic
import group_theory.submonoid.membership

/-!
# Frobenius Number in Two Variables

In this file we first define a predicate for Frobenius numbers, then solve the 2-variable variant
of this problem.

## Theorem Statement

Given a finite set of relatively prime integers all greater than 1, their Frobenius number is the
largest positive integer that cannot be expressed as a sum of nonnegative multiples of these
integers. Here we show the Frobenius number of two relatively prime integers `m` and `n` greater
than 1 is `m * n - m - n`. This result is also known as the Chicken McNugget Theorem.

## Implementation Notes

First we define Frobenius numbers in general using `is_greatest` and `add_submonoid.closure`. Then
we proceed to compute the Frobenius number of `m` and `n`.

For the upper bound, we begin with an auxiliary lemma showing `m * n` is not attainable, then show
`m * n - m - n` is not attainable. Then for the construction, we create a `k_1` which is `k mod n`
and `0 mod m`, then show it is at most `k`. Then `k_1` is a multiple of `m`, so `(k-k_1)`
is a multiple of n, and we're done.

## Tags

frobenius number, chicken mcnugget, chinese remainder theorem, add_submonoid.closure
-/

namespace nat

variables {m n : ℕ}

def is_frobenius (n : ℕ) (s : set ℕ) : Prop :=
  is_greatest {k | k ∉ add_submonoid.closure (s)} n

/- No solution for the product over the natural numbers. -/
lemma mul_add_mul_ne_mul_of_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
  (cop : coprime m n) : a * m + b * n ≠ m * n :=
begin
  intro h,
  obtain ⟨x, rfl⟩ := cop.symm.dvd_of_dvd_mul_right ((nat.dvd_add_iff_left (dvd_mul_left n b)).mpr
    ((congr_arg _ h).mpr (dvd_mul_left n m))),
  obtain ⟨y, rfl⟩ := cop.dvd_of_dvd_mul_right ((nat.dvd_add_iff_right (dvd_mul_left m (n * x))).mpr
      ((congr_arg _ h).mpr (dvd_mul_right m n))),
  rw [mul_comm n x, mul_comm m y, mul_assoc, mul_assoc, mul_comm n m, ←add_mul] at h,
  rw [mul_comm, mul_ne_zero_iff, ←one_le_iff_ne_zero] at ha hb,
  exact mul_ne_zero hb.2 ha.2 (eq_zero_of_mul_eq_self_left (ne_of_gt (add_le_add ha.1 hb.1)) h),
end

/- No solution for the maximal value over the natural numbers. -/
lemma mul_add_mul_ne_max_val (cop : coprime m n) (hm : 1 < m) (hn : 1 < n)
  (a b : ℕ) :
  a * m + b * n ≠ m * n - m - n :=
begin
  intro h,
  apply mul_add_mul_ne_mul_of_coprime (add_one_ne_zero a) (add_one_ne_zero b) cop,
  rw [add_mul, add_mul, one_mul, one_mul, add_assoc, ←add_assoc m, add_comm m, add_assoc,
      ←add_assoc, h, nat.sub_sub, nat.sub_add_cancel (add_le_mul hm hn)],
end

/- Providing construction for all larger values. -/
lemma not_in_clos_nat_pair (cop : coprime m n) (hm : 1 < m) (hn : 1 < n) :
  ∀ k, m * n - m - n < k → ∃ (a b : ℕ), a * m + b * n = k :=
begin
  intros k hk,
  let x := chinese_remainder cop 0 k,
  have key := modeq.le_of_lt_add x.2.2 (calc x.1 ≤ m * n - m : modeq.le_of_lt_add (x.2.1.trans
    (modeq_zero_iff_dvd.mpr (nat.dvd_sub' (dvd_mul_right m n) dvd_rfl)).symm) (lt_of_lt_of_le
    (chinese_remainder_lt_mul cop 0 k (pos_of_gt hm).ne' (pos_of_gt hn).ne') le_tsub_add)
  ... = m * n - m - n + n : (nat.sub_add_cancel (le_tsub_of_add_le_left (add_le_mul hm hn))).symm
  ... < k + n : add_lt_add_right hk n),
  obtain ⟨a, ha⟩ := modeq_zero_iff_dvd.mp x.2.1,
  obtain ⟨b, hb⟩ := (modeq_iff_dvd' key).mp x.2.2,
  exact ⟨a, b, by rw [mul_comm, ←ha, mul_comm, ←hb, nat.add_sub_of_le key]⟩,
end

/-- The **Chicken Mcnugget theorem** stated using `is_greatest`. -/
theorem max_not_sum_mult (cop: coprime m n) (hm : 1 < m) (hn : 1 < n) :
  is_greatest {k | ∀ a b, a * m + b * n ≠ k} (m * n - m - n) :=
⟨mul_add_mul_ne_max_val cop hm hn,
  λ k hk, not_lt.mp (mt (not_in_clos_nat_pair cop hm hn k) (λ ⟨a, b, H⟩, hk a b H))⟩

/-- The **Chicken Mcnugget theorem** stated using `is_frobenius`. -/
theorem max_not_in_clos_nat_pair_eq (cop : coprime m n) (hm : 1 < m) (hn : 1 < n) :
  is_frobenius (m * n - m - n) {m, n} :=
begin
  rw is_frobenius,
  simp_rw add_submonoid.mem_closure_pair,
  push_neg,
  exact max_not_sum_mult cop hm hn,
end

end nat
