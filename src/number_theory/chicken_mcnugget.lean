/-
Copyright (c) 2021 Alex Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Zhao
-/
import data.nat.modeq
import group_theory.submonoid.basic
import group_theory.submonoid.membership

/-!
# Chicken McNugget Theorem

In this file we prove the Chicken McNugget Theorem, first using natural multiplication,
then using additive submonoid closures.

## Theorem Statement:
The Chicken McNugget Theorem states,
for two relatively prime integers larger than 1,
the greatest integer not expressible as a sum of nonnegative multiples of these two
is m * n - m - n.

## Implementation Notes

For the upper bound, we begin with an auxiliary lemma showing m * n is not attainable, then show
m * n - m - n is not attainable. Then for the construction, we create a k_1 which is k mod n and
0 mod m, then show it is at most k. Then k_1 is a multiple of m, and (k-k_1) is a multiple of n,
and we're done.

Afterwards, we rewrite this with add_submonoid.closure and is_greatest.

## Tags

chicken mcnugget, frobenius coin, chinese remainder theorem
-/

open nat

/-- Auxiliary lemma for upper bound. -/
lemma chicken_mcnugget_upper_bound_aux (a b m n : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
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

/-- No solution for the maximal value over the natural numbers. -/
lemma chicken_mcnugget_upper_bound (m n : ℕ) (cop : coprime m n) (hm : 1 < m) (hn : 1 < n) :
  ¬ ∃ (a b : ℕ), a * m + b * n = m * n - m - n :=
begin
  rintro ⟨a, b, h⟩,
  apply chicken_mcnugget_upper_bound_aux _ _ m n (add_one_ne_zero a) (add_one_ne_zero b) cop,
  rw [add_mul, add_mul, one_mul, one_mul, add_assoc, ←add_assoc m, add_comm m, add_assoc,
      ←add_assoc, h, nat.sub_sub, nat.sub_add_cancel (add_le_mul hm hn)],
end

/-- Providing construction. -/
lemma chicken_mcnugget_construction (m n : ℕ) (cop : coprime m n) (hm : 1 < m) (hn : 1 < n) :
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

/-- Combines both sublemmas in a single claim. -/
theorem chicken_mcnugget_split (m n : ℕ) (cop: coprime m n) (hm : 1 < m) (hn: 1 < n) :
  (¬ ∃ a b, a * m + b * n = m * n - m - n) ∧ ∀ k, m * n - m - n < k → ∃ a b, a * m + b * n = k :=
⟨chicken_mcnugget_upper_bound m n cop hm hn, chicken_mcnugget_construction m n cop hm hn⟩

/-- Rewrites the above with is_greatest. -/
theorem chicken_mcnugget (m n : ℕ) (cop: coprime m n) (hm : 1 < m) (hn: 1 < n) :
  is_greatest {k | ∀ a b, a * m + b * n ≠ k} (m * n - m - n) :=
let h := chicken_mcnugget_split m n cop hm hn in
  ⟨λ a b H, h.1 ⟨a, b, H⟩, λ k hk, not_lt.mp (mt (h.2 k) (λ ⟨a, b, H⟩, hk a b H))⟩

/-- Restates the original theorem with add_submonoid.closure. -/
lemma chicken_mcnugget_add_submonoid_split (m n : ℕ) (cop: coprime m n) (hm: 1 < m) (hn: 1 < n) :
  m * n - m - n ∉ add_submonoid.closure ({m, n} : set ℕ) ∧
  ∀ k, m * n - m - n < k → k ∈ add_submonoid.closure ({m, n} : set ℕ) :=
begin
  simp_rw add_submonoid.mem_closure_pair,
  exact chicken_mcnugget_split m n cop hm hn,
end

/-- Rewrites the above with is_greatest. -/
theorem chicken_mcnugget_add_submonoid (m n : ℕ) (cop: coprime m n) (hm: 1 < m) (hn: 1 < n) :
  is_greatest {k | k ∉ add_submonoid.closure ({m, n} : set ℕ)} (m * n - m - n) :=
let h := chicken_mcnugget_add_submonoid_split m n cop hm hn in ⟨h.1, λ k, not_lt.mp ∘ mt (h.2 k)⟩
