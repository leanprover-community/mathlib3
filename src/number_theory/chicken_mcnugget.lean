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

In this file we prove the Chicken McNugget Theorem.

## Theorem Statement:
The Chicken McNugget Theorem states,
for two relatively prime integers larger than 1,
the largest integer not expressible as a sum of nonnegative multiples of these two
is m * n - m - n.

## Implementation Notes

For the upper bound, we begin with an auxiliary lemma showing m * n is not attainable, then show
m * n - m - n is not attainable. Then for the construction, we create a k_1 which is k mod n and
0 mod m, then show it is at most k. Then k_1 is a multiple of m, and (k-k_1) is a multiple of n,
and we're done.

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

/-- This theorem combines both sublemmas in a single claim. -/
theorem chicken_mcnugget (m n : ℕ) (hm : 1 < m) (hn: 1 < n) (cop: coprime m n) :
  (¬ ∃ a b, a * m + b * n = m * n - m - n) ∧ ∀ k, m * n - m - n < k → ∃ a b, a * m + b * n = k :=
⟨chicken_mcnugget_upper_bound m n cop hm hn, chicken_mcnugget_construction m n cop hm hn⟩

lemma singleton_lemma (m k : ℕ): m ∈ add_submonoid.closure({k} : set ℕ) ↔
  (∃ (n : ℕ), n * k = m) :=
by {apply @add_submonoid.mem_closure_singleton _ _ k m, }

lemma singleton_lemma_cor (m n : ℕ): m * n ∈ add_submonoid.closure({n} : set ℕ) :=
begin
  apply (singleton_lemma (m * n) n).2,
  use m,
end

lemma mult_add_subm_clos (m n k: ℕ):
  (∃ a b, a * m + b * n = k) ↔ k ∈ add_submonoid.closure(({m, n} : set ℕ)) :=
begin
  rw [←set.singleton_union, add_submonoid.closure_union],
  refine ⟨_, λ h, _⟩,
  rintros ⟨a, b, rfl⟩,
  exact add_submonoid.mem_sup.mpr ⟨a * m, add_submonoid.mem_closure_singleton.mpr ⟨a, rfl⟩,
    b * n, add_submonoid.mem_closure_singleton.mpr ⟨b, rfl⟩, rfl⟩,
  obtain ⟨a, ha, b, hb, rfl⟩ := add_submonoid.mem_sup.mp h,
  rw [add_submonoid.mem_closure_singleton] at ha hb,
  obtain ⟨a, rfl⟩ := ha,
  obtain ⟨b, rfl⟩ := hb,
  exact ⟨a, b, rfl⟩,
end

theorem chicken_mcnugget_addsubm_clos (m n : ℕ) (hm: 1 < m) (hn: 1 < n) (cop: coprime m n) :
  m * n - m - n ∉ add_submonoid.closure ({m, n} : set ℕ) ∧
  ∀ k, m * n - m - n < k → k ∈ add_submonoid.closure ({m, n} : set ℕ) :=
begin
  simp_rw ← mult_add_subm_clos,
  exact chicken_mcnugget m n hm hn cop,
end
