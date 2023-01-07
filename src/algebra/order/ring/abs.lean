/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/

import algebra.order.ring.defs
import algebra.ring.divisibility
import algebra.order.group.abs

/-!
# Absolute values in linear ordered rings.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*}

section linear_ordered_ring
variables [linear_ordered_ring α] {a b c : α}

@[simp] lemma abs_one : |(1 : α)| = 1 := abs_of_pos zero_lt_one
@[simp] lemma abs_two : |(2 : α)| = 2 := abs_of_pos zero_lt_two

lemma abs_mul (a b : α) : |a * b| = |a| * |b| :=
begin
  rw [abs_eq (mul_nonneg (abs_nonneg a) (abs_nonneg b))],
  cases le_total a 0 with ha ha; cases le_total b 0 with hb hb;
    simp only [abs_of_nonpos, abs_of_nonneg, true_or, or_true, eq_self_iff_true,
      neg_mul, mul_neg, neg_neg, *]
end

/-- `abs` as a `monoid_with_zero_hom`. -/
def abs_hom : α →*₀ α := ⟨abs, abs_zero, abs_one, abs_mul⟩

@[simp] lemma abs_mul_abs_self (a : α) : |a| * |a| = a * a :=
abs_by_cases (λ x, x * x = a * a) rfl (neg_mul_neg a a)

@[simp] lemma abs_mul_self (a : α) : |a * a| = a * a :=
by rw [abs_mul, abs_mul_abs_self]

@[simp] lemma abs_eq_self : |a| = a ↔ 0 ≤ a := by simp [abs_eq_max_neg]

@[simp] lemma abs_eq_neg_self : |a| = -a ↔ a ≤ 0 := by simp [abs_eq_max_neg]

/-- For an element `a` of a linear ordered ring, either `abs a = a` and `0 ≤ a`,
    or `abs a = -a` and `a < 0`.
    Use cases on this lemma to automate linarith in inequalities -/
lemma abs_cases (a : α) : (|a| = a ∧ 0 ≤ a) ∨ (|a| = -a ∧ a < 0) :=
begin
  by_cases 0 ≤ a,
  { left,
    exact ⟨abs_eq_self.mpr h, h⟩ },
  { right,
    push_neg at h,
    exact ⟨abs_eq_neg_self.mpr (le_of_lt h), h⟩ }
end

@[simp] lemma max_zero_add_max_neg_zero_eq_abs_self (a : α) :
  max a 0 + max (-a) 0 = |a| :=
begin
  symmetry,
  rcases le_total 0 a with ha|ha;
  simp [ha],
end

lemma abs_eq_iff_mul_self_eq : |a| = |b| ↔ a * a = b * b :=
begin
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b],
  exact (mul_self_inj (abs_nonneg a) (abs_nonneg b)).symm,
end

lemma abs_lt_iff_mul_self_lt : |a| < |b| ↔ a * a < b * b :=
begin
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b],
  exact mul_self_lt_mul_self_iff (abs_nonneg a) (abs_nonneg b)
end

lemma abs_le_iff_mul_self_le : |a| ≤ |b| ↔ a * a ≤ b * b :=
begin
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b],
  exact mul_self_le_mul_self_iff (abs_nonneg a) (abs_nonneg b)
end

lemma abs_le_one_iff_mul_self_le_one : |a| ≤ 1 ↔ a * a ≤ 1 :=
by simpa only [abs_one, one_mul] using @abs_le_iff_mul_self_le α _ a 1

end linear_ordered_ring

section linear_ordered_comm_ring

variables [linear_ordered_comm_ring α] {a b c d : α}

lemma abs_sub_sq (a b : α) : |a - b| * |a - b| = a * a + b * b - (1 + 1) * a * b :=
begin
  rw abs_mul_abs_self,
  simp only [mul_add, add_comm, add_left_comm, mul_comm, sub_eq_add_neg,
    mul_one, mul_neg, neg_add_rev, neg_neg],
end

end linear_ordered_comm_ring

section
variables [ring α] [linear_order α] {a b : α}

@[simp] lemma abs_dvd (a b : α) : |a| ∣ b ↔ a ∣ b :=
by { cases abs_choice a with h h; simp only [h, neg_dvd] }

lemma abs_dvd_self (a : α) : |a| ∣ a :=
(abs_dvd a a).mpr (dvd_refl a)

@[simp] lemma dvd_abs (a b : α) : a ∣ |b| ↔ a ∣ b :=
by { cases abs_choice b with h h; simp only [h, dvd_neg] }

lemma self_dvd_abs (a : α) : a ∣ |a| :=
(dvd_abs a a).mpr (dvd_refl a)

lemma abs_dvd_abs (a b : α) : |a| ∣ |b| ↔ a ∣ b :=
(abs_dvd _ _).trans (dvd_abs _ _)

end
