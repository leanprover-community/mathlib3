/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import algebra.order.ring.defs
import algebra.invertible

/-!
# Lemmas about `inv_of` in ordered (semi)rings.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*} [linear_ordered_semiring α] {a : α}

@[simp] lemma inv_of_pos [invertible a] : 0 < ⅟a ↔ 0 < a :=
begin
  have : 0 < a * ⅟a, by simp only [mul_inv_of_self, zero_lt_one],
  exact ⟨λ h, pos_of_mul_pos_left this h.le, λ h, pos_of_mul_pos_right this h.le⟩
end

@[simp] lemma inv_of_nonpos [invertible a] : ⅟a ≤ 0 ↔ a ≤ 0 :=
by simp only [← not_lt, inv_of_pos]

@[simp] lemma inv_of_nonneg [invertible a] : 0 ≤ ⅟a ↔ 0 ≤ a :=
begin
  have : 0 < a * ⅟a, by simp only [mul_inv_of_self, zero_lt_one],
  exact ⟨λ h, (pos_of_mul_pos_left this h).le, λ h, (pos_of_mul_pos_right this h).le⟩
end

@[simp] lemma inv_of_lt_zero [invertible a] : ⅟a < 0 ↔ a < 0 :=
by simp only [← not_le, inv_of_nonneg]

@[simp] lemma inv_of_le_one [invertible a] (h : 1 ≤ a) : ⅟a ≤ 1 :=
by haveI := @linear_order.decidable_le α _; exact
mul_inv_of_self a ▸ le_mul_of_one_le_left (inv_of_nonneg.2 $ zero_le_one.trans h) h
