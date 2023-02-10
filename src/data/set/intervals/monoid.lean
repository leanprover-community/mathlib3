/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot
-/
import data.set.intervals.basic
import data.set.function
import algebra.order.monoid.cancel.defs
import algebra.order.monoid.canonical.defs
import algebra.group.basic

/-!
# Images of intervals under `(+ d)`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The lemmas in this file state that addition maps intervals bijectively. The typeclass
`has_exists_add_of_le` is defined specifically to make them work when combined with
`ordered_cancel_add_comm_monoid`; the lemmas below therefore apply to all
`ordered_add_comm_group`, but also to `ℕ` and `ℝ≥0`, which are not groups.
-/

namespace set

variables {M : Type*} [ordered_cancel_add_comm_monoid M] [has_exists_add_of_le M] (a b c d : M)

lemma Ici_add_bij : bij_on (+d) (Ici a) (Ici (a + d)) :=
begin
  refine ⟨λ x h, add_le_add_right (mem_Ici.mp h) _, (add_left_injective d).inj_on _, λ _ h, _⟩,
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ici.mp h),
  rw [mem_Ici, add_right_comm, add_le_add_iff_right] at h,
  exact ⟨a + c, h, by rw add_right_comm⟩,
end

lemma Ioi_add_bij : bij_on (+d) (Ioi a) (Ioi (a + d)) :=
begin
  refine ⟨λ x h, add_lt_add_right (mem_Ioi.mp h) _, λ _ _ _ _ h, add_right_cancel h, λ _ h, _⟩,
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ioi.mp h).le,
  rw [mem_Ioi, add_right_comm, add_lt_add_iff_right] at h,
  exact ⟨a + c, h, by rw add_right_comm⟩,
end

lemma Icc_add_bij : bij_on (+d) (Icc a b) (Icc (a + d) (b + d)) :=
begin
  rw [← Ici_inter_Iic, ← Ici_inter_Iic],
  exact (Ici_add_bij a d).inter_maps_to (λ x hx, add_le_add_right hx _)
    (λ x hx, le_of_add_le_add_right hx.2)
end

lemma Ioo_add_bij : bij_on (+d) (Ioo a b) (Ioo (a + d) (b + d)) :=
begin
  rw [← Ioi_inter_Iio, ← Ioi_inter_Iio],
  exact (Ioi_add_bij a d).inter_maps_to (λ x hx, add_lt_add_right hx _)
    (λ x hx, lt_of_add_lt_add_right hx.2)
end

lemma Ioc_add_bij : bij_on (+d) (Ioc a b) (Ioc (a + d) (b + d)) :=
begin
  rw [← Ioi_inter_Iic, ← Ioi_inter_Iic],
  exact (Ioi_add_bij a d).inter_maps_to (λ x hx, add_le_add_right hx _)
    (λ x hx, le_of_add_le_add_right hx.2)
end

lemma Ico_add_bij : bij_on (+d) (Ico a b) (Ico (a + d) (b + d)) :=
begin
  rw [← Ici_inter_Iio, ← Ici_inter_Iio],
  exact (Ici_add_bij a d).inter_maps_to (λ x hx, add_lt_add_right hx _)
    (λ x hx, lt_of_add_lt_add_right hx.2)
end

/-!
### Images under `x ↦ x + a`
-/

@[simp] lemma image_add_const_Ici : (λ x, x + a) '' Ici b = Ici (b + a) :=
(Ici_add_bij _ _).image_eq

@[simp] lemma image_add_const_Ioi : (λ x, x + a) '' Ioi b = Ioi (b + a) :=
(Ioi_add_bij _ _).image_eq

@[simp] lemma image_add_const_Icc : (λ x, x + a) '' Icc b c = Icc (b + a) (c + a) :=
(Icc_add_bij _ _ _).image_eq

@[simp] lemma image_add_const_Ico : (λ x, x + a) '' Ico b c = Ico (b + a) (c + a) :=
(Ico_add_bij _ _ _).image_eq

@[simp] lemma image_add_const_Ioc : (λ x, x + a) '' Ioc b c = Ioc (b + a) (c + a) :=
(Ioc_add_bij _ _ _).image_eq

@[simp] lemma image_add_const_Ioo : (λ x, x + a) '' Ioo b c = Ioo (b + a) (c + a) :=
(Ioo_add_bij _ _ _).image_eq

/-!
### Images under `x ↦ a + x`
-/

@[simp] lemma image_const_add_Ici : (λ x, a + x) '' Ici b = Ici (a + b) :=
by simp only [add_comm a, image_add_const_Ici]

@[simp] lemma image_const_add_Ioi : (λ x, a + x) '' Ioi b = Ioi (a + b) :=
by simp only [add_comm a, image_add_const_Ioi]

@[simp] lemma image_const_add_Icc : (λ x, a + x) '' Icc b c = Icc (a + b) (a + c) :=
by simp only [add_comm a, image_add_const_Icc]

@[simp] lemma image_const_add_Ico : (λ x, a + x) '' Ico b c = Ico (a + b) (a + c) :=
by simp only [add_comm a, image_add_const_Ico]

@[simp] lemma image_const_add_Ioc : (λ x, a + x) '' Ioc b c = Ioc (a + b) (a + c) :=
by simp only [add_comm a, image_add_const_Ioc]

@[simp] lemma image_const_add_Ioo : (λ x, a + x) '' Ioo b c = Ioo (a + b) (a + c) :=
by simp only [add_comm a, image_add_const_Ioo]

end set
