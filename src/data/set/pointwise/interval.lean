/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot
-/
import data.set.intervals.unordered_interval
import data.set.intervals.monoid
import data.set.pointwise.basic
import algebra.order.field.basic
import algebra.order.group.min_max

/-!
# (Pre)images of intervals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove a bunch of trivial lemmas like “if we add `a` to all points of `[b, c]`,
then we get `[a + b, a + c]`”. For the functions `x ↦ x ± a`, `x ↦ a ± x`, and `x ↦ -x` we prove
lemmas about preimages and images of all intervals. We also prove a few lemmas about images under
`x ↦ a * x`, `x ↦ x * a` and `x ↦ x⁻¹`.
-/

open_locale interval pointwise

variables {α : Type*}

namespace set

section ordered_add_comm_group
variables [ordered_add_comm_group α] (a b c : α)

/-!
### Preimages under `x ↦ a + x`
-/

@[simp] lemma preimage_const_add_Ici : (λ x, a + x) ⁻¹' (Ici b) = Ici (b - a) :=
ext $ λ x, sub_le_iff_le_add'.symm

@[simp] lemma preimage_const_add_Ioi : (λ x, a + x) ⁻¹' (Ioi b) = Ioi (b - a) :=
ext $ λ x, sub_lt_iff_lt_add'.symm

@[simp] lemma preimage_const_add_Iic : (λ x, a + x) ⁻¹' (Iic b) = Iic (b - a) :=
ext $ λ x, le_sub_iff_add_le'.symm

@[simp] lemma preimage_const_add_Iio : (λ x, a + x) ⁻¹' (Iio b) = Iio (b - a) :=
ext $ λ x, lt_sub_iff_add_lt'.symm

@[simp] lemma preimage_const_add_Icc : (λ x, a + x) ⁻¹' (Icc b c) = Icc (b - a) (c - a) :=
by simp [← Ici_inter_Iic]

@[simp] lemma preimage_const_add_Ico : (λ x, a + x) ⁻¹' (Ico b c) = Ico (b - a) (c - a) :=
by simp [← Ici_inter_Iio]

@[simp] lemma preimage_const_add_Ioc : (λ x, a + x) ⁻¹' (Ioc b c) = Ioc (b - a) (c - a) :=
by simp [← Ioi_inter_Iic]

@[simp] lemma preimage_const_add_Ioo : (λ x, a + x) ⁻¹' (Ioo b c) = Ioo (b - a) (c - a) :=
by simp [← Ioi_inter_Iio]

/-!
### Preimages under `x ↦ x + a`
-/

@[simp] lemma preimage_add_const_Ici : (λ x, x + a) ⁻¹' (Ici b) = Ici (b - a) :=
ext $ λ x, sub_le_iff_le_add.symm

@[simp] lemma preimage_add_const_Ioi : (λ x, x + a) ⁻¹' (Ioi b) = Ioi (b - a) :=
ext $ λ x, sub_lt_iff_lt_add.symm

@[simp] lemma preimage_add_const_Iic : (λ x, x + a) ⁻¹' (Iic b) = Iic (b - a) :=
ext $ λ x, le_sub_iff_add_le.symm

@[simp] lemma preimage_add_const_Iio : (λ x, x + a) ⁻¹' (Iio b) = Iio (b - a) :=
ext $ λ x, lt_sub_iff_add_lt.symm

@[simp] lemma preimage_add_const_Icc : (λ x, x + a) ⁻¹' (Icc b c) = Icc (b - a) (c - a) :=
by simp [← Ici_inter_Iic]

@[simp] lemma preimage_add_const_Ico : (λ x, x + a) ⁻¹' (Ico b c) = Ico (b - a) (c - a) :=
by simp [← Ici_inter_Iio]

@[simp] lemma preimage_add_const_Ioc : (λ x, x + a) ⁻¹' (Ioc b c) = Ioc (b - a) (c - a) :=
by simp [← Ioi_inter_Iic]

@[simp] lemma preimage_add_const_Ioo : (λ x, x + a) ⁻¹' (Ioo b c) = Ioo (b - a) (c - a) :=
by simp [← Ioi_inter_Iio]

/-!
### Preimages under `x ↦ -x`
-/

@[simp] lemma preimage_neg_Ici : - Ici a = Iic (-a) := ext $ λ x, le_neg
@[simp] lemma preimage_neg_Iic : - Iic a = Ici (-a) := ext $ λ x, neg_le
@[simp] lemma preimage_neg_Ioi : - Ioi a = Iio (-a) := ext $ λ x, lt_neg
@[simp] lemma preimage_neg_Iio : - Iio a = Ioi (-a) := ext $ λ x, neg_lt

@[simp] lemma preimage_neg_Icc : - Icc a b = Icc (-b) (-a) :=
by simp [← Ici_inter_Iic, inter_comm]

@[simp] lemma preimage_neg_Ico : - Ico a b = Ioc (-b) (-a) :=
by simp [← Ici_inter_Iio, ← Ioi_inter_Iic, inter_comm]

@[simp] lemma preimage_neg_Ioc : - Ioc a b = Ico (-b) (-a) :=
by simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[simp] lemma preimage_neg_Ioo : - Ioo a b = Ioo (-b) (-a) :=
by simp [← Ioi_inter_Iio, inter_comm]

/-!
### Preimages under `x ↦ x - a`
-/

@[simp] lemma preimage_sub_const_Ici : (λ x, x - a) ⁻¹' (Ici b) = Ici (b + a) :=
by simp [sub_eq_add_neg]

@[simp] lemma preimage_sub_const_Ioi : (λ x, x - a) ⁻¹' (Ioi b) = Ioi (b + a) :=
by simp [sub_eq_add_neg]

@[simp] lemma preimage_sub_const_Iic : (λ x, x - a) ⁻¹' (Iic b) = Iic (b + a) :=
by simp [sub_eq_add_neg]

@[simp] lemma preimage_sub_const_Iio : (λ x, x - a) ⁻¹' (Iio b) = Iio (b + a) :=
by simp [sub_eq_add_neg]

@[simp] lemma preimage_sub_const_Icc : (λ x, x - a) ⁻¹' (Icc b c) = Icc (b + a) (c + a) :=
by simp [sub_eq_add_neg]

@[simp] lemma preimage_sub_const_Ico : (λ x, x - a) ⁻¹' (Ico b c) = Ico (b + a) (c + a) :=
by simp [sub_eq_add_neg]

@[simp] lemma preimage_sub_const_Ioc : (λ x, x - a) ⁻¹' (Ioc b c) = Ioc (b + a) (c + a) :=
by simp [sub_eq_add_neg]

@[simp] lemma preimage_sub_const_Ioo : (λ x, x - a) ⁻¹' (Ioo b c) = Ioo (b + a) (c + a) :=
by simp [sub_eq_add_neg]

/-!
### Preimages under `x ↦ a - x`
-/

@[simp] lemma preimage_const_sub_Ici : (λ x, a - x) ⁻¹' (Ici b) = Iic (a - b) :=
ext $ λ x, le_sub_comm

@[simp] lemma preimage_const_sub_Iic : (λ x, a - x) ⁻¹' (Iic b) = Ici (a - b) :=
ext $ λ x, sub_le_comm

@[simp] lemma preimage_const_sub_Ioi : (λ x, a - x) ⁻¹' (Ioi b) = Iio (a - b) :=
ext $ λ x, lt_sub_comm

@[simp] lemma preimage_const_sub_Iio : (λ x, a - x) ⁻¹' (Iio b) = Ioi (a - b) :=
ext $ λ x, sub_lt_comm

@[simp] lemma preimage_const_sub_Icc : (λ x, a - x) ⁻¹' (Icc b c) = Icc (a - c) (a - b) :=
by simp [← Ici_inter_Iic, inter_comm]

@[simp] lemma preimage_const_sub_Ico : (λ x, a - x) ⁻¹' (Ico b c) = Ioc (a - c) (a - b) :=
by simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[simp] lemma preimage_const_sub_Ioc : (λ x, a - x) ⁻¹' (Ioc b c) = Ico (a - c) (a - b) :=
by simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[simp] lemma preimage_const_sub_Ioo : (λ x, a - x) ⁻¹' (Ioo b c) = Ioo (a - c) (a - b) :=
by simp [← Ioi_inter_Iio, inter_comm]

/-!
### Images under `x ↦ a + x`
-/

@[simp] lemma image_const_add_Iic : (λ x, a + x) '' Iic b = Iic (a + b) :=
by simp [add_comm]

@[simp] lemma image_const_add_Iio : (λ x, a + x) '' Iio b = Iio (a + b) :=
by simp [add_comm]

/-!
### Images under `x ↦ x + a`
-/

@[simp] lemma image_add_const_Iic : (λ x, x + a) '' Iic b = Iic (b + a) := by simp
@[simp] lemma image_add_const_Iio : (λ x, x + a) '' Iio b = Iio (b + a) := by simp

/-!
### Images under `x ↦ -x`
-/

lemma image_neg_Ici : has_neg.neg '' (Ici a) = Iic (-a) := by simp
lemma image_neg_Iic : has_neg.neg '' (Iic a) = Ici (-a) := by simp
lemma image_neg_Ioi : has_neg.neg '' (Ioi a) = Iio (-a) := by simp
lemma image_neg_Iio : has_neg.neg '' (Iio a) = Ioi (-a) := by simp
lemma image_neg_Icc : has_neg.neg '' (Icc a b) = Icc (-b) (-a) := by simp
lemma image_neg_Ico : has_neg.neg '' (Ico a b) = Ioc (-b) (-a) := by simp
lemma image_neg_Ioc : has_neg.neg '' (Ioc a b) = Ico (-b) (-a) := by simp
lemma image_neg_Ioo : has_neg.neg '' (Ioo a b) = Ioo (-b) (-a) := by simp

/-!
### Images under `x ↦ a - x`
-/

@[simp] lemma image_const_sub_Ici : (λ x, a - x) '' Ici b = Iic (a - b) :=
by simp [sub_eq_add_neg, image_comp (λ x, a + x) (λ x, -x)]

@[simp] lemma image_const_sub_Iic : (λ x, a - x) '' Iic b = Ici (a - b) :=
by simp [sub_eq_add_neg, image_comp (λ x, a + x) (λ x, -x), add_comm]

@[simp] lemma image_const_sub_Ioi : (λ x, a - x) '' Ioi b = Iio (a - b) :=
by simp [sub_eq_add_neg, image_comp (λ x, a + x) (λ x, -x)]

@[simp] lemma image_const_sub_Iio : (λ x, a - x) '' Iio b = Ioi (a - b) :=
by simp [sub_eq_add_neg, image_comp (λ x, a + x) (λ x, -x), add_comm]

@[simp] lemma image_const_sub_Icc : (λ x, a - x) '' Icc b c = Icc (a - c) (a - b) :=
by simp [sub_eq_add_neg, image_comp (λ x, a + x) (λ x, -x), add_comm]

@[simp] lemma image_const_sub_Ico : (λ x, a - x) '' Ico b c = Ioc (a - c) (a - b) :=
by simp [sub_eq_add_neg, image_comp (λ x, a + x) (λ x, -x), add_comm]

@[simp] lemma image_const_sub_Ioc : (λ x, a - x) '' Ioc b c = Ico (a - c) (a - b) :=
by simp [sub_eq_add_neg, image_comp (λ x, a + x) (λ x, -x), add_comm]

@[simp] lemma image_const_sub_Ioo : (λ x, a - x) '' Ioo b c = Ioo (a - c) (a - b) :=
by simp [sub_eq_add_neg, image_comp (λ x, a + x) (λ x, -x), add_comm]

/-!
### Images under `x ↦ x - a`
-/

@[simp] lemma image_sub_const_Ici : (λ x, x - a) '' Ici b = Ici (b - a) := by simp [sub_eq_neg_add]
@[simp] lemma image_sub_const_Iic : (λ x, x - a) '' Iic b = Iic (b - a) := by simp [sub_eq_neg_add]
@[simp] lemma image_sub_const_Ioi : (λ x, x - a) '' Ioi b = Ioi (b - a) := by simp [sub_eq_neg_add]
@[simp] lemma image_sub_const_Iio : (λ x, x - a) '' Iio b = Iio (b - a) := by simp [sub_eq_neg_add]

@[simp] lemma image_sub_const_Icc : (λ x, x - a) '' Icc b c = Icc (b - a) (c - a) :=
by simp [sub_eq_neg_add]

@[simp] lemma image_sub_const_Ico : (λ x, x - a) '' Ico b c = Ico (b - a) (c - a) :=
by simp [sub_eq_neg_add]

@[simp] lemma image_sub_const_Ioc : (λ x, x - a) '' Ioc b c = Ioc (b - a) (c - a) :=
by simp [sub_eq_neg_add]

@[simp] lemma image_sub_const_Ioo : (λ x, x - a) '' Ioo b c = Ioo (b - a) (c - a) :=
by simp [sub_eq_neg_add]

/-!
### Bijections
-/

lemma Iic_add_bij : bij_on (+a) (Iic b) (Iic (b + a)) :=
image_add_const_Iic a b ▸ ((add_left_injective _).inj_on _).bij_on_image

lemma Iio_add_bij : bij_on (+a) (Iio b) (Iio (b + a)) :=
image_add_const_Iio a b ▸ ((add_left_injective _).inj_on _).bij_on_image

end ordered_add_comm_group

section linear_ordered_add_comm_group
variables [linear_ordered_add_comm_group α] (a b c d : α)

@[simp] lemma preimage_const_add_uIcc : (λ x, a + x) ⁻¹' [b, c] = [b - a, c - a] :=
by simp only [←Icc_min_max, preimage_const_add_Icc, min_sub_sub_right, max_sub_sub_right]

@[simp] lemma preimage_add_const_uIcc : (λ x, x + a) ⁻¹' [b, c] = [b - a, c - a] :=
by simpa only [add_comm] using preimage_const_add_uIcc a b c

@[simp] lemma preimage_neg_uIcc : - [a, b] = [-a, -b] :=
by simp only [←Icc_min_max, preimage_neg_Icc, min_neg_neg, max_neg_neg]

@[simp] lemma preimage_sub_const_uIcc : (λ x, x - a) ⁻¹' [b, c] = [b + a, c + a] :=
by simp [sub_eq_add_neg]

@[simp] lemma preimage_const_sub_uIcc : (λ x, a - x) ⁻¹' [b, c] = [a - b, a - c] :=
by { simp_rw [←Icc_min_max, preimage_const_sub_Icc],
  simp only [sub_eq_add_neg, min_add_add_left, max_add_add_left, min_neg_neg, max_neg_neg], }

@[simp] lemma image_const_add_uIcc : (λ x, a + x) '' [b, c] = [a + b, a + c] :=
by simp [add_comm]

@[simp] lemma image_add_const_uIcc : (λ x, x + a) '' [b, c] = [b + a, c + a] :=
by simp

@[simp] lemma image_const_sub_uIcc : (λ x, a - x) '' [b, c] = [a - b, a - c] :=
by simp [sub_eq_add_neg, image_comp (λ x, a + x) (λ x, -x)]

@[simp] lemma image_sub_const_uIcc : (λ x, x - a) '' [b, c] = [b - a, c - a] :=
by simp [sub_eq_add_neg, add_comm]

lemma image_neg_uIcc : has_neg.neg '' [a, b] = [-a, -b] := by simp

variables {a b c d}

/-- If `[c, d]` is a subinterval of `[a, b]`, then the distance between `c` and `d` is less than or
equal to that of `a` and `b` -/
lemma abs_sub_le_of_uIcc_subset_uIcc (h : [c, d] ⊆ [a, b]) : |d - c| ≤ |b - a| :=
begin
  rw [← max_sub_min_eq_abs, ← max_sub_min_eq_abs],
  rw [uIcc_subset_uIcc_iff_le] at h,
  exact sub_le_sub h.2 h.1,
end

/-- If `c ∈ [a, b]`, then the distance between `a` and `c` is less than or equal to
that of `a` and `b`  -/
lemma abs_sub_left_of_mem_uIcc (h : c ∈ [a, b]) : |c - a| ≤ |b - a| :=
abs_sub_le_of_uIcc_subset_uIcc $ uIcc_subset_uIcc_left h

/-- If `x ∈ [a, b]`, then the distance between `c` and `b` is less than or equal to
that of `a` and `b`  -/
lemma abs_sub_right_of_mem_uIcc (h : c ∈ [a, b]) : |b - c| ≤ |b - a| :=
abs_sub_le_of_uIcc_subset_uIcc $ uIcc_subset_uIcc_right h

end linear_ordered_add_comm_group

/-!
### Multiplication and inverse in a field
-/

section linear_ordered_field
variables [linear_ordered_field α] {a : α}

@[simp] lemma preimage_mul_const_Iio (a : α) {c : α} (h : 0 < c) :
  (λ x, x * c) ⁻¹' (Iio a) = Iio (a / c) :=
ext $ λ x, (lt_div_iff h).symm

@[simp] lemma preimage_mul_const_Ioi (a : α) {c : α} (h : 0 < c) :
  (λ x, x * c) ⁻¹' (Ioi a) = Ioi (a / c) :=
ext $ λ x, (div_lt_iff h).symm

@[simp] lemma preimage_mul_const_Iic (a : α) {c : α} (h : 0 < c) :
  (λ x, x * c) ⁻¹' (Iic a) = Iic (a / c) :=
ext $ λ x, (le_div_iff h).symm

@[simp] lemma preimage_mul_const_Ici (a : α) {c : α} (h : 0 < c) :
  (λ x, x * c) ⁻¹' (Ici a) = Ici (a / c) :=
ext $ λ x, (div_le_iff h).symm

@[simp] lemma preimage_mul_const_Ioo (a b : α) {c : α} (h : 0 < c) :
  (λ x, x * c) ⁻¹' (Ioo a b) = Ioo (a / c) (b / c) :=
by simp [← Ioi_inter_Iio, h]

@[simp] lemma preimage_mul_const_Ioc (a b : α) {c : α} (h : 0 < c) :
  (λ x, x * c) ⁻¹' (Ioc a b) = Ioc (a / c) (b / c) :=
by simp [← Ioi_inter_Iic, h]

@[simp] lemma preimage_mul_const_Ico (a b : α) {c : α} (h : 0 < c) :
  (λ x, x * c) ⁻¹' (Ico a b) = Ico (a / c) (b / c) :=
by simp [← Ici_inter_Iio, h]

@[simp] lemma preimage_mul_const_Icc (a b : α) {c : α} (h : 0 < c) :
  (λ x, x * c) ⁻¹' (Icc a b) = Icc (a / c) (b / c) :=
by simp [← Ici_inter_Iic, h]

@[simp] lemma preimage_mul_const_Iio_of_neg (a : α) {c : α} (h : c < 0) :
  (λ x, x * c) ⁻¹' (Iio a) = Ioi (a / c) :=
ext $ λ x, (div_lt_iff_of_neg h).symm

@[simp] lemma preimage_mul_const_Ioi_of_neg (a : α) {c : α} (h : c < 0) :
  (λ x, x * c) ⁻¹' (Ioi a) = Iio (a / c) :=
ext $ λ x, (lt_div_iff_of_neg h).symm

@[simp] lemma preimage_mul_const_Iic_of_neg (a : α) {c : α} (h : c < 0) :
  (λ x, x * c) ⁻¹' (Iic a) = Ici (a / c) :=
ext $ λ x, (div_le_iff_of_neg h).symm

@[simp] lemma preimage_mul_const_Ici_of_neg (a : α) {c : α} (h : c < 0) :
  (λ x, x * c) ⁻¹' (Ici a) = Iic (a / c) :=
ext $ λ x, (le_div_iff_of_neg h).symm

@[simp] lemma preimage_mul_const_Ioo_of_neg (a b : α) {c : α} (h : c < 0) :
  (λ x, x * c) ⁻¹' (Ioo a b) = Ioo (b / c) (a / c) :=
by simp [← Ioi_inter_Iio, h, inter_comm]

@[simp] lemma preimage_mul_const_Ioc_of_neg (a b : α) {c : α} (h : c < 0) :
  (λ x, x * c) ⁻¹' (Ioc a b) = Ico (b / c) (a / c) :=
by simp [← Ioi_inter_Iic, ← Ici_inter_Iio, h, inter_comm]

@[simp] lemma preimage_mul_const_Ico_of_neg (a b : α) {c : α} (h : c < 0) :
  (λ x, x * c) ⁻¹' (Ico a b) = Ioc (b / c) (a / c) :=
by simp [← Ici_inter_Iio, ← Ioi_inter_Iic, h, inter_comm]

@[simp] lemma preimage_mul_const_Icc_of_neg (a b : α) {c : α} (h : c < 0) :
  (λ x, x * c) ⁻¹' (Icc a b) = Icc (b / c) (a / c) :=
by simp [← Ici_inter_Iic, h, inter_comm]

@[simp] lemma preimage_const_mul_Iio (a : α) {c : α} (h : 0 < c) :
  ((*) c) ⁻¹' (Iio a) = Iio (a / c) :=
ext $ λ x, (lt_div_iff' h).symm

@[simp] lemma preimage_const_mul_Ioi (a : α) {c : α} (h : 0 < c) :
  ((*) c) ⁻¹' (Ioi a) = Ioi (a / c) :=
ext $ λ x, (div_lt_iff' h).symm

@[simp] lemma preimage_const_mul_Iic (a : α) {c : α} (h : 0 < c) :
  ((*) c) ⁻¹' (Iic a) = Iic (a / c) :=
ext $ λ x, (le_div_iff' h).symm

@[simp] lemma preimage_const_mul_Ici (a : α) {c : α} (h : 0 < c) :
  ((*) c) ⁻¹' (Ici a) = Ici (a / c) :=
ext $ λ x, (div_le_iff' h).symm

@[simp] lemma preimage_const_mul_Ioo (a b : α) {c : α} (h : 0 < c) :
  ((*) c) ⁻¹' (Ioo a b) = Ioo (a / c) (b / c) :=
by simp [← Ioi_inter_Iio, h]

@[simp] lemma preimage_const_mul_Ioc (a b : α) {c : α} (h : 0 < c) :
  ((*) c) ⁻¹' (Ioc a b) = Ioc (a / c) (b / c) :=
by simp [← Ioi_inter_Iic, h]

@[simp] lemma preimage_const_mul_Ico (a b : α) {c : α} (h : 0 < c) :
  ((*) c) ⁻¹' (Ico a b) = Ico (a / c) (b / c) :=
by simp [← Ici_inter_Iio, h]

@[simp] lemma preimage_const_mul_Icc (a b : α) {c : α} (h : 0 < c) :
  ((*) c) ⁻¹' (Icc a b) = Icc (a / c) (b / c) :=
by simp [← Ici_inter_Iic, h]

@[simp] lemma preimage_const_mul_Iio_of_neg (a : α) {c : α} (h : c < 0) :
  ((*) c) ⁻¹' (Iio a) = Ioi (a / c) :=
by simpa only [mul_comm] using preimage_mul_const_Iio_of_neg a h

@[simp] lemma preimage_const_mul_Ioi_of_neg (a : α) {c : α} (h : c < 0) :
  ((*) c) ⁻¹' (Ioi a) = Iio (a / c) :=
by simpa only [mul_comm] using preimage_mul_const_Ioi_of_neg a h

@[simp] lemma preimage_const_mul_Iic_of_neg (a : α) {c : α} (h : c < 0) :
  ((*) c) ⁻¹' (Iic a) = Ici (a / c) :=
by simpa only [mul_comm] using preimage_mul_const_Iic_of_neg a h

@[simp] lemma preimage_const_mul_Ici_of_neg (a : α) {c : α} (h : c < 0) :
  ((*) c) ⁻¹' (Ici a) = Iic (a / c) :=
by simpa only [mul_comm] using preimage_mul_const_Ici_of_neg a h

@[simp] lemma preimage_const_mul_Ioo_of_neg (a b : α) {c : α} (h : c < 0) :
  ((*) c) ⁻¹' (Ioo a b) = Ioo (b / c) (a / c) :=
by simpa only [mul_comm] using preimage_mul_const_Ioo_of_neg a b h

@[simp] lemma preimage_const_mul_Ioc_of_neg (a b : α) {c : α} (h : c < 0) :
  ((*) c) ⁻¹' (Ioc a b) = Ico (b / c) (a / c) :=
by simpa only [mul_comm] using preimage_mul_const_Ioc_of_neg a b h

@[simp] lemma preimage_const_mul_Ico_of_neg (a b : α) {c : α} (h : c < 0) :
  ((*) c) ⁻¹' (Ico a b) = Ioc (b / c) (a / c) :=
by simpa only [mul_comm] using preimage_mul_const_Ico_of_neg a b h

@[simp] lemma preimage_const_mul_Icc_of_neg (a b : α) {c : α} (h : c < 0) :
  ((*) c) ⁻¹' (Icc a b) = Icc (b / c) (a / c) :=
by simpa only [mul_comm] using preimage_mul_const_Icc_of_neg a b h

@[simp] lemma preimage_mul_const_uIcc (ha : a ≠ 0) (b c : α) :
  (λ x, x * a) ⁻¹' [b, c] = [b / a, c / a] :=
(lt_or_gt_of_ne ha).elim
  (λ h, by simp [←Icc_min_max, h, h.le, min_div_div_right_of_nonpos, max_div_div_right_of_nonpos])
  (λ (ha : 0 < a), by simp [←Icc_min_max, ha, ha.le, min_div_div_right, max_div_div_right])

@[simp] lemma preimage_const_mul_uIcc (ha : a ≠ 0) (b c : α) :
  (λ x, a * x) ⁻¹' [b, c] = [b / a, c / a] :=
by simp only [← preimage_mul_const_uIcc ha, mul_comm]

@[simp] lemma preimage_div_const_uIcc (ha : a ≠ 0) (b c : α) :
  (λ x, x / a) ⁻¹' [b, c] = [b * a, c * a] :=
by simp only [div_eq_mul_inv, preimage_mul_const_uIcc (inv_ne_zero ha), inv_inv]

@[simp] lemma image_mul_const_uIcc (a b c : α) : (λ x, x * a) '' [b, c] = [b * a, c * a] :=
if ha : a = 0 then by simp [ha] else
calc (λ x, x * a) '' [b, c] = (λ x, x * a⁻¹) ⁻¹' [b, c] :
  (units.mk0 a ha).mul_right.image_eq_preimage _
... = (λ x, x / a) ⁻¹' [b, c] : by simp only [div_eq_mul_inv]
... = [b * a, c * a] : preimage_div_const_uIcc ha _ _

@[simp] lemma image_const_mul_uIcc (a b c : α) : (λ x, a * x) '' [b, c] = [a * b, a * c] :=
by simpa only [mul_comm] using image_mul_const_uIcc a b c

@[simp] lemma image_div_const_uIcc (a b c : α) : (λ x, x / a) '' [b, c] = [b / a, c / a] :=
by simp only [div_eq_mul_inv, image_mul_const_uIcc]

lemma image_mul_right_Icc' (a b : α) {c : α} (h : 0 < c) :
  (λ x, x * c) '' Icc a b = Icc (a * c) (b * c) :=
((units.mk0 c h.ne').mul_right.image_eq_preimage _).trans (by simp [h, division_def])

lemma image_mul_right_Icc {a b c : α} (hab : a ≤ b) (hc : 0 ≤ c) :
  (λ x, x * c) '' Icc a b = Icc (a * c) (b * c) :=
begin
  cases eq_or_lt_of_le hc,
  { subst c,
    simp [(nonempty_Icc.2 hab).image_const] },
  exact image_mul_right_Icc' a b ‹0 < c›
end

lemma image_mul_left_Icc' {a : α} (h : 0 < a) (b c : α) :
  ((*) a) '' Icc b c = Icc (a * b) (a * c) :=
by { convert image_mul_right_Icc' b c h using 1; simp only [mul_comm _ a] }

lemma image_mul_left_Icc {a b c : α} (ha : 0 ≤ a) (hbc : b ≤ c) :
  ((*) a) '' Icc b c = Icc (a * b) (a * c) :=
by { convert image_mul_right_Icc hbc ha using 1; simp only [mul_comm _ a] }

lemma image_mul_right_Ioo (a b : α) {c : α} (h : 0 < c) :
  (λ x, x * c) '' Ioo a b = Ioo (a * c) (b * c) :=
((units.mk0 c h.ne').mul_right.image_eq_preimage _).trans (by simp [h, division_def])

lemma image_mul_left_Ioo {a : α} (h : 0 < a) (b c : α) :
  ((*) a) '' Ioo b c = Ioo (a * b) (a * c) :=
by { convert image_mul_right_Ioo b c h using 1; simp only [mul_comm _ a] }

/-- The (pre)image under `inv` of `Ioo 0 a` is `Ioi a⁻¹`. -/
lemma inv_Ioo_0_left {a : α} (ha : 0 < a) : (Ioo 0 a)⁻¹ = Ioi a⁻¹ :=
begin
  ext x,
  exact ⟨λ h, inv_inv x ▸ (inv_lt_inv ha h.1).2 h.2, λ h, ⟨inv_pos.2 $ (inv_pos.2 ha).trans h,
    inv_inv a ▸ (inv_lt_inv ((inv_pos.2 ha).trans h) (inv_pos.2 ha)).2 h⟩⟩,
end

lemma inv_Ioi {a : α} (ha : 0 < a) : (Ioi a)⁻¹ = Ioo 0 a⁻¹ :=
by rw [inv_eq_iff_eq_inv, inv_Ioo_0_left (inv_pos.2 ha), inv_inv]

lemma image_const_mul_Ioi_zero {k : Type*} [linear_ordered_field k]
  {x : k} (hx : 0 < x) :
  (λ y, x * y) '' Ioi (0 : k) = Ioi 0 :=
by erw [(units.mk0 x hx.ne').mul_left.image_eq_preimage, preimage_const_mul_Ioi 0 (inv_pos.mpr hx),
  zero_div]

/-!
### Images under `x ↦ a * x + b`
-/

@[simp] lemma image_affine_Icc' {a : α} (h : 0 < a) (b c d : α) :
  (λ x, a * x + b) '' Icc c d = Icc (a * c + b) (a * d + b) :=
begin
  suffices : (λ x, x + b) '' ((λ x, a * x) '' Icc c d) = Icc (a * c + b) (a * d + b),
  { rwa set.image_image at this, },
  rw [image_mul_left_Icc' h, image_add_const_Icc],
end

end linear_ordered_field
end set
