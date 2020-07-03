/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot
-/
import data.set.intervals.basic
import data.equiv.mul_add

/-!
# (Pre)images of intervals

In this file we prove a bunch of trivial lemmas like “if we add `a` to all points of `[b, c]`,
then we get `[a + b, a + c]`”. For the functions `x ↦ x ± a`, `x ↦ a ± x`, and `x ↦ -x` we prove
lemmas about preimages and images of all intervals. We also prove a few lemmas about images under
`x ↦ a * x`, `x ↦ x * a` and `x ↦ x⁻¹`.

-/

universe u

namespace set
section ordered_add_comm_group

variables {G : Type u} [ordered_add_comm_group G] (a b c : G)

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

@[simp] lemma preimage_neg_Ici : has_neg.neg ⁻¹' (Ici a) = Iic (-a) := ext $ λ x, le_neg
@[simp] lemma preimage_neg_Iic : has_neg.neg ⁻¹' (Iic a) = Ici (-a) := ext $ λ x, neg_le
@[simp] lemma preimage_neg_Ioi : has_neg.neg ⁻¹' (Ioi a) = Iio (-a) := ext $ λ x, lt_neg
@[simp] lemma preimage_neg_Iio : has_neg.neg ⁻¹' (Iio a) = Ioi (-a) := ext $ λ x, neg_lt

@[simp] lemma preimage_neg_Icc : has_neg.neg ⁻¹' (Icc a b) = Icc (-b) (-a) :=
by simp [← Ici_inter_Iic, inter_comm]

@[simp] lemma preimage_neg_Ico : has_neg.neg ⁻¹' (Ico a b) = Ioc (-b) (-a) :=
by simp [← Ici_inter_Iio, ← Ioi_inter_Iic, inter_comm]

@[simp] lemma preimage_neg_Ioc : has_neg.neg ⁻¹' (Ioc a b) = Ico (-b) (-a) :=
by simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[simp] lemma preimage_neg_Ioo : has_neg.neg ⁻¹' (Ioo a b) = Ioo (-b) (-a) :=
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
ext $ λ x, le_sub

@[simp] lemma preimage_const_sub_Iic : (λ x, a - x) ⁻¹' (Iic b) = Ici (a - b) :=
ext $ λ x, sub_le

@[simp] lemma preimage_const_sub_Ioi : (λ x, a - x) ⁻¹' (Ioi b) = Iio (a - b) :=
ext $ λ x, lt_sub

@[simp] lemma preimage_const_sub_Iio : (λ x, a - x) ⁻¹' (Iio b) = Ioi (a - b) :=
ext $ λ x, sub_lt

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

@[simp] lemma image_const_add_Ici : (λ x, a + x) '' Ici b = Ici (a + b) :=
((equiv.add_left a).image_eq_preimage _).trans $ by simp [add_comm]

@[simp] lemma image_const_add_Iic : (λ x, a + x) '' Iic b = Iic (a + b) :=
((equiv.add_left a).image_eq_preimage _).trans $ by simp [add_comm]

@[simp] lemma image_const_add_Iio : (λ x, a + x) '' Iio b = Iio (a + b) :=
((equiv.add_left a).image_eq_preimage _).trans $ by simp [add_comm]

@[simp] lemma image_const_add_Ioi : (λ x, a + x) '' Ioi b = Ioi (a + b) :=
((equiv.add_left a).image_eq_preimage _).trans $ by simp [add_comm]

@[simp] lemma image_const_add_Icc : (λ x, a + x) '' Icc b c = Icc (a + b) (a + c) :=
((equiv.add_left a).image_eq_preimage _).trans $ by simp [add_comm]

@[simp] lemma image_const_add_Ico : (λ x, a + x) '' Ico b c = Ico (a + b) (a + c) :=
((equiv.add_left a).image_eq_preimage _).trans $ by simp [add_comm]

@[simp] lemma image_const_add_Ioc : (λ x, a + x) '' Ioc b c = Ioc (a + b) (a + c) :=
((equiv.add_left a).image_eq_preimage _).trans $ by simp [add_comm]

@[simp] lemma image_const_add_Ioo : (λ x, a + x) '' Ioo b c = Ioo (a + b) (a + c) :=
((equiv.add_left a).image_eq_preimage _).trans $ by simp [add_comm]

/-!
### Images under `x ↦ x + a`
-/

@[simp] lemma image_add_const_Ici : (λ x, x + a) '' Ici b = Ici (a + b) := by simp [add_comm _ a]
@[simp] lemma image_add_const_Iic : (λ x, x + a) '' Iic b = Iic (a + b) := by simp [add_comm _ a]
@[simp] lemma image_add_const_Iio : (λ x, x + a) '' Iio b = Iio (a + b) := by simp [add_comm _ a]
@[simp] lemma image_add_const_Ioi : (λ x, x + a) '' Ioi b = Ioi (a + b) := by simp [add_comm _ a]

@[simp] lemma image_add_const_Icc : (λ x, x + a) '' Icc b c = Icc (a + b) (a + c) :=
by simp [add_comm _ a]

@[simp] lemma image_add_const_Ico : (λ x, x + a) '' Ico b c = Ico (a + b) (a + c) :=
by simp [add_comm _ a]

@[simp] lemma image_add_const_Ioc : (λ x, x + a) '' Ioc b c = Ioc (a + b) (a + c) :=
by simp [add_comm _ a]

@[simp] lemma image_add_const_Ioo : (λ x, x + a) '' Ioo b c = Ioo (a + b) (a + c) :=
by simp [add_comm _ a]

/-!
### Images under `x ↦ -x`
-/

@[simp] lemma image_neg_Ici : has_neg.neg '' (Ici a) = Iic (-a) :=
((equiv.neg G).image_eq_preimage _).trans $ preimage_neg_Ici _

@[simp] lemma image_neg_Iic : has_neg.neg '' (Iic a) = Ici (-a) :=
((equiv.neg G).image_eq_preimage _).trans $ preimage_neg_Iic _

@[simp] lemma image_neg_Ioi : has_neg.neg '' (Ioi a) = Iio (-a) :=
((equiv.neg G).image_eq_preimage _).trans $ preimage_neg_Ioi _

@[simp] lemma image_neg_Iio : has_neg.neg '' (Iio a) = Ioi (-a) :=
((equiv.neg G).image_eq_preimage _).trans $ preimage_neg_Iio _

@[simp] lemma image_neg_Icc : has_neg.neg '' (Icc a b) = Icc (-b) (-a) :=
((equiv.neg G).image_eq_preimage _).trans $ preimage_neg_Icc _ _

@[simp] lemma image_neg_Ico : has_neg.neg '' (Ico a b) = Ioc (-b) (-a) :=
((equiv.neg G).image_eq_preimage _).trans $ preimage_neg_Ico _ _

@[simp] lemma image_neg_Ioc : has_neg.neg '' (Ioc a b) = Ico (-b) (-a) :=
((equiv.neg G).image_eq_preimage _).trans $ preimage_neg_Ioc _ _

@[simp] lemma image_neg_Ioo : has_neg.neg '' (Ioo a b) = Ioo (-b) (-a) :=
((equiv.neg G).image_eq_preimage _).trans $ preimage_neg_Ioo _ _

/-!
### Images under `x ↦ a - x`
-/

@[simp] lemma image_const_sub_Ici : (λ x, a - x) '' Ici b = Iic (a - b) :=
by simp [sub_eq_add_neg, image_comp (λ x, a + x) (λ x, -x)]

@[simp] lemma image_const_sub_Iic : (λ x, a - x) '' Iic b = Ici (a - b) :=
by simp [sub_eq_add_neg, image_comp (λ x, a + x) (λ x, -x)]

@[simp] lemma image_const_sub_Ioi : (λ x, a - x) '' Ioi b = Iio (a - b) :=
by simp [sub_eq_add_neg, image_comp (λ x, a + x) (λ x, -x)]

@[simp] lemma image_const_sub_Iio : (λ x, a - x) '' Iio b = Ioi (a - b) :=
by simp [sub_eq_add_neg, image_comp (λ x, a + x) (λ x, -x)]

@[simp] lemma image_const_sub_Icc : (λ x, a - x) '' Icc b c = Icc (a - c) (a - b) :=
by simp [sub_eq_add_neg, image_comp (λ x, a + x) (λ x, -x)]

@[simp] lemma image_const_sub_Ico : (λ x, a - x) '' Ico b c = Ioc (a - c) (a - b) :=
by simp [sub_eq_add_neg, image_comp (λ x, a + x) (λ x, -x)]

@[simp] lemma image_const_sub_Ioc : (λ x, a - x) '' Ioc b c = Ico (a - c) (a - b) :=
by simp [sub_eq_add_neg, image_comp (λ x, a + x) (λ x, -x)]

@[simp] lemma image_const_sub_Ioo : (λ x, a - x) '' Ioo b c = Ioo (a - c) (a - b) :=
by simp [sub_eq_add_neg, image_comp (λ x, a + x) (λ x, -x)]

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

end ordered_add_comm_group

/-!
### Multiplication and inverse in a field
-/

section linear_ordered_field

variables {k : Type u} [linear_ordered_field k]

lemma image_mul_right_Icc' (a b : k) {c : k} (h : 0 < c) :
  (λ x, x * c) '' Icc a b = Icc (a * c) (b * c) :=
begin
  ext x,
  split,
  { rintros ⟨x, hx, rfl⟩,
    exact ⟨mul_le_mul_of_nonneg_right hx.1 (le_of_lt h),
      mul_le_mul_of_nonneg_right hx.2 (le_of_lt h)⟩ },
  { intro hx,
    refine ⟨x / c, _, div_mul_cancel x (ne_of_gt h)⟩,
    exact ⟨le_div_of_mul_le h hx.1, div_le_of_le_mul h (mul_comm b c ▸ hx.2)⟩ }
end

lemma image_mul_right_Icc {a b c : k} (hab : a ≤ b) (hc : 0 ≤ c) :
  (λ x, x * c) '' Icc a b = Icc (a * c) (b * c) :=
begin
  cases eq_or_lt_of_le hc,
  { subst c,
    simp [(nonempty_Icc.2 hab).image_const] },
  exact image_mul_right_Icc' a b ‹0 < c›
end

lemma image_mul_left_Icc' {a : k} (h : 0 < a) (b c : k) :
  ((*) a) '' Icc b c = Icc (a * b) (a * c) :=
by { convert image_mul_right_Icc' b c h using 1; simp only [mul_comm _ a] }

lemma image_mul_left_Icc {a b c : k} (ha : 0 ≤ a) (hbc : b ≤ c) :
  ((*) a) '' Icc b c = Icc (a * b) (a * c) :=
by { convert image_mul_right_Icc hbc ha using 1; simp only [mul_comm _ a] }

/-- The image under `inv` of `Ioo 0 a` is `Ioi a⁻¹`. -/
lemma image_inv_Ioo_0_left {a : k} (ha : 0 < a) : has_inv.inv '' Ioo 0 a = Ioi a⁻¹ :=
begin
  ext x,
  split,
  { rintros ⟨y, ⟨hy0, hya⟩, hyx⟩,
    exact hyx ▸ (inv_lt_inv ha hy0).2 hya },
  { exact λ h, ⟨x⁻¹, ⟨inv_pos.2 (lt_trans (inv_pos.2 ha) h),
                      (inv_lt ha (lt_trans (inv_pos.2 ha) h)).1 h⟩,
                     inv_inv' x⟩ }
end

end linear_ordered_field
end set
