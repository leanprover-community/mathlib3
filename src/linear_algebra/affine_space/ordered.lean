/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import algebra.order.invertible
import algebra.order.module
import linear_algebra.affine_space.midpoint
import linear_algebra.affine_space.slope
import tactic.field_simp

/-!
# Ordered modules as affine spaces

In this file we prove some theorems about `slope` and `line_map` in the case when the module `E`
acting on the codomain `PE` of a function is an ordered module over its domain `k`. We also prove
inequalities that can be used to link convexity of a function on an interval to monotonicity of the
slope, see section docstring below for details.

## Implementation notes

We do not introduce the notion of ordered affine spaces (yet?). Instead, we prove various theorems
for an ordered module interpreted as an affine space.

## Tags

affine space, ordered module, slope
-/

open affine_map

variables {k E PE : Type*}

/-!
### Monotonicity of `line_map`

In this section we prove that `line_map a b r` is monotone (strictly or not) in its arguments if
other arguments belong to specific domains.
-/

section ordered_ring

variables [ordered_ring k] [ordered_add_comm_group E] [module k E] [ordered_smul k E]

variables {a a' b b' : E} {r r' : k}

lemma line_map_mono_left (ha : a ≤ a') (hr : r ≤ 1) :
  line_map a b r ≤ line_map a' b r :=
begin
  simp only [line_map_apply_module],
  exact add_le_add_right (smul_le_smul_of_nonneg ha (sub_nonneg.2 hr)) _
end

lemma line_map_strict_mono_left (ha : a < a') (hr : r < 1) :
  line_map a b r < line_map a' b r :=
begin
  simp only [line_map_apply_module],
  exact add_lt_add_right (smul_lt_smul_of_pos ha (sub_pos.2 hr)) _
end

lemma line_map_mono_right (hb : b ≤ b') (hr : 0 ≤ r) :
  line_map a b r ≤ line_map a b' r :=
begin
  simp only [line_map_apply_module],
  exact add_le_add_left (smul_le_smul_of_nonneg hb hr) _
end

lemma line_map_strict_mono_right (hb : b < b') (hr : 0 < r) :
  line_map a b r < line_map a b' r :=
begin
  simp only [line_map_apply_module],
  exact add_lt_add_left (smul_lt_smul_of_pos hb hr) _
end

lemma line_map_mono_endpoints (ha : a ≤ a') (hb : b ≤ b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
  line_map a b r ≤ line_map a' b' r :=
(line_map_mono_left ha h₁).trans (line_map_mono_right hb h₀)

lemma line_map_strict_mono_endpoints (ha : a < a') (hb : b < b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
  line_map a b r < line_map a' b' r :=
begin
  rcases h₀.eq_or_lt with (rfl|h₀), { simpa },
  exact (line_map_mono_left ha.le h₁).trans_lt (line_map_strict_mono_right hb h₀)
end

lemma line_map_lt_line_map_iff_of_lt (h : r < r') :
  line_map a b r < line_map a b r' ↔ a < b :=
begin
  simp only [line_map_apply_module],
  rw [← lt_sub_iff_add_lt, add_sub_assoc, ← sub_lt_iff_lt_add', ← sub_smul, ← sub_smul,
    sub_sub_sub_cancel_left, smul_lt_smul_iff_of_pos (sub_pos.2 h)],
  apply_instance,
end

lemma left_lt_line_map_iff_lt (h : 0 < r) : a < line_map a b r ↔ a < b :=
iff.trans (by rw line_map_apply_zero) (line_map_lt_line_map_iff_of_lt h)

lemma line_map_lt_left_iff_lt (h : 0 < r) : line_map a b r < a ↔ b < a :=
@left_lt_line_map_iff_lt k Eᵒᵈ _ _ _ _ _ _ _ h

lemma line_map_lt_right_iff_lt (h : r < 1) : line_map a b r < b ↔ a < b :=
iff.trans (by rw line_map_apply_one) (line_map_lt_line_map_iff_of_lt h)

lemma right_lt_line_map_iff_lt (h : r < 1) : b < line_map a b r ↔ b < a :=
@line_map_lt_right_iff_lt k Eᵒᵈ _ _ _ _ _ _ _ h

end ordered_ring

section linear_ordered_ring

variables [linear_ordered_ring k] [ordered_add_comm_group E] [module k E]
  [ordered_smul k E] [invertible (2:k)] {a a' b b' : E} {r r' : k}

lemma midpoint_le_midpoint (ha : a ≤ a') (hb : b ≤ b') :
  midpoint k a b ≤ midpoint k a' b' :=
line_map_mono_endpoints ha hb (inv_of_nonneg.2 zero_le_two) $
  inv_of_le_one one_le_two

end linear_ordered_ring

section linear_ordered_field

variables [linear_ordered_field k] [ordered_add_comm_group E]
variables [module k E] [ordered_smul k E]

section

variables {a b : E} {r r' : k}

lemma line_map_le_line_map_iff_of_lt (h : r < r') :
  line_map a b r ≤ line_map a b r' ↔ a ≤ b :=
begin
  simp only [line_map_apply_module],
  rw [← le_sub_iff_add_le, add_sub_assoc, ← sub_le_iff_le_add', ← sub_smul, ← sub_smul,
    sub_sub_sub_cancel_left, smul_le_smul_iff_of_pos (sub_pos.2 h)],
  apply_instance,
end

lemma left_le_line_map_iff_le (h : 0 < r) : a ≤ line_map a b r ↔ a ≤ b :=
iff.trans (by rw line_map_apply_zero) (line_map_le_line_map_iff_of_lt h)

@[simp] lemma left_le_midpoint : a ≤ midpoint k a b ↔ a ≤ b :=
left_le_line_map_iff_le $ inv_pos.2 zero_lt_two

lemma line_map_le_left_iff_le (h : 0 < r) : line_map a b r ≤ a ↔ b ≤ a :=
@left_le_line_map_iff_le k Eᵒᵈ _ _ _ _ _ _ _ h

@[simp] lemma midpoint_le_left : midpoint k a b ≤ a ↔ b ≤ a :=
line_map_le_left_iff_le $ inv_pos.2 zero_lt_two

lemma line_map_le_right_iff_le (h : r < 1) : line_map a b r ≤ b ↔ a ≤ b :=
iff.trans (by rw line_map_apply_one) (line_map_le_line_map_iff_of_lt h)

@[simp] lemma midpoint_le_right : midpoint k a b ≤ b ↔ a ≤ b :=
line_map_le_right_iff_le $ inv_lt_one one_lt_two

lemma right_le_line_map_iff_le (h : r < 1) : b ≤ line_map a b r ↔ b ≤ a :=
@line_map_le_right_iff_le k Eᵒᵈ _ _ _ _ _ _ _ h

@[simp] lemma right_le_midpoint : b ≤ midpoint k a b ↔ b ≤ a :=
right_le_line_map_iff_le $ inv_lt_one one_lt_two

end

/-!
### Convexity and slope

Given an interval `[a, b]` and a point `c ∈ (a, b)`, `c = line_map a b r`, there are a few ways to
say that the point `(c, f c)` is above/below the segment `[(a, f a), (b, f b)]`:

* compare `f c` to `line_map (f a) (f b) r`;
* compare `slope f a c` to `slope `f a b`;
* compare `slope f c b` to `slope f a b`;
* compare `slope f a c` to `slope f c b`.

In this section we prove equivalence of these four approaches. In order to make the statements more
readable, we introduce local notation `c = line_map a b r`. Then we prove lemmas like

```
lemma map_le_line_map_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
  f c ≤ line_map (f a) (f b) r ↔ slope f a c ≤ slope f a b :=
```

For each inequality between `f c` and `line_map (f a) (f b) r` we provide 3 lemmas:

* `*_left` relates it to an inequality on `slope f a c` and `slope f a b`;
* `*_right` relates it to an inequality on `slope f a b` and `slope f c b`;
* no-suffix version relates it to an inequality on `slope f a c` and `slope f c b`.

These inequalities can by used in to restate `convex_on` in terms of monotonicity of the slope.
-/

variables {f : k → E} {a b r : k}

local notation `c` := line_map a b r

/-- Given `c = line_map a b r`, `a < c`, the point `(c, f c)` is non-strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a c ≤ slope f a b`. -/
lemma map_le_line_map_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
  f c ≤ line_map (f a) (f b) r ↔ slope f a c ≤ slope f a b :=
begin
  rw [line_map_apply, line_map_apply, slope, slope,
  vsub_eq_sub, vsub_eq_sub, vsub_eq_sub, vadd_eq_add, vadd_eq_add,
  smul_eq_mul, add_sub_cancel, smul_sub, smul_sub, smul_sub,
  sub_le_iff_le_add, mul_inv_rev, mul_smul, mul_smul, ←smul_sub, ←smul_sub, ←smul_add, smul_smul,
  ← mul_inv_rev, smul_le_iff_of_pos (inv_pos.2 h), inv_inv, smul_smul,
  mul_inv_cancel_right₀ (right_ne_zero_of_mul h.ne'), smul_add,
  smul_inv_smul₀ (left_ne_zero_of_mul h.ne')],
  apply_instance
end

/-- Given `c = line_map a b r`, `a < c`, the point `(c, f c)` is non-strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f a b ≤ slope f a c`. -/
lemma line_map_le_map_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
  line_map (f a) (f b) r ≤ f c ↔ slope f a b ≤ slope f a c :=
@map_le_line_map_iff_slope_le_slope_left k Eᵒᵈ _ _ _ _ f a b r h

/-- Given `c = line_map a b r`, `a < c`, the point `(c, f c)` is strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a c < slope f a b`. -/
lemma map_lt_line_map_iff_slope_lt_slope_left (h : 0 < r * (b - a)) :
  f c < line_map (f a) (f b) r ↔ slope f a c < slope f a b :=
lt_iff_lt_of_le_iff_le' (line_map_le_map_iff_slope_le_slope_left h)
  (map_le_line_map_iff_slope_le_slope_left h)

/-- Given `c = line_map a b r`, `a < c`, the point `(c, f c)` is strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f a b < slope f a c`. -/
lemma line_map_lt_map_iff_slope_lt_slope_left (h : 0 < r * (b - a)) :
  line_map (f a) (f b) r < f c ↔ slope f a b < slope f a c :=
@map_lt_line_map_iff_slope_lt_slope_left k Eᵒᵈ _ _ _ _ f a b r h

/-- Given `c = line_map a b r`, `c < b`, the point `(c, f c)` is non-strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a b ≤ slope f c b`. -/
lemma map_le_line_map_iff_slope_le_slope_right (h : 0 < (1 - r) * (b - a)) :
  f c ≤ line_map (f a) (f b) r ↔ slope f a b ≤ slope f c b :=
begin
  rw [← line_map_apply_one_sub, ← line_map_apply_one_sub _ _ r],
  revert h, generalize : 1 - r = r', clear r, intro h,
  simp_rw [line_map_apply, slope, vsub_eq_sub, vadd_eq_add, smul_eq_mul],
  rw [sub_add_eq_sub_sub_swap, sub_self, zero_sub, le_smul_iff_of_pos, inv_inv, smul_smul,
    neg_mul_eq_mul_neg, neg_sub, mul_inv_cancel_right₀, le_sub, ← neg_sub (f b), smul_neg,
    neg_add_eq_sub],
  { exact right_ne_zero_of_mul h.ne' },
  { simpa [mul_sub] using h }
end

/-- Given `c = line_map a b r`, `c < b`, the point `(c, f c)` is non-strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f c b ≤ slope f a b`. -/
lemma line_map_le_map_iff_slope_le_slope_right (h : 0 < (1 - r) * (b - a)) :
  line_map (f a) (f b) r ≤ f c ↔ slope f c b ≤ slope f a b :=
@map_le_line_map_iff_slope_le_slope_right k Eᵒᵈ _ _ _ _ f a b r h

/-- Given `c = line_map a b r`, `c < b`, the point `(c, f c)` is strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a b < slope f c b`. -/
lemma map_lt_line_map_iff_slope_lt_slope_right (h : 0 < (1 - r) * (b - a)) :
  f c < line_map (f a) (f b) r ↔ slope f a b < slope f c b :=
lt_iff_lt_of_le_iff_le' (line_map_le_map_iff_slope_le_slope_right h)
  (map_le_line_map_iff_slope_le_slope_right h)

/-- Given `c = line_map a b r`, `c < b`, the point `(c, f c)` is strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f c b < slope f a b`. -/
lemma line_map_lt_map_iff_slope_lt_slope_right (h : 0 < (1 - r) * (b - a)) :
  line_map (f a) (f b) r < f c ↔ slope f c b < slope f a b :=
@map_lt_line_map_iff_slope_lt_slope_right k Eᵒᵈ _ _ _ _ f a b r h

/-- Given `c = line_map a b r`, `a < c < b`, the point `(c, f c)` is non-strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a c ≤ slope f c b`. -/
lemma map_le_line_map_iff_slope_le_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
  f c ≤ line_map (f a) (f b) r ↔ slope f a c ≤ slope f c b :=
begin
  rw [map_le_line_map_iff_slope_le_slope_left (mul_pos h₀ (sub_pos.2 hab)),
    ← line_map_slope_line_map_slope_line_map f a b r, right_le_line_map_iff_le h₁],
  apply_instance,
  apply_instance,
end

/-- Given `c = line_map a b r`, `a < c < b`, the point `(c, f c)` is non-strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f c b ≤ slope f a c`. -/
lemma line_map_le_map_iff_slope_le_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
  line_map (f a) (f b) r ≤ f c ↔ slope f c b ≤ slope f a c :=
@map_le_line_map_iff_slope_le_slope k Eᵒᵈ _ _ _ _ _ _ _ _ hab h₀ h₁

/-- Given `c = line_map a b r`, `a < c < b`, the point `(c, f c)` is strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a c < slope f c b`. -/
lemma map_lt_line_map_iff_slope_lt_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
  f c < line_map (f a) (f b) r ↔ slope f a c < slope f c b :=
lt_iff_lt_of_le_iff_le' (line_map_le_map_iff_slope_le_slope hab h₀ h₁)
  (map_le_line_map_iff_slope_le_slope hab h₀ h₁)

/-- Given `c = line_map a b r`, `a < c < b`, the point `(c, f c)` is strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f c b < slope f a c`. -/
lemma line_map_lt_map_iff_slope_lt_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
  line_map (f a) (f b) r < f c ↔ slope f c b < slope f a c :=
@map_lt_line_map_iff_slope_lt_slope k Eᵒᵈ _ _ _ _ _ _ _ _ hab h₀ h₁

end linear_ordered_field
