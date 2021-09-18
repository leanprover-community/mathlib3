/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import linear_algebra.affine_space.midpoint
import algebra.module.ordered
import tactic.field_simp

/-!
# Ordered modules as affine spaces

In this file we define the slope of a function `f : k → PE` taking values in an affine space over
`k` and prove some theorems about `slope` and `line_map` in the case when `PE` is an ordered
module over `k`. The `slope` function naturally appears in the Mean Value Theorem, and in the
proof of the fact that a function with nonnegative second derivative on an interval is convex on
this interval. In the third part of this file we prove inequalities that will be used in
`analysis.convex.function` to link convexity of a function on an interval to monotonicity of the
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
### Definition of `slope` and basic properties

In this section we define `slope f a b` and prove some properties that do not require order on the
codomain.  -/

section no_order

variables [field k] [add_comm_group E] [module k E] [add_torsor E PE]

include E

/-- `slope f a b = (b - a)⁻¹ • (f b -ᵥ f a)` is the slope of a function `f` on the interval
`[a, b]`. Note that `slope f a a = 0`, not the derivative of `f` at `a`. -/
def slope (f : k → PE) (a b : k) : E := (b - a)⁻¹ • (f b -ᵥ f a)

omit E

lemma slope_def_field (f : k → k) (a b : k) : slope f a b = (f b - f a) / (b - a) :=
div_eq_inv_mul.symm

@[simp] lemma slope_same (f : k → PE) (a : k) : (slope f a a : E) = 0 :=
by rw [slope, sub_self, inv_zero, zero_smul]

include E

lemma eq_of_slope_eq_zero {f : k → PE} {a b : k} (h : slope f a b = (0:E)) : f a = f b :=
begin
  rw [slope, smul_eq_zero, inv_eq_zero, sub_eq_zero, vsub_eq_zero_iff_eq] at h,
  exact h.elim (λ h, h ▸ rfl) eq.symm
end

lemma slope_comm (f : k → PE) (a b : k) : slope f a b = slope f b a :=
by rw [slope, slope, ← neg_vsub_eq_vsub_rev, smul_neg, ← neg_smul, neg_inv, neg_sub]

/-- `slope f a c` is a linear combination of `slope f a b` and `slope f b c`. This version
explicitly provides coefficients. If `a ≠ c`, then the sum of the coefficients is `1`, so it is
actually an affine combination, see `line_map_slope_slope_sub_div_sub`. -/
lemma sub_div_sub_smul_slope_add_sub_div_sub_smul_slope (f : k → PE) (a b c : k) :
  ((b - a) / (c - a)) • slope f a b + ((c - b) / (c - a)) • slope f b c = slope f a c :=
begin
  by_cases hab : a = b,
  { subst hab,
    rw [sub_self, zero_div, zero_smul, zero_add],
    by_cases hac : a = c,
    { simp [hac] },
    { rw [div_self (sub_ne_zero.2 $ ne.symm hac), one_smul] } },
  by_cases hbc : b = c, { subst hbc, simp [sub_ne_zero.2 (ne.symm hab)] },
  rw [add_comm],
  simp_rw [slope, div_eq_inv_mul, mul_smul, ← smul_add,
    smul_inv_smul' (sub_ne_zero.2 $ ne.symm hab), smul_inv_smul' (sub_ne_zero.2 $ ne.symm hbc),
    vsub_add_vsub_cancel],
end

/-- `slope f a c` is an affine combination of `slope f a b` and `slope f b c`. This version uses
`line_map` to express this property. -/
lemma line_map_slope_slope_sub_div_sub (f : k → PE) (a b c : k) (h : a ≠ c) :
  line_map (slope f a b) (slope f b c) ((c - b) / (c - a)) = slope f a c :=
by  field_simp [sub_ne_zero.2 h.symm, ← sub_div_sub_smul_slope_add_sub_div_sub_smul_slope f a b c,
  line_map_apply_module]

/-- `slope f a b` is an affine combination of `slope f a (line_map a b r)` and
`slope f (line_map a b r) b`. We use `line_map` to express this property. -/
lemma line_map_slope_line_map_slope_line_map (f : k → PE) (a b r : k) :
  line_map (slope f (line_map a b r) b) (slope f a (line_map a b r)) r = slope f a b :=
begin
  obtain (rfl|hab) : a = b ∨ a ≠ b := classical.em _, { simp },
  rw [slope_comm _ a, slope_comm _ a, slope_comm _ _ b],
  convert line_map_slope_slope_sub_div_sub f b (line_map a b r) a hab.symm using 2,
  rw [line_map_apply_ring, eq_div_iff (sub_ne_zero.2 hab), sub_mul, one_mul, mul_sub, ← sub_sub,
    sub_sub_cancel]
end

end no_order

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
@left_lt_line_map_iff_lt k (order_dual E) _ _ _ _ _ _ _ h

lemma line_map_lt_right_iff_lt (h : r < 1) : line_map a b r < b ↔ a < b :=
iff.trans (by rw line_map_apply_one) (line_map_lt_line_map_iff_of_lt h)

lemma right_lt_line_map_iff_lt (h : r < 1) : b < line_map a b r ↔ b < a :=
@line_map_lt_right_iff_lt k (order_dual E) _ _ _ _ _ _ _ h

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
@left_le_line_map_iff_le k (order_dual E) _ _ _ _ _ _ _ h

@[simp] lemma midpoint_le_left : midpoint k a b ≤ a ↔ b ≤ a :=
line_map_le_left_iff_le $ inv_pos.2 zero_lt_two

lemma line_map_le_right_iff_le (h : r < 1) : line_map a b r ≤ b ↔ a ≤ b :=
iff.trans (by rw line_map_apply_one) (line_map_le_line_map_iff_of_lt h)

@[simp] lemma midpoint_le_right : midpoint k a b ≤ b ↔ a ≤ b :=
line_map_le_right_iff_le $ inv_lt_one one_lt_two

lemma right_le_line_map_iff_le (h : r < 1) : b ≤ line_map a b r ↔ b ≤ a :=
@line_map_le_right_iff_le k (order_dual E) _ _ _ _ _ _ _ h

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

Later these inequalities will be used in to restate `convex_on` in terms of monotonicity of the
slope.
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
  sub_le_iff_le_add, mul_inv_rev', mul_smul, mul_smul, ←smul_sub, ←smul_sub, ←smul_add, smul_smul,
  ← mul_inv_rev', smul_le_iff_of_pos (inv_pos.2 h), inv_inv', smul_smul,
  mul_inv_cancel_right' (right_ne_zero_of_mul h.ne'), smul_add,
  smul_inv_smul' (left_ne_zero_of_mul h.ne')],
  apply_instance
end

/-- Given `c = line_map a b r`, `a < c`, the point `(c, f c)` is non-strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f a b ≤ slope f a c`. -/
lemma line_map_le_map_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
  line_map (f a) (f b) r ≤ f c ↔ slope f a b ≤ slope f a c :=
@map_le_line_map_iff_slope_le_slope_left k (order_dual E) _ _ _ _ f a b r h

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
@map_lt_line_map_iff_slope_lt_slope_left k (order_dual E) _ _ _ _ f a b r h

/-- Given `c = line_map a b r`, `c < b`, the point `(c, f c)` is non-strictly below the
segment `[(a, f a), (b, f b)]` if and only if `slope f a b ≤ slope f c b`. -/
lemma map_le_line_map_iff_slope_le_slope_right (h : 0 < (1 - r) * (b - a)) :
  f c ≤ line_map (f a) (f b) r ↔ slope f a b ≤ slope f c b :=
begin
  rw [← line_map_apply_one_sub, ← line_map_apply_one_sub _ _ r],
  revert h, generalize : 1 - r = r', clear r, intro h,
  simp_rw [line_map_apply, slope, vsub_eq_sub, vadd_eq_add, smul_eq_mul],
  rw [sub_add_eq_sub_sub_swap, sub_self, zero_sub, le_smul_iff_of_pos, inv_inv', smul_smul,
    neg_mul_eq_mul_neg, neg_sub, mul_inv_cancel_right', le_sub, ← neg_sub (f b), smul_neg,
    neg_add_eq_sub],
  { exact right_ne_zero_of_mul h.ne' },
  { simpa [mul_sub] using h }
end

/-- Given `c = line_map a b r`, `c < b`, the point `(c, f c)` is non-strictly above the
segment `[(a, f a), (b, f b)]` if and only if `slope f c b ≤ slope f a b`. -/
lemma line_map_le_map_iff_slope_le_slope_right (h : 0 < (1 - r) * (b - a)) :
  line_map (f a) (f b) r ≤ f c ↔ slope f c b ≤ slope f a b :=
@map_le_line_map_iff_slope_le_slope_right k (order_dual E) _ _ _ _ f a b r h

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
@map_lt_line_map_iff_slope_lt_slope_right k (order_dual E) _ _ _ _ f a b r h

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
@map_le_line_map_iff_slope_le_slope k (order_dual E) _ _ _ _ _ _ _ _ hab h₀ h₁

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
@map_lt_line_map_iff_slope_lt_slope k (order_dual E) _ _ _ _ _ _ _ _ hab h₀ h₁

end linear_ordered_field
