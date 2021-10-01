/-
Copyright (c) 2021 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov, Malo Jaffré
-/
import analysis.convex.function

/-!
# Slopes of convex functions

This file relates convexity/concavity of functions in a linearly ordered field and the monotonicity
of their slopes.

The main use is to show convexity/concavity from monotonicity of the derivative.
-/

variables {𝕜 : Type*} [linear_ordered_field 𝕜] {s : set 𝕜} {f : 𝕜 → 𝕜}

/-- If `f : 𝕜 → 𝕜` is convex, then for any three points `x < y < z` the slope of the secant line of
`f` on `[x, y]` is less than the slope of the secant line of `f` on `[x, z]`. -/
lemma convex_on.slope_mono_adjacent (hf : convex_on 𝕜 s f)
  {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
  (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) :=
begin
  have hxz := hxy.trans hyz,
  rw ←sub_pos at hxy hxz hyz,
  suffices : f y / (y - x) + f y / (z - y) ≤ f x / (y - x) + f z / (z - y),
  { ring_nf at this ⊢, linarith },
  set a := (z - y) / (z - x),
  set b := (y - x) / (z - x),
  have hy : a • x + b • z = y, by { field_simp, rw div_eq_iff; [ring, linarith] },
  have key, from
    hf.2 hx hz
      (show 0 ≤ a, by apply div_nonneg; linarith)
      (show 0 ≤ b, by apply div_nonneg; linarith)
      (show a + b = 1, by { field_simp, rw div_eq_iff; [ring, linarith] }),
  rw hy at key,
  replace key := mul_le_mul_of_nonneg_left key hxz.le,
  field_simp [hxy.ne', hyz.ne', hxz.ne', mul_comm (z - x) _] at key ⊢,
  rw div_le_div_right,
  { linarith },
  { nlinarith }
end

/-- If `f : 𝕜 → 𝕜` is concave, then for any three points `x < y < z` the slope of the secant line of
`f` on `[x, y]` is greater than the slope of the secant line of `f` on `[x, z]`. -/
lemma concave_on.slope_anti_adjacent (hf : concave_on 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s)
  (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
  (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) :=
begin
  rw [←neg_le_neg_iff, ←neg_sub_neg (f x), ←neg_sub_neg (f y)],
  simp_rw [←pi.neg_apply, ←neg_div, neg_sub],
  exact convex_on.slope_mono_adjacent hf.neg hx hz hxy hyz,
end

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
less than the slope of the secant line of `f` on `[x, z]`, then `f` is convex. -/
lemma convex_on_of_slope_mono_adjacent (hs : convex 𝕜 s)
  (hf : ∀ {x y z : 𝕜}, x ∈ s → z ∈ s → x < y → y < z →
    (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) :
  convex_on 𝕜 s f :=
linear_order.convex_on_of_lt hs
begin
  assume x z hx hz hxz a b ha hb hab,
  let y := a * x + b * z,
  have hxy : x < y,
  { rw [← one_mul x, ← hab, add_mul],
    exact add_lt_add_left ((mul_lt_mul_left hb).2 hxz) _ },
  have hyz : y < z,
  { rw [← one_mul z, ← hab, add_mul],
    exact add_lt_add_right ((mul_lt_mul_left ha).2 hxz) _ },
  have : (f y - f x) * (z - y) ≤ (f z - f y) * (y - x),
    from (div_le_div_iff (sub_pos.2 hxy) (sub_pos.2 hyz)).1 (hf hx hz hxy hyz),
  have hxz : 0 < z - x, from sub_pos.2 (hxy.trans hyz),
  have ha : (z - y) / (z - x) = a,
  { rw [eq_comm, ← sub_eq_iff_eq_add'] at hab,
    simp_rw [div_eq_iff hxz.ne', y, ←hab], ring },
  have hb : (y - x) / (z - x) = b,
  { rw [eq_comm, ← sub_eq_iff_eq_add] at hab,
    simp_rw [div_eq_iff hxz.ne', y, ←hab], ring },
  rwa [sub_mul, sub_mul, sub_le_iff_le_add', ← add_sub_assoc, le_sub_iff_add_le, ← mul_add,
    sub_add_sub_cancel, ← le_div_iff hxz, add_div, mul_div_assoc, mul_div_assoc, mul_comm (f x),
    mul_comm (f z), ha, hb] at this,
end

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
greater than the slope of the secant line of `f` on `[x, z]`, then `f` is concave. -/
lemma concave_on_of_slope_anti_adjacent (hs : convex 𝕜 s)
  (hf : ∀ {x y z : 𝕜}, x ∈ s → z ∈ s → x < y → y < z →
    (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) : concave_on 𝕜 s f :=
begin
  rw ←neg_convex_on_iff,
  refine convex_on_of_slope_mono_adjacent hs (λ x y z hx hz hxy hyz, _),
  rw ←neg_le_neg_iff,
  simp_rw [←neg_div, neg_sub, pi.neg_apply, neg_sub_neg],
  exact hf hx hz hxy hyz,
end

/-- A function `f : 𝕜 → 𝕜` is convex iff for any three points `x < y < z` the slope of the secant
line of `f` on `[x, y]` is less than the slope of the secant line of `f` on `[x, z]`. -/
lemma convex_on_iff_slope_mono_adjacent :
  convex_on 𝕜 s f ↔ convex 𝕜 s ∧
    ∀ ⦃x y z : 𝕜⦄, x ∈ s → z ∈ s → x < y → y < z →
      (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) :=
⟨λ h, ⟨h.1, λ x y z, h.slope_mono_adjacent⟩, λ h, convex_on_of_slope_mono_adjacent h.1 h.2⟩

/-- A function `f : 𝕜 → 𝕜` is concave iff for any three points `x < y < z` the slope of the secant
line of `f` on `[x, y]` is greater than the slope of the secant line of `f` on `[x, z]`. -/
lemma concave_on_iff_slope_anti_adjacent :
  concave_on 𝕜 s f ↔ convex 𝕜 s ∧
    ∀ ⦃x y z : 𝕜⦄, x ∈ s → z ∈ s → x < y → y < z →
      (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) :=
⟨λ h, ⟨h.1, λ x y z, h.slope_anti_adjacent⟩, λ h, concave_on_of_slope_anti_adjacent h.1 h.2⟩
