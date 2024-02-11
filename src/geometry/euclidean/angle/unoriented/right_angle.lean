/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import analysis.special_functions.trigonometric.arctan
import geometry.euclidean.angle.unoriented.affine

/-!
# Right-angled triangles

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves basic geometrical results about distances and angles in (possibly degenerate)
right-angled triangles in real inner product spaces and Euclidean affine spaces.

## Implementation notes

Results in this file are generally given in a form with only those non-degeneracy conditions
needed for the particular result, rather than requiring affine independence of the points of a
triangle unnecessarily.

## References

* https://en.wikipedia.org/wiki/Pythagorean_theorem

-/

noncomputable theory
open_locale big_operators
open_locale euclidean_geometry
open_locale real
open_locale real_inner_product_space

namespace inner_product_geometry

variables {V : Type*} [normed_add_comm_group V] [inner_product_space ℝ V]

/-- Pythagorean theorem, if-and-only-if vector angle form. -/
lemma norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) :
  ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2 :=
begin
  rw norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero,
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y
end

/-- Pythagorean theorem, vector angle form. -/
lemma norm_add_sq_eq_norm_sq_add_norm_sq' (x y : V) (h : angle x y = π / 2) :
  ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
(norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector angle form. -/
lemma norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) :
  ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2 :=
begin
  rw norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero,
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y
end

/-- Pythagorean theorem, subtracting vectors, vector angle form. -/
lemma norm_sub_sq_eq_norm_sq_add_norm_sq' (x y : V) (h : angle x y = π / 2) :
  ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
(norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

/-- An angle in a right-angled triangle expressed using `arccos`. -/
lemma angle_add_eq_arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
  angle x (x + y) = real.arccos (‖x‖ / ‖x + y‖) :=
begin
  rw [angle, inner_add_right, h, add_zero, real_inner_self_eq_norm_mul_norm],
  by_cases hx : ‖x‖ = 0, { simp [hx] },
  rw [div_mul_eq_div_div, mul_self_div_self]
end

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
lemma angle_add_eq_arcsin_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y ≠ 0) :
  angle x (x + y) = real.arcsin (‖y‖ / ‖x + y‖) :=
begin
  have hxy : ‖x + y‖ ^ 2 ≠ 0,
  { rw [pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_real h, ne_comm],
    refine ne_of_lt _,
    rcases h0 with h0 | h0,
    { exact left.add_pos_of_pos_of_nonneg (mul_self_pos.2 (norm_ne_zero_iff.2 h0))
                                          (mul_self_nonneg _) },
    { exact left.add_pos_of_nonneg_of_pos (mul_self_nonneg _)
                                          (mul_self_pos.2 (norm_ne_zero_iff.2 h0)) } },
  rw [angle_add_eq_arccos_of_inner_eq_zero h,
      real.arccos_eq_arcsin (div_nonneg (norm_nonneg _) (norm_nonneg _)), div_pow,
      one_sub_div hxy],
  nth_rewrite 0 [pow_two],
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_real h, pow_two, add_sub_cancel', ←pow_two, ←div_pow,
      real.sqrt_sq (div_nonneg (norm_nonneg _) (norm_nonneg _))]
end

/-- An angle in a right-angled triangle expressed using `arctan`. -/
lemma angle_add_eq_arctan_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0) :
  angle x (x + y) = real.arctan (‖y‖ / ‖x‖) :=
begin
  rw [angle_add_eq_arcsin_of_inner_eq_zero h (or.inl h0), real.arctan_eq_arcsin,
      ←div_mul_eq_div_div, norm_add_eq_sqrt_iff_real_inner_eq_zero.2 h],
  nth_rewrite 2 [←real.sqrt_sq (norm_nonneg x)],
  rw [←real.sqrt_mul (sq_nonneg _), div_pow, pow_two, pow_two, mul_add, mul_one, mul_div,
      mul_comm (‖x‖ * ‖x‖), ←mul_div, div_self (mul_self_pos.2 (norm_ne_zero_iff.2 h0)).ne',
      mul_one]
end

/-- An angle in a non-degenerate right-angled triangle is positive. -/
lemma angle_add_pos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y ≠ 0) :
  0 < angle x (x + y) :=
begin
  rw [angle_add_eq_arccos_of_inner_eq_zero h, real.arccos_pos,
      norm_add_eq_sqrt_iff_real_inner_eq_zero.2 h],
  by_cases hx : x = 0, { simp [hx] },
  rw [div_lt_one (real.sqrt_pos.2 (left.add_pos_of_pos_of_nonneg
                                     (mul_self_pos.2 (norm_ne_zero_iff.2 hx))
                                     (mul_self_nonneg _))), real.lt_sqrt (norm_nonneg _),
      pow_two],
  simpa [hx] using h0
end

/-- An angle in a right-angled triangle is at most `π / 2`. -/
lemma angle_add_le_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
  angle x (x + y) ≤ π / 2 :=
begin
  rw [angle_add_eq_arccos_of_inner_eq_zero h, real.arccos_le_pi_div_two],
  exact div_nonneg (norm_nonneg _) (norm_nonneg _)
end

/-- An angle in a non-degenerate right-angled triangle is less than `π / 2`. -/
lemma angle_add_lt_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0) :
  angle x (x + y) < π / 2 :=
begin
  rw [angle_add_eq_arccos_of_inner_eq_zero h, real.arccos_lt_pi_div_two,
      norm_add_eq_sqrt_iff_real_inner_eq_zero.2 h],
  exact div_pos (norm_pos_iff.2 h0) (real.sqrt_pos.2 (left.add_pos_of_pos_of_nonneg
                                                        (mul_self_pos.2 (norm_ne_zero_iff.2 h0))
                                                        (mul_self_nonneg _)))
end

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
lemma cos_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
  real.cos (angle x (x + y)) = ‖x‖ / ‖x + y‖ :=
begin
  rw [angle_add_eq_arccos_of_inner_eq_zero h,
      real.cos_arccos (le_trans (by norm_num) (div_nonneg (norm_nonneg _) (norm_nonneg _)))
                      (div_le_one_of_le _ (norm_nonneg _))],
  rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _),
      norm_add_sq_eq_norm_sq_add_norm_sq_real h],
  exact le_add_of_nonneg_right (mul_self_nonneg _)
end

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
lemma sin_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y ≠ 0) :
  real.sin (angle x (x + y)) = ‖y‖ / ‖x + y‖ :=
begin
  rw [angle_add_eq_arcsin_of_inner_eq_zero h h0,
      real.sin_arcsin (le_trans (by norm_num) (div_nonneg (norm_nonneg _) (norm_nonneg _)))
                      (div_le_one_of_le _ (norm_nonneg _))],
  rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _),
      norm_add_sq_eq_norm_sq_add_norm_sq_real h],
  exact le_add_of_nonneg_left (mul_self_nonneg _)
end

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
lemma tan_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
  real.tan (angle x (x + y)) = ‖y‖ / ‖x‖ :=
begin
  by_cases h0 : x = 0, { simp [h0] },
  rw [angle_add_eq_arctan_of_inner_eq_zero h h0, real.tan_arctan]
end

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
lemma cos_angle_add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
  real.cos (angle x (x + y)) * ‖x + y‖ = ‖x‖ :=
begin
  rw cos_angle_add_of_inner_eq_zero h,
  by_cases hxy : ‖x + y‖ = 0,
  { have h' := norm_add_sq_eq_norm_sq_add_norm_sq_real h,
    rw [hxy, zero_mul, eq_comm, add_eq_zero_iff' (mul_self_nonneg ‖x‖) (mul_self_nonneg ‖y‖),
        mul_self_eq_zero] at h',
    simp [h'.1] },
  { exact div_mul_cancel _ hxy }
end

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
lemma sin_angle_add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
  real.sin (angle x (x + y)) * ‖x + y‖ = ‖y‖ :=
begin
  by_cases h0 : x = 0 ∧ y = 0, { simp [h0] },
  rw not_and_distrib at h0,
  rw [sin_angle_add_of_inner_eq_zero h h0, div_mul_cancel],
  rw [←mul_self_ne_zero, norm_add_sq_eq_norm_sq_add_norm_sq_real h],
  refine (ne_of_lt _).symm,
  rcases h0 with h0 | h0,
  { exact left.add_pos_of_pos_of_nonneg (mul_self_pos.2 (norm_ne_zero_iff.2 h0))
                                        (mul_self_nonneg _) },
  { exact left.add_pos_of_nonneg_of_pos (mul_self_nonneg _)
                                        (mul_self_pos.2 (norm_ne_zero_iff.2 h0)) }
end

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
lemma tan_angle_add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y = 0) :
  real.tan (angle x (x + y)) * ‖x‖ = ‖y‖ :=
begin
  rw [tan_angle_add_of_inner_eq_zero h],
  rcases h0 with h0 | h0; simp [h0]
end

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
lemma norm_div_cos_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y = 0) :
  ‖x‖ / real.cos (angle x (x + y)) = ‖x + y‖ :=
begin
  rw cos_angle_add_of_inner_eq_zero h,
  rcases h0 with h0 | h0,
  { rw [div_div_eq_mul_div, mul_comm, div_eq_mul_inv,
        mul_inv_cancel_right₀ (norm_ne_zero_iff.2 h0)] },
  { simp [h0] }
end

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
lemma norm_div_sin_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y ≠ 0) :
  ‖y‖ / real.sin (angle x (x + y)) = ‖x + y‖ :=
begin
  rcases h0 with h0 | h0, { simp [h0] },
  rw [sin_angle_add_of_inner_eq_zero h (or.inr h0), div_div_eq_mul_div, mul_comm, div_eq_mul_inv,
        mul_inv_cancel_right₀ (norm_ne_zero_iff.2 h0)]
end

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
lemma norm_div_tan_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y ≠ 0) :
  ‖y‖ / real.tan (angle x (x + y)) = ‖x‖ :=
begin
  rw tan_angle_add_of_inner_eq_zero h,
  rcases h0 with h0 | h0,
  { simp [h0] },
  { rw [div_div_eq_mul_div, mul_comm, div_eq_mul_inv,
        mul_inv_cancel_right₀ (norm_ne_zero_iff.2 h0)] }
end

/-- An angle in a right-angled triangle expressed using `arccos`, version subtracting vectors. -/
lemma angle_sub_eq_arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
  angle x (x - y) = real.arccos (‖x‖ / ‖x - y‖) :=
begin
  rw [←neg_eq_zero, ←inner_neg_right] at h,
  rw [sub_eq_add_neg, angle_add_eq_arccos_of_inner_eq_zero h]
end

/-- An angle in a right-angled triangle expressed using `arcsin`, version subtracting vectors. -/
lemma angle_sub_eq_arcsin_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y ≠ 0) :
  angle x (x - y) = real.arcsin (‖y‖ / ‖x - y‖) :=
begin
  rw [←neg_eq_zero, ←inner_neg_right] at h,
  nth_rewrite 1 ←neg_ne_zero at h0,
  rw [sub_eq_add_neg, angle_add_eq_arcsin_of_inner_eq_zero h h0, norm_neg]
end

/-- An angle in a right-angled triangle expressed using `arctan`, version subtracting vectors. -/
lemma angle_sub_eq_arctan_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0) :
  angle x (x - y) = real.arctan (‖y‖ / ‖x‖) :=
begin
  rw [←neg_eq_zero, ←inner_neg_right] at h,
  rw [sub_eq_add_neg, angle_add_eq_arctan_of_inner_eq_zero h h0, norm_neg]
end

/-- An angle in a non-degenerate right-angled triangle is positive, version subtracting
vectors. -/
lemma angle_sub_pos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y ≠ 0) :
  0 < angle x (x - y) :=
begin
  rw [←neg_eq_zero, ←inner_neg_right] at h,
  rw ←neg_ne_zero at h0,
  rw sub_eq_add_neg,
  exact angle_add_pos_of_inner_eq_zero h h0
end

/-- An angle in a right-angled triangle is at most `π / 2`, version subtracting vectors. -/
lemma angle_sub_le_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
  angle x (x - y) ≤ π / 2 :=
begin
  rw [←neg_eq_zero, ←inner_neg_right] at h,
  rw sub_eq_add_neg,
  exact angle_add_le_pi_div_two_of_inner_eq_zero h
end

/-- An angle in a non-degenerate right-angled triangle is less than `π / 2`, version subtracting
vectors. -/
lemma angle_sub_lt_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0) :
  angle x (x - y) < π / 2 :=
begin
  rw [←neg_eq_zero, ←inner_neg_right] at h,
  rw sub_eq_add_neg,
  exact angle_add_lt_pi_div_two_of_inner_eq_zero h h0
end

/-- The cosine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
lemma cos_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
  real.cos (angle x (x - y)) = ‖x‖ / ‖x - y‖ :=
begin
  rw [←neg_eq_zero, ←inner_neg_right] at h,
  rw [sub_eq_add_neg, cos_angle_add_of_inner_eq_zero h]
end

/-- The sine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
lemma sin_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y ≠ 0) :
  real.sin (angle x (x - y)) = ‖y‖ / ‖x - y‖ :=
begin
  rw [←neg_eq_zero, ←inner_neg_right] at h,
  nth_rewrite 1 ←neg_ne_zero at h0,
  rw [sub_eq_add_neg, sin_angle_add_of_inner_eq_zero h h0, norm_neg]
end

/-- The tangent of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
lemma tan_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
  real.tan (angle x (x - y)) = ‖y‖ / ‖x‖ :=
begin
  rw [←neg_eq_zero, ←inner_neg_right] at h,
  rw [sub_eq_add_neg, tan_angle_add_of_inner_eq_zero h, norm_neg]
end

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side, version subtracting vectors. -/
lemma cos_angle_sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
  real.cos (angle x (x - y)) * ‖x - y‖ = ‖x‖ :=
begin
  rw [←neg_eq_zero, ←inner_neg_right] at h,
  rw [sub_eq_add_neg, cos_angle_add_mul_norm_of_inner_eq_zero h]
end

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side, version subtracting vectors. -/
lemma sin_angle_sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
  real.sin (angle x (x - y)) * ‖x - y‖ = ‖y‖ :=
begin
  rw [←neg_eq_zero, ←inner_neg_right] at h,
  rw [sub_eq_add_neg, sin_angle_add_mul_norm_of_inner_eq_zero h, norm_neg]
end

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side, version subtracting vectors. -/
lemma tan_angle_sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y = 0) :
  real.tan (angle x (x - y)) * ‖x‖ = ‖y‖ :=
begin
  rw [←neg_eq_zero, ←inner_neg_right] at h,
  rw ←neg_eq_zero at h0,
  rw [sub_eq_add_neg, tan_angle_add_mul_norm_of_inner_eq_zero h h0, norm_neg]
end

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse, version subtracting vectors. -/
lemma norm_div_cos_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y = 0) :
  ‖x‖ / real.cos (angle x (x - y)) = ‖x - y‖ :=
begin
  rw [←neg_eq_zero, ←inner_neg_right] at h,
  rw ←neg_eq_zero at h0,
  rw [sub_eq_add_neg, norm_div_cos_angle_add_of_inner_eq_zero h h0]
end

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse, version subtracting vectors. -/
lemma norm_div_sin_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y ≠ 0) :
  ‖y‖ / real.sin (angle x (x - y)) = ‖x - y‖ :=
begin
  rw [←neg_eq_zero, ←inner_neg_right] at h,
  rw ←neg_ne_zero at h0,
  rw [sub_eq_add_neg, ←norm_neg, norm_div_sin_angle_add_of_inner_eq_zero h h0]
end

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side, version subtracting vectors. -/
lemma norm_div_tan_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y ≠ 0) :
  ‖y‖ / real.tan (angle x (x - y)) = ‖x‖ :=
begin
  rw [←neg_eq_zero, ←inner_neg_right] at h,
  rw ←neg_ne_zero at h0,
  rw [sub_eq_add_neg, ←norm_neg, norm_div_tan_angle_add_of_inner_eq_zero h h0]
end

end inner_product_geometry

namespace euclidean_geometry

open inner_product_geometry

variables {V : Type*} {P : Type*}
  [normed_add_comm_group V] [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P]
include V

/-- **Pythagorean theorem**, if-and-only-if angle-at-point form. -/
lemma dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two (p1 p2 p3 : P) :
  dist p1 p3 * dist p1 p3 = dist p1 p2 * dist p1 p2 + dist p3 p2 * dist p3 p2 ↔
    ∠ p1 p2 p3 = π / 2 :=
by erw [dist_comm p3 p2, dist_eq_norm_vsub V p1 p3, dist_eq_norm_vsub V p1 p2,
        dist_eq_norm_vsub V p2 p3,
        ←norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two,
        vsub_sub_vsub_cancel_right p1, ←neg_vsub_eq_vsub_rev p2 p3, norm_neg]

/-- An angle in a right-angled triangle expressed using `arccos`. -/
lemma angle_eq_arccos_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
  ∠ p₂ p₃ p₁ = real.arccos (dist p₃ p₂ / dist p₁ p₃) :=
begin
  rw [angle, ←inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ←neg_eq_zero,
      ←inner_neg_left, neg_vsub_eq_vsub_rev] at h,
  rw [angle, dist_eq_norm_vsub' V p₃ p₂, dist_eq_norm_vsub V p₁ p₃,
      ←vsub_add_vsub_cancel p₁ p₂ p₃, add_comm, angle_add_eq_arccos_of_inner_eq_zero h]
end

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
lemma angle_eq_arcsin_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  (h0 : p₁ ≠ p₂ ∨ p₃ ≠ p₂) : ∠ p₂ p₃ p₁ = real.arcsin (dist p₁ p₂ / dist p₁ p₃) :=
begin
  rw [angle, ←inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ←neg_eq_zero,
      ←inner_neg_left, neg_vsub_eq_vsub_rev] at h,
  rw [←@vsub_ne_zero V, @ne_comm _ p₃, ←@vsub_ne_zero V _ _ _ p₂, or_comm] at h0,
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃,
      ←vsub_add_vsub_cancel p₁ p₂ p₃, add_comm, angle_add_eq_arcsin_of_inner_eq_zero h h0]
end

/-- An angle in a right-angled triangle expressed using `arctan`. -/
lemma angle_eq_arctan_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  (h0 : p₃ ≠ p₂) : ∠ p₂ p₃ p₁ = real.arctan (dist p₁ p₂ / dist p₃ p₂) :=
begin
  rw [angle, ←inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ←neg_eq_zero,
      ←inner_neg_left, neg_vsub_eq_vsub_rev] at h,
  rw [ne_comm, ←@vsub_ne_zero V] at h0,
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub' V p₃ p₂,
      ←vsub_add_vsub_cancel p₁ p₂ p₃, add_comm, angle_add_eq_arctan_of_inner_eq_zero h h0]
end

/-- An angle in a non-degenerate right-angled triangle is positive. -/
lemma angle_pos_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  (h0 : p₁ ≠ p₂ ∨ p₃ = p₂) : 0 < ∠ p₂ p₃ p₁ :=
begin
  rw [angle, ←inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ←neg_eq_zero,
      ←inner_neg_left, neg_vsub_eq_vsub_rev] at h,
  rw [←@vsub_ne_zero V, eq_comm, ←@vsub_eq_zero_iff_eq V, or_comm] at h0,
  rw [angle, ←vsub_add_vsub_cancel p₁ p₂ p₃, add_comm],
  exact angle_add_pos_of_inner_eq_zero h h0
end

/-- An angle in a right-angled triangle is at most `π / 2`. -/
lemma angle_le_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
  ∠ p₂ p₃ p₁ ≤ π / 2 :=
begin
  rw [angle, ←inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ←neg_eq_zero,
      ←inner_neg_left, neg_vsub_eq_vsub_rev] at h,
  rw [angle, ←vsub_add_vsub_cancel p₁ p₂ p₃, add_comm],
  exact angle_add_le_pi_div_two_of_inner_eq_zero h
end

/-- An angle in a non-degenerate right-angled triangle is less than `π / 2`. -/
lemma angle_lt_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  (h0 : p₃ ≠ p₂) : ∠ p₂ p₃ p₁ < π / 2 :=
begin
  rw [angle, ←inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ←neg_eq_zero,
      ←inner_neg_left, neg_vsub_eq_vsub_rev] at h,
  rw [ne_comm, ←@vsub_ne_zero V] at h0,
  rw [angle, ←vsub_add_vsub_cancel p₁ p₂ p₃, add_comm],
  exact angle_add_lt_pi_div_two_of_inner_eq_zero h h0
end

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
lemma cos_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
  real.cos (∠ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₃ :=
begin
  rw [angle, ←inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ←neg_eq_zero,
      ←inner_neg_left, neg_vsub_eq_vsub_rev] at h,
  rw [angle, dist_eq_norm_vsub' V p₃ p₂, dist_eq_norm_vsub V p₁ p₃,
      ←vsub_add_vsub_cancel p₁ p₂ p₃, add_comm, cos_angle_add_of_inner_eq_zero h]
end

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
lemma sin_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  (h0 : p₁ ≠ p₂ ∨ p₃ ≠ p₂) : real.sin (∠ p₂ p₃ p₁) = dist p₁ p₂ / dist p₁ p₃ :=
begin
  rw [angle, ←inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ←neg_eq_zero,
      ←inner_neg_left, neg_vsub_eq_vsub_rev] at h,
  rw [←@vsub_ne_zero V, @ne_comm _ p₃, ←@vsub_ne_zero V _ _ _ p₂, or_comm] at h0,
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃,
      ←vsub_add_vsub_cancel p₁ p₂ p₃, add_comm, sin_angle_add_of_inner_eq_zero h h0]
end

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
lemma tan_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
  real.tan (∠ p₂ p₃ p₁) = dist p₁ p₂ / dist p₃ p₂ :=
begin
  rw [angle, ←inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ←neg_eq_zero,
      ←inner_neg_left, neg_vsub_eq_vsub_rev] at h,
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub' V p₃ p₂,
      ←vsub_add_vsub_cancel p₁ p₂ p₃, add_comm, tan_angle_add_of_inner_eq_zero h]
end

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
lemma cos_angle_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
  real.cos (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₃ p₂ :=
begin
  rw [angle, ←inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ←neg_eq_zero,
      ←inner_neg_left, neg_vsub_eq_vsub_rev] at h,
  rw [angle, dist_eq_norm_vsub' V p₃ p₂, dist_eq_norm_vsub V p₁ p₃,
      ←vsub_add_vsub_cancel p₁ p₂ p₃, add_comm, cos_angle_add_mul_norm_of_inner_eq_zero h]
end

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
lemma sin_angle_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
  real.sin (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₁ p₂ :=
begin
  rw [angle, ←inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ←neg_eq_zero,
      ←inner_neg_left, neg_vsub_eq_vsub_rev] at h,
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃,
      ←vsub_add_vsub_cancel p₁ p₂ p₃, add_comm, sin_angle_add_mul_norm_of_inner_eq_zero h]
end

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
lemma tan_angle_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  (h0 : p₁ = p₂ ∨ p₃ ≠ p₂) : real.tan (∠ p₂ p₃ p₁) * dist p₃ p₂ = dist p₁ p₂ :=
begin
  rw [angle, ←inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ←neg_eq_zero,
      ←inner_neg_left, neg_vsub_eq_vsub_rev] at h,
  rw [ne_comm, ←@vsub_ne_zero V, ←@vsub_eq_zero_iff_eq V, or_comm] at h0,
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub' V p₃ p₂,
      ←vsub_add_vsub_cancel p₁ p₂ p₃, add_comm, tan_angle_add_mul_norm_of_inner_eq_zero h h0]
end

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
lemma dist_div_cos_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  (h0 : p₁ = p₂ ∨ p₃ ≠ p₂) : dist p₃ p₂ / real.cos (∠ p₂ p₃ p₁) = dist p₁ p₃ :=
begin
  rw [angle, ←inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ←neg_eq_zero,
      ←inner_neg_left, neg_vsub_eq_vsub_rev] at h,
  rw [ne_comm, ←@vsub_ne_zero V, ←@vsub_eq_zero_iff_eq V, or_comm] at h0,
  rw [angle, dist_eq_norm_vsub' V p₃ p₂, dist_eq_norm_vsub V p₁ p₃,
      ←vsub_add_vsub_cancel p₁ p₂ p₃, add_comm, norm_div_cos_angle_add_of_inner_eq_zero h h0]
end

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
lemma dist_div_sin_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  (h0 : p₁ ≠ p₂ ∨ p₃ = p₂) : dist p₁ p₂ / real.sin (∠ p₂ p₃ p₁) = dist p₁ p₃ :=
begin
  rw [angle, ←inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ←neg_eq_zero,
      ←inner_neg_left, neg_vsub_eq_vsub_rev] at h,
  rw [eq_comm, ←@vsub_ne_zero V, ←@vsub_eq_zero_iff_eq V, or_comm] at h0,
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃,
      ←vsub_add_vsub_cancel p₁ p₂ p₃, add_comm, norm_div_sin_angle_add_of_inner_eq_zero h h0]
end

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
lemma dist_div_tan_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
  (h0 : p₁ ≠ p₂ ∨ p₃ = p₂) : dist p₁ p₂ / real.tan (∠ p₂ p₃ p₁) = dist p₃ p₂ :=
begin
  rw [angle, ←inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ←neg_eq_zero,
      ←inner_neg_left, neg_vsub_eq_vsub_rev] at h,
  rw [eq_comm, ←@vsub_ne_zero V, ←@vsub_eq_zero_iff_eq V, or_comm] at h0,
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub' V p₃ p₂,
      ←vsub_add_vsub_cancel p₁ p₂ p₃, add_comm, norm_div_tan_angle_add_of_inner_eq_zero h h0]
end

end euclidean_geometry
