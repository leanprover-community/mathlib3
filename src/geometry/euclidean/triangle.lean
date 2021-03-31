/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import geometry.euclidean.basic
import tactic.interval_cases

noncomputable theory
open_locale big_operators
open_locale classical
open_locale real
open_locale real_inner_product_space
open_locale nnreal
open_locale ennreal

set_option pp.coercions true
/-!
# Triangles

This file proves basic geometrical results about distances and angles
in (possibly degenerate) triangles in real inner product spaces and
Euclidean affine spaces.  More specialized results, and results
developed for simplices in general rather than just for triangles, are
in separate files.  Definitions and results that make sense in more
general affine spaces rather than just in the Euclidean case go under
`linear_algebra.affine_space`.

## Implementation notes

Results in this file are generally given in a form with only those
non-degeneracy conditions needed for the particular result, rather
than requiring affine independence of the points of a triangle
unnecessarily.

## References

* https://en.wikipedia.org/wiki/Pythagorean_theorem
* https://en.wikipedia.org/wiki/Law_of_cosines
* https://en.wikipedia.org/wiki/Pons_asinorum
* https://en.wikipedia.org/wiki/Sum_of_angles_of_a_triangle

-/

namespace inner_product_geometry
/-!
### Geometrical results on triangles in real inner product spaces

This section develops some results on (possibly degenerate) triangles
in real inner product spaces, where those definitions and results can
most conveniently be developed in terms of vectors and then used to
deduce corresponding results for Euclidean affine spaces.
-/

variables {V : Type*} [inner_product_space ℝ V]

/-- Pythagorean theorem, if-and-only-if vector angle form. -/
lemma norm_add_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two (x y : V) :
  ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ ↔ angle x y = π / 2 :=
begin
  rw norm_add_square_eq_norm_square_add_norm_square_iff_real_inner_eq_zero,
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y
end

/-- Pythagorean theorem, vector angle form. -/
lemma norm_add_square_eq_norm_square_add_norm_square' (x y : V) (h : angle x y = π / 2) :
  ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ :=
(norm_add_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two x y).2 h

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector angle form. -/
lemma norm_sub_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two (x y : V) :
  ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ ↔ angle x y = π / 2 :=
begin
  rw norm_sub_square_eq_norm_square_add_norm_square_iff_real_inner_eq_zero,
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y
end

/-- Pythagorean theorem, subtracting vectors, vector angle form. -/
lemma norm_sub_square_eq_norm_square_add_norm_square' (x y : V) (h : angle x y = π / 2) :
  ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ :=
(norm_sub_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two x y).2 h

/-- Law of cosines (cosine rule), vector angle form. -/
lemma norm_sub_square_eq_norm_square_add_norm_square_sub_two_mul_norm_mul_norm_mul_cos_angle
    (x y : V) :
  ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ - 2 * ∥x∥ * ∥y∥ * real.cos (angle x y) :=
by rw [(show 2 * ∥x∥ * ∥y∥ * real.cos (angle x y) =
             2 * (real.cos (angle x y) * (∥x∥ * ∥y∥)), by ring),
       cos_angle_mul_norm_mul_norm, ←real_inner_self_eq_norm_square,
       ←real_inner_self_eq_norm_square, ←real_inner_self_eq_norm_square, real_inner_sub_sub_self,
       sub_add_eq_add_sub]

/-- Pons asinorum, vector angle form. -/
lemma angle_sub_eq_angle_sub_rev_of_norm_eq {x y : V} (h : ∥x∥ = ∥y∥) :
  angle x (x - y) = angle y (y - x) :=
begin
  refine real.inj_on_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ⟨angle_nonneg _ _, angle_le_pi _ _⟩ _,
  rw [cos_angle, cos_angle, h, ←neg_sub, norm_neg, neg_sub,
    inner_sub_right, inner_sub_right, real_inner_self_eq_norm_square,
    real_inner_self_eq_norm_square, h, real_inner_comm x y]
end

/-- Converse of pons asinorum, vector angle form. -/
lemma norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi {x y : V}
    (h : angle x (x - y) = angle y (y - x)) (hpi : angle x y ≠ π) : ∥x∥ = ∥y∥ :=
begin
  replace h := real.arccos_inj_on
    (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x (x - y)))
    (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one y (y - x))) h,
  by_cases hxy : x = y,
  { rw hxy },
  { rw [←norm_neg (y - x), neg_sub, mul_comm, mul_comm ∥y∥, div_eq_mul_inv, div_eq_mul_inv,
        mul_inv_rev', mul_inv_rev', ←mul_assoc, ←mul_assoc] at h,
    replace h :=
      mul_right_cancel' (inv_ne_zero (λ hz, hxy (eq_of_sub_eq_zero (norm_eq_zero.1 hz)))) h,
    rw [inner_sub_right, inner_sub_right, real_inner_comm x y, real_inner_self_eq_norm_square,
        real_inner_self_eq_norm_square, mul_sub_right_distrib, mul_sub_right_distrib,
        mul_self_mul_inv, mul_self_mul_inv, sub_eq_sub_iff_sub_eq_sub,
        ←mul_sub_left_distrib] at h,
    by_cases hx0 : x = 0,
    { rw [hx0, norm_zero, inner_zero_left, zero_mul, zero_sub, neg_eq_zero] at h,
      rw [hx0, norm_zero, h] },
    { by_cases hy0 : y = 0,
      { rw [hy0, norm_zero, inner_zero_right, zero_mul, sub_zero] at h,
        rw [hy0, norm_zero, h] },
      { rw [inv_sub_inv (λ hz, hx0 (norm_eq_zero.1 hz)) (λ hz, hy0 (norm_eq_zero.1 hz)),
            ←neg_sub, ←mul_div_assoc, mul_comm, mul_div_assoc, ←mul_neg_one] at h,
        symmetry,
        by_contradiction hyx,
        replace h := (mul_left_cancel' (sub_ne_zero_of_ne hyx) h).symm,
        rw [real_inner_div_norm_mul_norm_eq_neg_one_iff, ←angle_eq_pi_iff] at h,
        exact hpi h } } }
end

/-- The cosine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
lemma cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  real.cos (angle x (x - y) + angle y (y - x)) = -real.cos (angle x y) :=
begin
  by_cases hxy : x = y,
  { rw [hxy, angle_self hy],
    simp },
  { rw [real.cos_add, cos_angle, cos_angle, cos_angle],
    have hxn : ∥x∥ ≠ 0 := (λ h, hx (norm_eq_zero.1 h)),
    have hyn : ∥y∥ ≠ 0 := (λ h, hy (norm_eq_zero.1 h)),
    have hxyn : ∥x - y∥ ≠ 0 := (λ h, hxy (eq_of_sub_eq_zero (norm_eq_zero.1 h))),
    apply mul_right_cancel' hxn,
    apply mul_right_cancel' hyn,
    apply mul_right_cancel' hxyn,
    apply mul_right_cancel' hxyn,
    have H1 : real.sin (angle x (x - y)) * real.sin (angle y (y - x)) *
                ∥x∥ * ∥y∥ * ∥x - y∥ * ∥x - y∥ =
              (real.sin (angle x (x - y)) * (∥x∥ * ∥x - y∥)) *
                (real.sin (angle y (y - x)) * (∥y∥ * ∥x - y∥)), { ring },
    have H2 : ⟪x, x⟫ * (inner x x - inner x y - (inner x y - inner y y)) -
                (inner x x - inner x y) * (inner x x - inner x y) =
              inner x x * inner y y - inner x y * inner x y, { ring },
    have H3 : ⟪y, y⟫ * (inner y y - inner x y - (inner x y - inner x x)) -
                (inner y y - inner x y) * (inner y y - inner x y) =
              inner x x * inner y y - inner x y * inner x y, { ring },
    rw [mul_sub_right_distrib, mul_sub_right_distrib, mul_sub_right_distrib,
        mul_sub_right_distrib, H1, sin_angle_mul_norm_mul_norm, norm_sub_rev x y,
        sin_angle_mul_norm_mul_norm, norm_sub_rev y x, inner_sub_left, inner_sub_left,
        inner_sub_right, inner_sub_right, inner_sub_right, inner_sub_right, real_inner_comm x y, H2,
        H3, real.mul_self_sqrt (sub_nonneg_of_le (real_inner_mul_inner_self_le x y)),
        real_inner_self_eq_norm_square, real_inner_self_eq_norm_square,
        real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two],
    field_simp [hxn, hyn, hxyn],
    ring }
end

/-- The sine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
lemma sin_angle_sub_add_angle_sub_rev_eq_sin_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  real.sin (angle x (x - y) + angle y (y - x)) = real.sin (angle x y) :=
begin
  by_cases hxy : x = y,
  { rw [hxy, angle_self hy],
    simp },
  { rw [real.sin_add, cos_angle, cos_angle],
    have hxn : ∥x∥ ≠ 0 := (λ h, hx (norm_eq_zero.1 h)),
    have hyn : ∥y∥ ≠ 0 := (λ h, hy (norm_eq_zero.1 h)),
    have hxyn : ∥x - y∥ ≠ 0 := (λ h, hxy (eq_of_sub_eq_zero (norm_eq_zero.1 h))),
    apply mul_right_cancel' hxn,
    apply mul_right_cancel' hyn,
    apply mul_right_cancel' hxyn,
    apply mul_right_cancel' hxyn,
    have H1 : real.sin (angle x (x - y)) * (⟪y, y - x⟫ / (∥y∥ * ∥y - x∥)) * ∥x∥ * ∥y∥ * ∥x - y∥ =
                real.sin (angle x (x - y)) * (∥x∥ * ∥x - y∥) *
                  (⟪y, y - x⟫ / (∥y∥ * ∥y - x∥)) * ∥y∥, { ring },
    have H2 : ⟪x, x - y⟫ / (∥x∥ * ∥y - x∥) * real.sin (angle y (y - x)) * ∥x∥ * ∥y∥ * ∥y - x∥ =
                ⟪x, x - y⟫ / (∥x∥ * ∥y - x∥) *
                  (real.sin (angle y (y - x)) * (∥y∥ * ∥y - x∥)) * ∥x∥, { ring },
    have H3 : ⟪x, x⟫ * (⟪x, x⟫ - ⟪x, y⟫ - (⟪x, y⟫ - ⟪y, y⟫)) -
                (⟪x, x⟫ - ⟪x, y⟫) * (⟪x, x⟫ - ⟪x, y⟫) =
              ⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫, { ring },
    have H4 : ⟪y, y⟫ * (⟪y, y⟫ - ⟪x, y⟫ - (⟪x, y⟫ - ⟪x, x⟫)) -
                (⟪y, y⟫ - ⟪x, y⟫) * (⟪y, y⟫ - ⟪x, y⟫) =
              ⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫  * ⟪x, y⟫, { ring },
    rw [right_distrib, right_distrib, right_distrib, right_distrib, H1,
        sin_angle_mul_norm_mul_norm, norm_sub_rev x y, H2, sin_angle_mul_norm_mul_norm,
        norm_sub_rev y x, mul_assoc (real.sin (angle x y)), sin_angle_mul_norm_mul_norm,
        inner_sub_left, inner_sub_left, inner_sub_right, inner_sub_right, inner_sub_right,
        inner_sub_right, real_inner_comm x y, H3, H4, real_inner_self_eq_norm_square,
        real_inner_self_eq_norm_square,
        real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two],
    field_simp [hxn, hyn, hxyn],
    ring }
end

/-- The cosine of the sum of the angles of a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
lemma cos_angle_add_angle_sub_add_angle_sub_eq_neg_one {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  real.cos (angle x y + angle x (x - y) + angle y (y - x)) = -1 :=
by rw [add_assoc, real.cos_add, cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle hx hy,
       sin_angle_sub_add_angle_sub_rev_eq_sin_angle hx hy, ←neg_mul_eq_mul_neg, ←neg_add',
       add_comm, ←pow_two, ←pow_two, real.sin_sq_add_cos_sq]

/-- The sine of the sum of the angles of a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
lemma sin_angle_add_angle_sub_add_angle_sub_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  real.sin (angle x y + angle x (x - y) + angle y (y - x)) = 0 :=
begin
  rw [add_assoc, real.sin_add, cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle hx hy,
      sin_angle_sub_add_angle_sub_rev_eq_sin_angle hx hy],
  ring
end

/-- The sum of the angles of a possibly degenerate triangle (where the
two given sides are nonzero), vector angle form. -/
lemma angle_add_angle_sub_add_angle_sub_eq_pi {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  angle x y + angle x (x - y) + angle y (y - x) = π :=
begin
  have hcos := cos_angle_add_angle_sub_add_angle_sub_eq_neg_one hx hy,
  have hsin := sin_angle_add_angle_sub_add_angle_sub_eq_zero hx hy,
  rw real.sin_eq_zero_iff at hsin,
  cases hsin with n hn,
  symmetry' at hn,
  have h0 : 0 ≤ angle x y + angle x (x - y) + angle y (y - x) :=
    add_nonneg (add_nonneg (angle_nonneg _ _) (angle_nonneg _ _)) (angle_nonneg _ _),
  have h3 : angle x y + angle x (x - y) + angle y (y - x) ≤ π + π + π :=
    add_le_add (add_le_add (angle_le_pi _ _) (angle_le_pi _ _)) (angle_le_pi _ _),
  have h3lt : angle x y + angle x (x - y) + angle y (y - x) < π + π + π,
  { by_contradiction hnlt,
    have hxy : angle x y = π,
    { by_contradiction hxy,
      exact hnlt (add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le
                                           (lt_of_le_of_ne (angle_le_pi _ _) hxy)
                                         (angle_le_pi _ _)) (angle_le_pi _ _)) },
    rw hxy at hnlt,
    rw angle_eq_pi_iff at hxy,
    rcases hxy with ⟨hx, ⟨r, ⟨hr, hxr⟩⟩⟩,
    rw [hxr, ←one_smul ℝ x, ←mul_smul, mul_one, ←sub_smul, one_smul, sub_eq_add_neg,
        angle_smul_right_of_pos _ _ (add_pos zero_lt_one (neg_pos_of_neg hr)), angle_self hx,
        add_zero] at hnlt,
    apply hnlt,
    rw add_assoc,
    exact add_lt_add_left (lt_of_le_of_lt (angle_le_pi _ _)
                                          (lt_add_of_pos_right π real.pi_pos)) _ },
  have hn0 : 0 ≤ n,
  { rw [hn, mul_nonneg_iff_right_nonneg_of_pos real.pi_pos] at h0,
    norm_cast at h0,
    exact h0 },
  have hn3 : n < 3,
  { rw [hn, (show π + π + π = 3 * π, by ring)] at h3lt,
    replace h3lt := lt_of_mul_lt_mul_right h3lt (le_of_lt real.pi_pos),
    norm_cast at h3lt,
    exact h3lt },
  interval_cases n,
  { rw hn at hcos,
    simp at hcos,
    norm_num at hcos },
  { rw hn,
    norm_num },
  { rw hn at hcos,
    simp at hcos,
    norm_num at hcos },
end

end inner_product_geometry

namespace euclidean_geometry
/-!
### Geometrical results on triangles in Euclidean affine spaces

This section develops some geometrical definitions and results on
(possible degenerate) triangles in Euclidean affine spaces.
-/
open inner_product_geometry

open_locale euclidean_geometry

variables {V : Type*} {P : Type*} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P]
include V

/-- Pythagorean theorem, if-and-only-if angle-at-point form. -/
lemma dist_square_eq_dist_square_add_dist_square_iff_angle_eq_pi_div_two (p1 p2 p3 : P) :
  dist p1 p3 * dist p1 p3 = dist p1 p2 * dist p1 p2 + dist p3 p2 * dist p3 p2 ↔
    ∠ p1 p2 p3 = π / 2 :=
by erw [pseudo_metric_space.dist_comm p3 p2, dist_eq_norm_vsub V p1 p3, dist_eq_norm_vsub V p1 p2,
        dist_eq_norm_vsub V p2 p3,
        ←norm_sub_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two,
        vsub_sub_vsub_cancel_right p1, ←neg_vsub_eq_vsub_rev p2 p3, norm_neg]

/-- Law of cosines (cosine rule), angle-at-point form. -/
lemma dist_square_eq_dist_square_add_dist_square_sub_two_mul_dist_mul_dist_mul_cos_angle
    (p1 p2 p3 : P) :
  dist p1 p3 * dist p1 p3 =
    dist p1 p2 * dist p1 p2 + dist p3 p2 * dist p3 p2 -
      2 * dist p1 p2 * dist p3 p2 * real.cos (∠ p1 p2 p3) :=
begin
  rw [dist_eq_norm_vsub V p1 p3, dist_eq_norm_vsub V p1 p2, dist_eq_norm_vsub V p3 p2],
  unfold angle,
  convert norm_sub_square_eq_norm_square_add_norm_square_sub_two_mul_norm_mul_norm_mul_cos_angle
          (p1 -ᵥ p2 : V) (p3 -ᵥ p2 : V),
  { exact (vsub_sub_vsub_cancel_right p1 p3 p2).symm },
  { exact (vsub_sub_vsub_cancel_right p1 p3 p2).symm }
end

/-- Pons asinorum, angle-at-point form. -/
lemma angle_eq_angle_of_dist_eq {p1 p2 p3 : P} (h : dist p1 p2 = dist p1 p3) :
  ∠ p1 p2 p3 = ∠ p1 p3 p2 :=
begin
  rw [dist_eq_norm_vsub V p1 p2, dist_eq_norm_vsub V p1 p3] at h,
  unfold angle,
  convert angle_sub_eq_angle_sub_rev_of_norm_eq h,
  { exact (vsub_sub_vsub_cancel_left p3 p2 p1).symm },
  { exact (vsub_sub_vsub_cancel_left p2 p3 p1).symm }
end

/-- Converse of pons asinorum, angle-at-point form. -/
lemma dist_eq_of_angle_eq_angle_of_angle_ne_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = ∠ p1 p3 p2)
    (hpi : ∠ p2 p1 p3 ≠ π) : dist p1 p2 = dist p1 p3 :=
begin
  unfold angle at h hpi,
  rw [dist_eq_norm_vsub V p1 p2, dist_eq_norm_vsub V p1 p3],
  rw [←angle_neg_neg, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] at hpi,
  rw [←vsub_sub_vsub_cancel_left p3 p2 p1, ←vsub_sub_vsub_cancel_left p2 p3 p1] at h,
  exact norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi h hpi
end

/-- The sum of the angles of a possibly degenerate triangle (where the
given vertex is distinct from the others), angle-at-point. -/
lemma angle_add_angle_add_angle_eq_pi {p1 p2 p3 : P} (h2 : p2 ≠ p1) (h3 : p3 ≠ p1) :
  ∠ p1 p2 p3 + ∠ p2 p3 p1 + ∠ p3 p1 p2 = π :=
begin
  rw [add_assoc, add_comm, add_comm (∠ p2 p3 p1), angle_comm p2 p3 p1],
  unfold angle,
  rw [←angle_neg_neg (p1 -ᵥ p3), ←angle_neg_neg (p1 -ᵥ p2), neg_vsub_eq_vsub_rev,
      neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev,
      ←vsub_sub_vsub_cancel_right p3 p2 p1, ←vsub_sub_vsub_cancel_right p2 p3 p1],
  exact angle_add_angle_sub_add_angle_sub_eq_pi (λ he, h3 (vsub_eq_zero_iff_eq.1 he))
                                                (λ he, h2 (vsub_eq_zero_iff_eq.1 he))
end

lemma sin_eq_sqrt_one_minus_cos_sq (x : ℝ) (hl : x ≥ 0) (hu : x ≤ π) :
  real.sin x = real.sqrt (1 - (real.cos x)^2) :=
begin
  rw ← real.sqrt_sqr (real.sin_nonneg_of_nonneg_of_le_pi hl hu),
  exact congr_arg real.sqrt (real.sin_square x),
end

lemma rearrange_cos_rule (a b c d : ℝ) (a_nonzero : a ≠ 0) (b_nonzero : b ≠ 0):
  c * c = a * a + b * b - 2 * a * b * d →
    d = (a * a + b * b - c * c) / (2 * a * b) :=
begin
  intro hyp,
  simp *,
  field_simp,
  ring,
end

lemma heron {p1 p2 p3 : P} (h2 : p1 ≠ p2) (h3 : p1 ≠ p3) (h4 : p3 ≠ p2) :
  (1/2) * dist p1 p2 * dist p3 p2 * real.sin (∠ p1 p2 p3) =
    real.sqrt (
      ( ( (dist p1 p2) + (dist p1 p3) + (dist p3 p2) ) / 2 ) *
      ( ( ( (dist p1 p2) + (dist p1 p3) + (dist p3 p2) ) / 2 ) - ( dist p1 p2 ) ) *
      ( ( ( (dist p1 p2) + (dist p1 p3) + (dist p3 p2) ) / 2 ) - ( dist p1 p3 ) ) *
      ( ( ( (dist p1 p2) + (dist p1 p3) + (dist p3 p2) ) / 2 ) - ( dist p3 p2 ) )
    ) :=
begin
  let a := dist p1 p2,
  let b := dist p3 p2,
  let c := dist p1 p3,
  let γ := ∠ p1 p2 p3,

  have a_nonzero : a ≠ 0, exact ne_of_gt (dist_pos.mpr h2),
  have b_nonzero : b ≠ 0, exact ne_of_gt (dist_pos.mpr h4),
  have c_nonzero : c ≠ 0, exact ne_of_gt (dist_pos.mpr h3),

  have cos_rule_1 := dist_square_eq_dist_square_add_dist_square_sub_two_mul_dist_mul_dist_mul_cos_angle p1 p2 p3,
  have cos_rule_3 := rearrange_cos_rule a b c (real.cos γ) a_nonzero b_nonzero cos_rule_1,
  have sin_to_cos := sin_eq_sqrt_one_minus_cos_sq γ (angle_nonneg p1 p2 p3) (angle_le_pi p1 p2 p3),

  let s := (a + c + b) / 2,

  have ab2_pos : 0 ≤ (2 * a * b), by {
    have a_pos : 0 ≤ a, exact le_of_lt (dist_pos.mpr h2),
    have b_pos : 0 ≤ b, exact le_of_lt (dist_pos.mpr h4),
    have ab_pos : 0 ≤ a * b, exact mul_nonneg a_pos b_pos,
    linarith,
  },

  have sqrt_four_squared : real.sqrt (4^2) = 4, apply real.sqrt_sqr; linarith,

  have lemma1 :=
  calc 1 - real.cos γ ^ 2 = 1 - ((a*a + b*b - c*c) / (2*a*b)) ^ 2 : by rw cos_rule_3
  ... = 1 - (a*a + b*b - c*c)^2 / (2*a*b)^2 : by congr' ; exact div_pow (a*a + b*b - c*c) (2*a*b) 2
  ... = (((2*a*b)^2 - (a*a + b*b - c*c)^2) / (2*a*b)^2) : by field_simp
  ,
  have lemma2 : (((2*a*b)^2 - (a*a + b*b - c*c)^2) / (2*a*b)^2) ≥ 0, by
  calc (((2*a*b)^2 - (a*a + b*b - c*c)^2) / (2*a*b)^2) = 1 - real.cos γ ^ 2 : by rw ← lemma1
  ... ≥ 0 : by {
    have keyyy := real.cos_sq_le_one γ,
    linarith,
  },
  have lemma3 : ((2*a*b)^2 - (a*a + b*b - c*c)^2) ≥ 0, by {
    have denom_pos : (2*a*b)^2 ≥ 0, by {
      rw pow_two,
      exact mul_nonneg ab2_pos ab2_pos,
    },
    have flipit: 0 ≤ (((2*a*b)^2 - (a*a + b*b - c*c)^2)) / ((2*a*b)^2), exact lemma2,
    rw div_nonneg_iff at flipit,
    cases flipit,
    exact flipit.left,
    let clef := flipit.right,
    exfalso,
    have anotherc : (2*a*b)^2 = 0, by exact le_antisymm clef denom_pos ,
    rw pow_two at anotherc,
    field_simp at anotherc,
    exact anotherc,
  },

  have pen_lemma : 1/4 * real.sqrt ( (s * (s - a) * (s - c) * (s - b) * 4) * 4) =
  1/4 * real.sqrt ( s * (s - a) * (s - c) * (s - b) * 4) * real.sqrt (4), by {
    rw real.sqrt_mul' (s * (s - a) * (s - c) * (s - b) * 4) _,
    ring,
    linarith,
  },
  have lastlemma : 1/4 * real.sqrt ( s * (s - a) * (s - c) * (s - b) * 4^2) =
  1/4 * real.sqrt ( s * (s - a) * (s - c) * (s - b)) * real.sqrt (4^2), by {
    rw pow_two,
    have something : 1 / 4 * real.sqrt (s * (s - a) * (s - c) * (s - b) * (4 * 4))
      = 1 / 4 * real.sqrt (s * (s - a) * (s - c) * (s - b) * 4 * 4), by ring,
    rw something,
    rw pen_lemma,
    rw real.sqrt_mul' (s * (s - a) * (s - c) * (s - b)) _,
    have yetanother : 1 / 4 * (real.sqrt (s * (s - a) * (s - c) * (s - b)) * real.sqrt 4) * real.sqrt 4
      = 1 / 4 * (real.sqrt (s * (s - a) * (s - c) * (s - b))) * (real.sqrt 4 * real.sqrt 4), by ring,
    rw yetanother,
    rw ← real.sqrt_mul' _ _,
    linarith,
    linarith,
  },

  calc 1/2*a*b * real.sin γ = 1/2*a*b * real.sqrt (1 - real.cos γ ^ 2) : by rw sin_to_cos
    ... = 1/2*a*b * real.sqrt (1 - ((a*a + b*b - c*c) / (2*a*b)) ^ 2) : by rw cos_rule_3
    ... = 1/2*a*b * real.sqrt (1 - (a*a + b*b - c*c)^2 / (2*a*b)^2) : by congr' ; exact div_pow (a*a + b*b - c*c) (2*a*b) 2
    ... = 1/2*a*b * real.sqrt (((2*a*b)^2 - (a*a + b*b - c*c)^2) / (2*a*b)^2) : by field_simp
    ... = 1/2*a*b * real.sqrt ((2*a*b)^2 - (a*a + b*b - c*c)^2) / real.sqrt ((2*a*b)^2) : by {
      rw real.sqrt_div lemma3,
      ring,
    }
    ... = 1/2*a*b * real.sqrt ((2*a*b)^2 - (a*a + b*b - c*c)^2) / (2*a*b) : by rw real.sqrt_sqr ab2_pos
    ... = 1/4 * real.sqrt ((2*a*b)^2 - (a*a + b*b - c*c)^2) : by field_simp ; ring_nf
    ... = 1/4 * real.sqrt ( s * (s - a) * (s - c) * (s - b) * 4^2) : by field_simp ; ring_nf
    ... = 1/4 * real.sqrt ( s * (s - a) * (s - c) * (s - b)) * real.sqrt (4^2) : lastlemma  -- more nonzero shit: real.sqrt_mul' (s * (s - a) * (s - c) * (s - b)) (by linarith)
    ... = 1/4 * real.sqrt ( s * (s - a) * (s - c) * (s - b)) * 4 : by rw sqrt_four_squared
    ... = real.sqrt ( s * (s - a) * (s - c) * (s - b)) : by ring,

  -- What the crap is this?!
  exact V,
  exact _inst_1,
  exact V,
  exact _inst_1,

end

end euclidean_geometry
