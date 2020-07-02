/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import analysis.normed_space.real_inner_product
import analysis.normed_space.add_torsor
import linear_algebra.affine_space
import tactic.interval_cases

noncomputable theory
open_locale big_operators
open_locale classical
open_locale real

/-!
# Euclidean spaces

This file defines Euclidean affine spaces.

## Implementation notes

Rather than requiring Euclidean affine spaces to be finite-dimensional
(as in the definition on Wikipedia), this is specified only for those
theorems that need it.

## References

* https://en.wikipedia.org/wiki/Euclidean_space

-/

/-- A `euclidean_affine_space V P` is an affine space with points `P`
over an `inner_product_space V`. -/
abbreviation euclidean_affine_space (V : Type*) (P : Type*) [inner_product_space V]
    [metric_space P] :=
normed_add_torsor V P

example (n : Type*) [fintype n] : euclidean_affine_space (euclidean_space n) (euclidean_space n) :=
by apply_instance

namespace inner_product_geometry
/-!
### Geometrical results on real inner product spaces

This section develops some geometrical definitions and results on real
inner product spaces, where those definitions and results can most
conveniently be developed in terms of vectors and then used to deduce
corresponding results for Euclidean affine spaces.
-/

variables {V : Type*} [inner_product_space V]

/-- The undirected angle between two vectors. If either vector is 0,
this is π/2. -/
def angle (x y : V) : ℝ := real.arccos (inner x y / (∥x∥ * ∥y∥))

/-- The cosine of the angle between two vectors. -/
lemma cos_angle (x y : V) : real.cos (angle x y) = inner x y / (∥x∥ * ∥y∥) :=
real.cos_arccos (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).1
                (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).2

/-- The angle between two vectors does not depend on their order. -/
lemma angle_comm (x y : V) : angle x y = angle y x :=
begin
  unfold angle,
  rw [inner_comm, mul_comm]
end

/-- The angle between the negation of two vectors. -/
@[simp] lemma angle_neg_neg (x y : V) : angle (-x) (-y) = angle x y :=
begin
  unfold angle,
  rw [inner_neg_neg, norm_neg, norm_neg]
end

/-- The angle between two vectors is nonnegative. -/
lemma angle_nonneg (x y : V) : 0 ≤ angle x y :=
real.arccos_nonneg _

/-- The angle between two vectors is at most π. -/
lemma angle_le_pi (x y : V) : angle x y ≤ π :=
real.arccos_le_pi _

/-- The angle between a vector and the negation of another vector. -/
lemma angle_neg_right (x y : V) : angle x (-y) = π - angle x y :=
begin
  unfold angle,
  rw [←real.arccos_neg, norm_neg, inner_neg_right, neg_div]
end

/-- The angle between the negation of a vector and another vector. -/
lemma angle_neg_left (x y : V) : angle (-x) y = π - angle x y :=
by rw [←angle_neg_neg, neg_neg, angle_neg_right]

/-- The angle between the zero vector and a vector. -/
@[simp] lemma angle_zero_left (x : V) : angle 0 x = π / 2 :=
begin
  unfold angle,
  rw [inner_zero_left, zero_div, real.arccos_zero]
end

/-- The angle between a vector and the zero vector. -/
@[simp] lemma angle_zero_right (x : V) : angle x 0 = π / 2 :=
begin
  unfold angle,
  rw [inner_zero_right, zero_div, real.arccos_zero]
end

/-- The angle between a nonzero vector and itself. -/
@[simp] lemma angle_self {x : V} (hx : x ≠ 0) : angle x x = 0 :=
begin
  unfold angle,
  rw [←inner_self_eq_norm_square, div_self (λ h, hx (inner_self_eq_zero.1 h)),
      real.arccos_one]
end

/-- The angle between a nonzero vector and its negation. -/
@[simp] lemma angle_self_neg_of_nonzero {x : V} (hx : x ≠ 0) : angle x (-x) = π :=
by rw [angle_neg_right, angle_self hx, sub_zero]

/-- The angle between the negation of a nonzero vector and that
vector. -/
@[simp] lemma angle_neg_self_of_nonzero {x : V} (hx : x ≠ 0) : angle (-x) x = π :=
by rw [angle_comm, angle_self_neg_of_nonzero hx]

/-- The angle between a vector and a positive multiple of a vector. -/
@[simp] lemma angle_smul_right_of_pos (x y : V) {r : ℝ} (hr : 0 < r) :
  angle x (r • y) = angle x y :=
begin
  unfold angle,
  rw [inner_smul_right, norm_smul, real.norm_eq_abs, abs_of_nonneg (le_of_lt hr), ←mul_assoc,
      mul_comm _ r, mul_assoc, mul_div_mul_left _ _ (ne_of_gt hr)]
end

/-- The angle between a positive multiple of a vector and a vector. -/
@[simp] lemma angle_smul_left_of_pos (x y : V) {r : ℝ} (hr : 0 < r) :
  angle (r • x) y = angle x y :=
by rw [angle_comm, angle_smul_right_of_pos y x hr, angle_comm]

/-- The angle between a vector and a negative multiple of a vector. -/
@[simp] lemma angle_smul_right_of_neg (x y : V) {r : ℝ} (hr : r < 0) :
  angle x (r • y) = angle x (-y) :=
by rw [←neg_neg r, neg_smul, angle_neg_right, angle_smul_right_of_pos x y (neg_pos_of_neg hr),
       angle_neg_right]

/-- The angle between a negative multiple of a vector and a vector. -/
@[simp] lemma angle_smul_left_of_neg (x y : V) {r : ℝ} (hr : r < 0) :
  angle (r • x) y = angle (-x) y :=
by rw [angle_comm, angle_smul_right_of_neg y x hr, angle_comm]

/-- The cosine of the angle between two vectors, multiplied by the
product of their norms. -/
lemma cos_angle_mul_norm_mul_norm (x y : V) : real.cos (angle x y) * (∥x∥ * ∥y∥) = inner x y :=
begin
  rw cos_angle,
  by_cases h : (∥x∥ * ∥y∥) = 0,
  { rw [h, mul_zero],
    cases eq_zero_or_eq_zero_of_mul_eq_zero h with hx hy,
    { rw norm_eq_zero at hx,
      rw [hx, inner_zero_left] },
    { rw norm_eq_zero at hy,
      rw [hy, inner_zero_right] } },
  { exact div_mul_cancel _ h }
end

/-- The sine of the angle between two vectors, multiplied by the
product of their norms. -/
lemma sin_angle_mul_norm_mul_norm (x y : V) : real.sin (angle x y) * (∥x∥ * ∥y∥) =
    real.sqrt (inner x x * inner y y - inner x y * inner x y) :=
begin
  unfold angle,
  rw [real.sin_arccos (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).1
                      (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).2,
      ←real.sqrt_mul_self (mul_nonneg (norm_nonneg x) (norm_nonneg y)),
      ←real.sqrt_mul' _ (mul_self_nonneg _), pow_two,
      real.sqrt_mul_self (mul_nonneg (norm_nonneg x) (norm_nonneg y)), inner_self_eq_norm_square,
      inner_self_eq_norm_square],
  by_cases h : (∥x∥ * ∥y∥) = 0,
  { rw [(show ∥x∥ * ∥x∥ * (∥y∥ * ∥y∥) = (∥x∥ * ∥y∥) * (∥x∥ * ∥y∥), by ring), h, mul_zero, mul_zero,
        zero_sub],
    cases eq_zero_or_eq_zero_of_mul_eq_zero h with hx hy,
    { rw norm_eq_zero at hx,
      rw [hx, inner_zero_left, zero_mul, neg_zero] },
    { rw norm_eq_zero at hy,
      rw [hy, inner_zero_right, zero_mul, neg_zero] } },
  { field_simp [h],
    ring }
end

/-- The angle between two vectors is zero if and only if they are
nonzero and one is a positive multiple of the other. -/
lemma angle_eq_zero_iff (x y : V) : angle x y = 0 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), 0 < r ∧ y = r • x) :=
begin
  unfold angle,
  rw [←inner_div_norm_mul_norm_eq_one_iff, ←real.arccos_one],
  split,
  { intro h,
    exact real.arccos_inj (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).1
                          (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).2
                          (by norm_num)
                          (by norm_num)
                          h },
  { intro h,
    rw h }
end

/-- The angle between two vectors is π if and only if they are nonzero
and one is a negative multiple of the other. -/
lemma angle_eq_pi_iff (x y : V) : angle x y = π ↔ (x ≠ 0 ∧ ∃ (r : ℝ), r < 0 ∧ y = r • x) :=
begin
  unfold angle,
  rw [←inner_div_norm_mul_norm_eq_neg_one_iff, ←real.arccos_neg_one],
  split,
  { intro h,
    exact real.arccos_inj (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).1
                          (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).2
                          (by norm_num)
                          (by norm_num)
                          h },
  { intro h,
    rw h }
end

/-- If the angle between two vectors is π, the angles between those
vectors and a third vector add to π. -/
lemma angle_add_angle_eq_pi_of_angle_eq_pi {x y : V} (z : V) (h : angle x y = π) :
  angle x z + angle y z = π :=
begin
  rw angle_eq_pi_iff at h,
  rcases h with ⟨hx, ⟨r, ⟨hr, hxy⟩⟩⟩,
  rw [hxy, angle_smul_left_of_neg x z hr, angle_neg_left,
      add_sub_cancel'_right]
end

/-- Two vectors have inner product 0 if and only if the angle between
them is π/2. -/
lemma inner_eq_zero_iff_angle_eq_pi_div_two (x y : V) : inner x y = 0 ↔ angle x y = π / 2 :=
begin
  split,
  { intro h,
    unfold angle,
    rw [h, zero_div, real.arccos_zero] },
  { intro h,
    unfold angle at h,
    rw ←real.arccos_zero at h,
    have h2 : inner x y / (∥x∥ * ∥y∥) = 0 :=
      real.arccos_inj (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).1
                      (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x y)).2
                      (by norm_num)
                      (by norm_num)
                      h,
    by_cases h : (∥x∥ * ∥y∥) = 0,
    { cases eq_zero_or_eq_zero_of_mul_eq_zero h with hx hy,
      { rw norm_eq_zero at hx,
        rw [hx, inner_zero_left] },
      { rw norm_eq_zero at hy,
        rw [hy, inner_zero_right] } },
    { simpa [h, div_eq_zero_iff] using h2 } },
end

/-- Pythagorean theorem, if-and-only-if vector angle form. -/
lemma norm_add_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two (x y : V) :
  ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ ↔ angle x y = π / 2 :=
begin
  rw norm_add_square_eq_norm_square_add_norm_square_iff_inner_eq_zero,
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
  rw norm_sub_square_eq_norm_square_add_norm_square_iff_inner_eq_zero,
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
       cos_angle_mul_norm_mul_norm, ←inner_self_eq_norm_square,
       ←inner_self_eq_norm_square, ←inner_self_eq_norm_square, inner_sub_sub_self,
       sub_add_eq_add_sub]

/-- Pons asinorum, vector angle form. -/
lemma angle_sub_eq_angle_sub_rev_of_norm_eq {x y : V} (h : ∥x∥ = ∥y∥) :
  angle x (x - y) = angle y (y - x) :=
begin
  refine real.cos_inj_of_nonneg_of_le_pi (angle_nonneg _ _)
                                         (angle_le_pi _ _)
                                         (angle_nonneg _ _)
                                         (angle_le_pi _ _) _,
  rw [cos_angle, cos_angle, h, ←neg_sub, norm_neg, neg_sub,
      inner_sub_right, inner_sub_right, inner_self_eq_norm_square, inner_self_eq_norm_square, h,
      inner_comm x y]
end

/-- Converse of pons asinorum, vector angle form. -/
lemma norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi {x y : V}
    (h : angle x (x - y) = angle y (y - x)) (hpi : angle x y ≠ π) : ∥x∥ = ∥y∥ :=
begin
  replace h := real.arccos_inj
    (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x (x - y))).1
    (abs_le.mp (abs_inner_div_norm_mul_norm_le_one x (x - y))).2
    (abs_le.mp (abs_inner_div_norm_mul_norm_le_one y (y - x))).1
    (abs_le.mp (abs_inner_div_norm_mul_norm_le_one y (y - x))).2
    h,
  by_cases hxy : x = y,
  { rw hxy },
  { rw [←norm_neg (y - x), neg_sub, mul_comm, mul_comm ∥y∥, div_eq_mul_inv, div_eq_mul_inv,
        mul_inv', mul_inv', ←mul_assoc, ←mul_assoc] at h,
    replace h :=
      mul_right_cancel' (inv_ne_zero (λ hz, hxy (eq_of_sub_eq_zero (norm_eq_zero.1 hz)))) h,
    rw [inner_sub_right, inner_sub_right, inner_comm y x, inner_self_eq_norm_square,
        inner_self_eq_norm_square, mul_sub_right_distrib, mul_sub_right_distrib,
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
        rw [inner_div_norm_mul_norm_eq_neg_one_iff, ←angle_eq_pi_iff] at h,
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
    have H2 : inner x x * (inner x x - inner x y - (inner x y - inner y y)) -
                (inner x x - inner x y) * (inner x x - inner x y) =
              inner x x * inner y y - inner x y * inner x y, { ring },
    have H3 : inner y y * (inner y y - inner x y - (inner x y - inner x x)) -
                (inner y y - inner x y) * (inner y y - inner x y) =
              inner x x * inner y y - inner x y * inner x y, { ring },
    rw [mul_sub_right_distrib, mul_sub_right_distrib, mul_sub_right_distrib,
        mul_sub_right_distrib, H1, sin_angle_mul_norm_mul_norm, norm_sub_rev x y,
        sin_angle_mul_norm_mul_norm, norm_sub_rev y x, inner_sub_left, inner_sub_left,
        inner_sub_right, inner_sub_right, inner_sub_right, inner_sub_right, inner_comm y x, H2,
        H3, real.mul_self_sqrt (sub_nonneg_of_le (inner_mul_inner_self_le x y)),
        inner_self_eq_norm_square, inner_self_eq_norm_square,
        inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two],
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
    have H1 : real.sin (angle x (x - y)) * (inner y (y - x) / (∥y∥ * ∥y - x∥)) * ∥x∥ * ∥y∥ * ∥x - y∥ =
                real.sin (angle x (x - y)) * (∥x∥ * ∥x - y∥) *
                  (inner y (y - x) / (∥y∥ * ∥y - x∥)) * ∥y∥, { ring },
    have H2 : inner x (x - y) / (∥x∥ * ∥y - x∥) * real.sin (angle y (y - x)) * ∥x∥ * ∥y∥ * ∥y - x∥ =
                inner x (x - y) / (∥x∥ * ∥y - x∥) *
                  (real.sin (angle y (y - x)) * (∥y∥ * ∥y - x∥)) * ∥x∥, { ring },
    have H3 : inner x x * (inner x x - inner x y - (inner x y - inner y y)) -
                (inner x x - inner x y) * (inner x x - inner x y) =
              inner x x * inner y y - inner x y * inner x y, { ring },
    have H4 : inner y y * (inner y y - inner x y - (inner x y - inner x x)) -
                (inner y y - inner x y) * (inner y y - inner x y) =
              inner x x * inner y y - inner x y * inner x y, { ring },
    rw [right_distrib, right_distrib, right_distrib, right_distrib, H1,
        sin_angle_mul_norm_mul_norm, norm_sub_rev x y, H2, sin_angle_mul_norm_mul_norm,
        norm_sub_rev y x, mul_assoc (real.sin (angle x y)), sin_angle_mul_norm_mul_norm,
        inner_sub_left, inner_sub_left, inner_sub_right, inner_sub_right, inner_sub_right,
        inner_sub_right, inner_comm y x, H3, H4, inner_self_eq_norm_square,
        inner_self_eq_norm_square,
        inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two],
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
        angle_smul_right_of_pos _ _ (add_pos' zero_lt_one (neg_pos_of_neg hr)), angle_self hx,
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
### Geometrical results on Euclidean affine spaces

This section develops some geometrical definitions and results on
Euclidean affine spaces.
-/
open add_torsor inner_product_geometry

variables (V : Type*) {P : Type*} [inner_product_space V] [metric_space P]
    [euclidean_affine_space V P]
include V

/-- The undirected angle at `p2` between the line segments to `p1` and
`p3`. If either of those points equals `p2`, this is π/2. Use
`open_locale euclidean_geometry` to access the `∠ V p1 p2 p3`
notation. -/
def angle (p1 p2 p3 : P) : ℝ := angle (p1 -ᵥ p2 : V) (p3 -ᵥ p2)

localized "notation `∠` := euclidean_geometry.angle" in euclidean_geometry

/-- The angle at a point does not depend on the order of the other two
points. -/
lemma angle_comm (p1 p2 p3 : P) : ∠ V p1 p2 p3 = ∠ V p3 p2 p1 :=
angle_comm _ _

/-- The angle at a point is nonnegative. -/
lemma angle_nonneg (p1 p2 p3 : P) : 0 ≤ ∠ V p1 p2 p3 :=
angle_nonneg _ _

/-- The angle at a point is at most π. -/
lemma angle_le_pi (p1 p2 p3 : P) : ∠ V p1 p2 p3 ≤ π :=
angle_le_pi _ _

/-- The angle ∠AAB at a point. -/
lemma angle_eq_left (p1 p2 : P) : ∠ V p1 p1 p2 = π / 2 :=
begin
  unfold angle,
  rw vsub_self,
  exact angle_zero_left _
end

/-- The angle ∠ABB at a point. -/
lemma angle_eq_right (p1 p2 : P) : ∠ V p1 p2 p2 = π / 2 :=
by rw [angle_comm, angle_eq_left]

/-- The angle ∠ABA at a point. -/
lemma angle_eq_of_ne {p1 p2 : P} (h : p1 ≠ p2) : ∠ V p1 p2 p1 = 0 :=
angle_self (λ he, h ((vsub_eq_zero_iff_eq V).1 he))

/-- If the angle ∠ABC at a point is π, the angle ∠BAC is 0. -/
lemma angle_eq_zero_of_angle_eq_pi_left {p1 p2 p3 : P} (h : ∠ V p1 p2 p3 = π) :
  ∠ V p2 p1 p3 = 0 :=
begin
  unfold angle at h,
  rw angle_eq_pi_iff at h,
  rcases h with ⟨hp1p2, ⟨r, ⟨hr, hpr⟩⟩⟩,
  unfold angle,
  rw angle_eq_zero_iff,
  rw [←neg_vsub_eq_vsub_rev, neg_ne_zero] at hp1p2,
  use [hp1p2, -r + 1, add_pos' (neg_pos_of_neg hr) zero_lt_one],
  rw [add_smul, ←neg_vsub_eq_vsub_rev V p1 p2, smul_neg],
  simp [←hpr]
end

/-- If the angle ∠ABC at a point is π, the angle ∠BCA is 0. -/
lemma angle_eq_zero_of_angle_eq_pi_right {p1 p2 p3 : P} (h : ∠ V p1 p2 p3 = π) :
  ∠ V p2 p3 p1 = 0 :=
begin
  rw angle_comm at h,
  exact angle_eq_zero_of_angle_eq_pi_left V h
end

/-- If ∠BCD = π, then ∠ABC = ∠ABD. -/
lemma angle_eq_angle_of_angle_eq_pi (p1 : P) {p2 p3 p4 : P} (h : ∠ V p2 p3 p4 = π) :
  ∠ V p1 p2 p3 = ∠ V p1 p2 p4 :=
begin
  unfold angle at h,
  rw angle_eq_pi_iff at h,
  rcases h with ⟨hp2p3, ⟨r, ⟨hr, hpr⟩⟩⟩,
  unfold angle,
  symmetry,
  convert angle_smul_right_of_pos _ _ (add_pos' (neg_pos_of_neg hr) zero_lt_one),
  rw [add_smul, ←neg_vsub_eq_vsub_rev V p2 p3, smul_neg],
  simp [←hpr]
end

/-- If ∠BCD = π, then ∠ACB + ∠ACD = π. -/
lemma angle_add_angle_eq_pi_of_angle_eq_pi (p1 : P) {p2 p3 p4 : P} (h : ∠ V p2 p3 p4 = π) :
  ∠ V p1 p3 p2 + ∠ V p1 p3 p4 = π :=
begin
  unfold angle at h,
  rw [angle_comm V p1 p3 p2, angle_comm V p1 p3 p4],
  unfold angle,
  exact angle_add_angle_eq_pi_of_angle_eq_pi _ h
end

/-- Pythagorean theorem, if-and-only-if angle-at-point form. -/
lemma dist_square_eq_dist_square_add_dist_square_iff_angle_eq_pi_div_two (p1 p2 p3 : P) :
  dist p1 p3 * dist p1 p3 = dist p1 p2 * dist p1 p2 + dist p3 p2 * dist p3 p2 ↔
    ∠ V p1 p2 p3 = π / 2 :=
by erw [metric_space.dist_comm p3 p2, dist_eq_norm V p1 p3, dist_eq_norm V p1 p2,
        dist_eq_norm V p2 p3,
        ←norm_sub_square_eq_norm_square_add_norm_square_iff_angle_eq_pi_div_two,
        vsub_sub_vsub_cancel_right V p1, ←neg_vsub_eq_vsub_rev V p2 p3, norm_neg]

/-- Law of cosines (cosine rule), angle-at-point form. -/
lemma dist_square_eq_dist_square_add_dist_square_sub_two_mul_dist_mul_dist_mul_cos_angle
    (p1 p2 p3 : P) :
  dist p1 p3 * dist p1 p3 =
    dist p1 p2 * dist p1 p2 + dist p3 p2 * dist p3 p2 -
      2 * dist p1 p2 * dist p3 p2 * real.cos (∠ V p1 p2 p3) :=
begin
  rw [dist_eq_norm V p1 p3, dist_eq_norm V p1 p2, dist_eq_norm V p3 p2],
  unfold angle,
  convert norm_sub_square_eq_norm_square_add_norm_square_sub_two_mul_norm_mul_norm_mul_cos_angle
          (p1 -ᵥ p2 : V) (p3 -ᵥ p2 : V),
  { exact (vsub_sub_vsub_cancel_right V p1 p3 p2).symm },
  { exact (vsub_sub_vsub_cancel_right V p1 p3 p2).symm }
end

/-- Pons asinorum, angle-at-point form. -/
lemma angle_eq_angle_of_dist_eq {p1 p2 p3 : P} (h : dist p1 p2 = dist p1 p3) :
  ∠ V p1 p2 p3 = ∠ V p1 p3 p2 :=
begin
  rw [dist_eq_norm V p1 p2, dist_eq_norm V p1 p3] at h,
  unfold angle,
  convert angle_sub_eq_angle_sub_rev_of_norm_eq h,
  { exact (vsub_sub_vsub_cancel_left V p3 p2 p1).symm },
  { exact (vsub_sub_vsub_cancel_left V p2 p3 p1).symm }
end

/-- Converse of pons asinorum, angle-at-point form. -/
lemma dist_eq_of_angle_eq_angle_of_angle_ne_pi {p1 p2 p3 : P} (h : ∠ V p1 p2 p3 = ∠ V p1 p3 p2)
    (hpi : ∠ V p2 p1 p3 ≠ π) : dist p1 p2 = dist p1 p3 :=
begin
  unfold angle at h hpi,
  rw [dist_eq_norm V p1 p2, dist_eq_norm V p1 p3],
  rw [←angle_neg_neg, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] at hpi,
  rw [←vsub_sub_vsub_cancel_left V p3 p2 p1, ←vsub_sub_vsub_cancel_left V p2 p3 p1] at h,
  exact norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi h hpi
end

/-- The sum of the angles of a possibly degenerate triangle (where the
given vertex is distinct from the others), angle-at-point. -/
lemma angle_add_angle_add_angle_eq_pi {p1 p2 p3 : P} (h2 : p2 ≠ p1) (h3 : p3 ≠ p1) :
  ∠ V p1 p2 p3 + ∠ V p2 p3 p1 + ∠ V p3 p1 p2 = π :=
begin
  rw [add_assoc, add_comm, add_comm (∠ V p2 p3 p1), angle_comm V p2 p3 p1],
  unfold angle,
  rw [←angle_neg_neg (p1 -ᵥ p3), ←angle_neg_neg (p1 -ᵥ p2), neg_vsub_eq_vsub_rev,
      neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev,
      ←vsub_sub_vsub_cancel_right V p3 p2 p1, ←vsub_sub_vsub_cancel_right V p2 p3 p1],
  exact angle_add_angle_sub_add_angle_sub_eq_pi (λ he, h3 ((vsub_eq_zero_iff_eq V).1 he))
                                                (λ he, h2 ((vsub_eq_zero_iff_eq V).1 he))
end

/-- The inner product of two vectors given with `weighted_vsub`, in
terms of the pairwise distances. -/
lemma inner_weighted_vsub {ι₁ : Type*} {s₁ : finset ι₁} {w₁ : ι₁ → ℝ} (p₁ : ι₁ → P)
    (h₁ : ∑ i in s₁, w₁ i = 0) {ι₂ : Type*} {s₂ : finset ι₂} {w₂ : ι₂ → ℝ} (p₂ : ι₂ → P)
    (h₂ : ∑ i in s₂, w₂ i = 0) :
  inner (s₁.weighted_vsub V p₁ w₁) (s₂.weighted_vsub V p₂ w₂) =
    (-∑ i₁ in s₁, ∑ i₂ in s₂,
      w₁ i₁ * w₂ i₂ * (dist (p₁ i₁) (p₂ i₂) * dist (p₁ i₁) (p₂ i₂))) / 2 :=
begin
  rw [finset.weighted_vsub_apply, finset.weighted_vsub_apply,
      inner_sum_smul_sum_smul_of_sum_eq_zero _ h₁ _ h₂],
  simp_rw [vsub_sub_vsub_cancel_right],
  congr,
  ext i₁,
  congr,
  ext i₂,
  rw dist_eq_norm V (p₁ i₁) (p₂ i₂)
end

/-- The distance between two points given with `affine_combination`,
in terms of the pairwise distances between the points in that
combination. -/
lemma dist_affine_combination {ι : Type*} {s : finset ι} {w₁ w₂ : ι → ℝ} (p : ι → P)
    (h₁ : ∑ i in s, w₁ i = 1) (h₂ : ∑ i in s, w₂ i = 1) :
  dist (s.affine_combination V w₁ p) (s.affine_combination V w₂ p) *
    dist (s.affine_combination V w₁ p) (s.affine_combination V w₂ p) =
    (-∑ i₁ in s, ∑ i₂ in s,
      (w₁ - w₂) i₁ * (w₁ - w₂) i₂ * (dist (p i₁) (p i₂) * dist (p i₁) (p i₂))) / 2 :=
begin
  rw [dist_eq_norm V (s.affine_combination V w₁ p) (s.affine_combination V w₂ p),
      ←inner_self_eq_norm_square, finset.affine_combination_vsub],
  have h : ∑ i in s, (w₁ - w₂) i = 0,
  { simp_rw [pi.sub_apply, finset.sum_sub_distrib, h₁, h₂, sub_self] },
  exact inner_weighted_vsub V p h p h
end

end euclidean_geometry
