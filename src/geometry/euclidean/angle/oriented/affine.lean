/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import analysis.convex.side
import geometry.euclidean.angle.oriented.rotation
import geometry.euclidean.angle.unoriented.affine

/-!
# Oriented angles.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines oriented angles in Euclidean affine spaces.

## Main definitions

* `euclidean_geometry.oangle`, with notation `∡`, is the oriented angle determined by three
  points.

-/

noncomputable theory

open finite_dimensional complex
open_locale affine euclidean_geometry real real_inner_product_space complex_conjugate

namespace euclidean_geometry

variables {V : Type*} {P : Type*}
  [normed_add_comm_group V] [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P]
  [hd2 : fact (finrank ℝ V = 2)] [module.oriented ℝ V (fin 2)]
include hd2

local notation `o` := module.oriented.positive_orientation

/-- The oriented angle at `p₂` between the line segments to `p₁` and `p₃`, modulo `2 * π`. If
either of those points equals `p₂`, this is 0. See `euclidean_geometry.angle` for the
corresponding unoriented angle definition. -/
def oangle (p₁ p₂ p₃ : P) : real.angle := (o).oangle (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)

localized "notation (name := oangle) `∡` := euclidean_geometry.oangle" in euclidean_geometry

/-- Oriented angles are continuous when neither end point equals the middle point. -/
lemma continuous_at_oangle {x : P × P × P} (hx12 : x.1 ≠ x.2.1) (hx32 : x.2.2 ≠ x.2.1) :
  continuous_at (λ y : P × P × P, ∡ y.1 y.2.1 y.2.2) x :=
begin
  let f : P × P × P → V × V := λ y, (y.1 -ᵥ y.2.1, y.2.2 -ᵥ y.2.1),
  have hf1 : (f x).1 ≠ 0, by simp [hx12],
  have hf2 : (f x).2 ≠ 0, by simp [hx32],
  exact ((o).continuous_at_oangle hf1 hf2).comp
    ((continuous_fst.vsub continuous_snd.fst).prod_mk
      (continuous_snd.snd.vsub continuous_snd.fst)).continuous_at
end

/-- The angle ∡AAB at a point. -/
@[simp] lemma oangle_self_left (p₁ p₂ : P) : ∡ p₁ p₁ p₂ = 0 :=
by simp [oangle]

/-- The angle ∡ABB at a point. -/
@[simp] lemma oangle_self_right (p₁ p₂ : P) : ∡ p₁ p₂ p₂ = 0 :=
by simp [oangle]

/-- The angle ∡ABA at a point. -/
@[simp] lemma oangle_self_left_right (p₁ p₂ : P) : ∡ p₁ p₂ p₁ = 0 :=
(o).oangle_self _

/-- If the angle between three points is nonzero, the first two points are not equal. -/
lemma left_ne_of_oangle_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ ≠ 0) : p₁ ≠ p₂ :=
by { rw ←@vsub_ne_zero V, exact (o).left_ne_zero_of_oangle_ne_zero h }

/-- If the angle between three points is nonzero, the last two points are not equal. -/
lemma right_ne_of_oangle_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ ≠ 0) : p₃ ≠ p₂ :=
by { rw ←@vsub_ne_zero V, exact (o).right_ne_zero_of_oangle_ne_zero h }

/-- If the angle between three points is nonzero, the first and third points are not equal. -/
lemma left_ne_right_of_oangle_ne_zero {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ ≠ 0) : p₁ ≠ p₃ :=
by { rw ←(vsub_left_injective p₂).ne_iff, exact (o).ne_of_oangle_ne_zero h }

/-- If the angle between three points is `π`, the first two points are not equal. -/
lemma left_ne_of_oangle_eq_pi {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π) : p₁ ≠ p₂ :=
left_ne_of_oangle_ne_zero (h.symm ▸ real.angle.pi_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)

/-- If the angle between three points is `π`, the last two points are not equal. -/
lemma right_ne_of_oangle_eq_pi {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π) : p₃ ≠ p₂ :=
right_ne_of_oangle_ne_zero (h.symm ▸ real.angle.pi_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)

/-- If the angle between three points is `π`, the first and third points are not equal. -/
lemma left_ne_right_of_oangle_eq_pi {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π) : p₁ ≠ p₃ :=
left_ne_right_of_oangle_ne_zero (h.symm ▸ real.angle.pi_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)

/-- If the angle between three points is `π / 2`, the first two points are not equal. -/
lemma left_ne_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : ℝ)) : p₁ ≠ p₂ :=
left_ne_of_oangle_ne_zero (h.symm ▸ real.angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)

/-- If the angle between three points is `π / 2`, the last two points are not equal. -/
lemma right_ne_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : ℝ)) : p₃ ≠ p₂ :=
right_ne_of_oangle_ne_zero (h.symm ▸ real.angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)

/-- If the angle between three points is `π / 2`, the first and third points are not equal. -/
lemma left_ne_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : ℝ)) :
  p₁ ≠ p₃ :=
left_ne_right_of_oangle_ne_zero (h.symm ▸ real.angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)

/-- If the angle between three points is `-π / 2`, the first two points are not equal. -/
lemma left_ne_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : ℝ)) :
  p₁ ≠ p₂ :=
left_ne_of_oangle_ne_zero (h.symm ▸ real.angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)

/-- If the angle between three points is `-π / 2`, the last two points are not equal. -/
lemma right_ne_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : ℝ)) :
  p₃ ≠ p₂ :=
right_ne_of_oangle_ne_zero (h.symm ▸ real.angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)

/-- If the angle between three points is `-π / 2`, the first and third points are not equal. -/
lemma left_ne_right_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : ℝ)) :
  p₁ ≠ p₃ :=
left_ne_right_of_oangle_ne_zero (h.symm ▸ real.angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)

/-- If the sign of the angle between three points is nonzero, the first two points are not
equal. -/
lemma left_ne_of_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign ≠ 0) : p₁ ≠ p₂ :=
left_ne_of_oangle_ne_zero (real.angle.sign_ne_zero_iff.1 h).1

/-- If the sign of the angle between three points is nonzero, the last two points are not
equal. -/
lemma right_ne_of_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign ≠ 0) : p₃ ≠ p₂ :=
right_ne_of_oangle_ne_zero (real.angle.sign_ne_zero_iff.1 h).1

/-- If the sign of the angle between three points is nonzero, the first and third points are not
equal. -/
lemma left_ne_right_of_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign ≠ 0) :
  p₁ ≠ p₃ :=
left_ne_right_of_oangle_ne_zero (real.angle.sign_ne_zero_iff.1 h).1

/-- If the sign of the angle between three points is positive, the first two points are not
equal. -/
lemma left_ne_of_oangle_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : p₁ ≠ p₂ :=
left_ne_of_oangle_sign_ne_zero (h.symm ▸ dec_trivial : (∡ p₁ p₂ p₃).sign ≠ 0)

/-- If the sign of the angle between three points is positive, the last two points are not
equal. -/
lemma right_ne_of_oangle_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : p₃ ≠ p₂ :=
right_ne_of_oangle_sign_ne_zero (h.symm ▸ dec_trivial : (∡ p₁ p₂ p₃).sign ≠ 0)

/-- If the sign of the angle between three points is positive, the first and third points are not
equal. -/
lemma left_ne_right_of_oangle_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : p₁ ≠ p₃ :=
left_ne_right_of_oangle_sign_ne_zero (h.symm ▸ dec_trivial : (∡ p₁ p₂ p₃).sign ≠ 0)

/-- If the sign of the angle between three points is negative, the first two points are not
equal. -/
lemma left_ne_of_oangle_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) : p₁ ≠ p₂ :=
left_ne_of_oangle_sign_ne_zero (h.symm ▸ dec_trivial : (∡ p₁ p₂ p₃).sign ≠ 0)

/-- If the sign of the angle between three points is negative, the last two points are not equal.
-/
lemma right_ne_of_oangle_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) : p₃ ≠ p₂ :=
right_ne_of_oangle_sign_ne_zero (h.symm ▸ dec_trivial : (∡ p₁ p₂ p₃).sign ≠ 0)

/-- If the sign of the angle between three points is negative, the first and third points are not
equal. -/
lemma left_ne_right_of_oangle_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) :
  p₁ ≠ p₃ :=
left_ne_right_of_oangle_sign_ne_zero (h.symm ▸ dec_trivial : (∡ p₁ p₂ p₃).sign ≠ 0)

/-- Reversing the order of the points passed to `oangle` negates the angle. -/
lemma oangle_rev (p₁ p₂ p₃ : P) : ∡ p₃ p₂ p₁ = -∡ p₁ p₂ p₃ :=
(o).oangle_rev _ _

/-- Adding an angle to that with the order of the points reversed results in 0. -/
@[simp] lemma oangle_add_oangle_rev (p₁ p₂ p₃ : P) : ∡ p₁ p₂ p₃ + ∡ p₃ p₂ p₁ = 0 :=
(o).oangle_add_oangle_rev _ _

/-- An oriented angle is zero if and only if the angle with the order of the points reversed is
zero. -/
lemma oangle_eq_zero_iff_oangle_rev_eq_zero {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = 0 ↔ ∡ p₃ p₂ p₁ = 0 :=
(o).oangle_eq_zero_iff_oangle_rev_eq_zero

/-- An oriented angle is `π` if and only if the angle with the order of the points reversed is
`π`. -/
lemma oangle_eq_pi_iff_oangle_rev_eq_pi {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ ∡ p₃ p₂ p₁ = π :=
(o).oangle_eq_pi_iff_oangle_rev_eq_pi

/-- An oriented angle is not zero or `π` if and only if the three points are affinely
independent. -/
lemma oangle_ne_zero_and_ne_pi_iff_affine_independent {p₁ p₂ p₃ : P} :
  (∡ p₁ p₂ p₃ ≠ 0 ∧ ∡ p₁ p₂ p₃ ≠ π) ↔ affine_independent ℝ ![p₁, p₂, p₃] :=
begin
  rw [oangle, (o).oangle_ne_zero_and_ne_pi_iff_linear_independent,
      affine_independent_iff_linear_independent_vsub ℝ _ (1 : fin 3),
      ←linear_independent_equiv (fin_succ_above_equiv (1 : fin 3)).to_equiv],
  convert iff.rfl,
  ext i,
  fin_cases i;
    refl
end

/-- An oriented angle is zero or `π` if and only if the three points are collinear. -/
lemma oangle_eq_zero_or_eq_pi_iff_collinear {p₁ p₂ p₃ : P} :
  (∡ p₁ p₂ p₃ = 0 ∨ ∡ p₁ p₂ p₃ = π) ↔ collinear ℝ ({p₁, p₂, p₃} : set P) :=
by rw [←not_iff_not, not_or_distrib, oangle_ne_zero_and_ne_pi_iff_affine_independent,
       affine_independent_iff_not_collinear_set]

/-- If twice the oriented angles between two triples of points are equal, one triple is affinely
independent if and only if the other is. -/
lemma affine_independent_iff_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P}
  (h : (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₄ p₅ p₆) :
  affine_independent ℝ ![p₁, p₂, p₃] ↔ affine_independent ℝ ![p₄, p₅, p₆] :=
by simp_rw [←oangle_ne_zero_and_ne_pi_iff_affine_independent, ←real.angle.two_zsmul_ne_zero_iff, h]

/-- If twice the oriented angles between two triples of points are equal, one triple is collinear
if and only if the other is. -/
lemma collinear_iff_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P}
  (h : (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₄ p₅ p₆) :
  collinear ℝ ({p₁, p₂, p₃} : set P) ↔ collinear ℝ ({p₄, p₅, p₆} : set P) :=
by simp_rw [←oangle_eq_zero_or_eq_pi_iff_collinear, ←real.angle.two_zsmul_eq_zero_iff, h]

/-- If corresponding pairs of points in two angles have the same vector span, twice those angles
are equal. -/
lemma two_zsmul_oangle_of_vector_span_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P}
  (h₁₂₄₅ : vector_span ℝ ({p₁, p₂} : set P) = vector_span ℝ ({p₄, p₅} : set P))
  (h₃₂₆₅ : vector_span ℝ ({p₃, p₂} : set P) = vector_span ℝ ({p₆, p₅} : set P)) :
  (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₄ p₅ p₆ :=
begin
  simp_rw vector_span_pair at h₁₂₄₅ h₃₂₆₅,
  exact (o).two_zsmul_oangle_of_span_eq_of_span_eq h₁₂₄₅ h₃₂₆₅
end

/-- If the lines determined by corresponding pairs of points in two angles are parallel, twice
those angles are equal. -/
lemma two_zsmul_oangle_of_parallel {p₁ p₂ p₃ p₄ p₅ p₆ : P}
  (h₁₂₄₅ : line[ℝ, p₁, p₂] ∥ line[ℝ, p₄, p₅]) (h₃₂₆₅ : line[ℝ, p₃, p₂] ∥ line[ℝ, p₆, p₅]) :
  (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₄ p₅ p₆ :=
begin
  rw affine_subspace.affine_span_pair_parallel_iff_vector_span_eq at h₁₂₄₅ h₃₂₆₅,
  exact two_zsmul_oangle_of_vector_span_eq h₁₂₄₅ h₃₂₆₅
end

/-- Given three points not equal to `p`, the angle between the first and the second at `p` plus
the angle between the second and the third equals the angle between the first and the third. -/
@[simp] lemma oangle_add {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
  ∡ p₁ p p₂ + ∡ p₂ p p₃ = ∡ p₁ p p₃ :=
(o).oangle_add (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

/-- Given three points not equal to `p`, the angle between the second and the third at `p` plus
the angle between the first and the second equals the angle between the first and the third. -/
@[simp] lemma oangle_add_swap {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
  ∡ p₂ p p₃ + ∡ p₁ p p₂ = ∡ p₁ p p₃ :=
(o).oangle_add_swap (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

/-- Given three points not equal to `p`, the angle between the first and the third at `p` minus
the angle between the first and the second equals the angle between the second and the third. -/
@[simp] lemma oangle_sub_left {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
  ∡ p₁ p p₃ - ∡ p₁ p p₂ = ∡ p₂ p p₃ :=
(o).oangle_sub_left (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

/-- Given three points not equal to `p`, the angle between the first and the third at `p` minus
the angle between the second and the third equals the angle between the first and the second. -/
@[simp] lemma oangle_sub_right {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
  ∡ p₁ p p₃ - ∡ p₂ p p₃ = ∡ p₁ p p₂ :=
(o).oangle_sub_right (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

/-- Given three points not equal to `p`, adding the angles between them at `p` in cyclic order
results in 0. -/
@[simp] lemma oangle_add_cyc3 {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
  ∡ p₁ p p₂ + ∡ p₂ p p₃ + ∡ p₃ p p₁ = 0 :=
(o).oangle_add_cyc3 (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

/-- Pons asinorum, oriented angle-at-point form. -/
lemma oangle_eq_oangle_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃) :
  ∡ p₁ p₂ p₃ = ∡ p₂ p₃ p₁ :=
begin
  simp_rw dist_eq_norm_vsub at h,
  rw [oangle, oangle, ←vsub_sub_vsub_cancel_left p₃ p₂ p₁, ←vsub_sub_vsub_cancel_left p₂ p₃ p₁,
      (o).oangle_sub_eq_oangle_sub_rev_of_norm_eq h]
end

/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
angle-at-point form. -/
lemma oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq {p₁ p₂ p₃ : P} (hn : p₂ ≠ p₃)
  (h : dist p₁ p₂ = dist p₁ p₃) : ∡ p₃ p₁ p₂ = π - (2 : ℤ) • ∡ p₁ p₂ p₃ :=
begin
  simp_rw dist_eq_norm_vsub at h,
  rw [oangle, oangle],
  convert (o).oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq _ h using 1,
  { rw [←neg_vsub_eq_vsub_rev p₁ p₃, ←neg_vsub_eq_vsub_rev p₁ p₂, (o).oangle_neg_neg] },
  { rw [←(o).oangle_sub_eq_oangle_sub_rev_of_norm_eq h], simp },
  { simpa using hn }
end

/-- A base angle of an isosceles triangle is acute, oriented angle-at-point form. -/
lemma abs_oangle_right_to_real_lt_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P}
  (h : dist p₁ p₂ = dist p₁ p₃) : |(∡ p₁ p₂ p₃).to_real| < π / 2 :=
begin
  simp_rw dist_eq_norm_vsub at h,
  rw [oangle, ←vsub_sub_vsub_cancel_left p₃ p₂ p₁],
  exact (o).abs_oangle_sub_right_to_real_lt_pi_div_two h
end

/-- A base angle of an isosceles triangle is acute, oriented angle-at-point form. -/
lemma abs_oangle_left_to_real_lt_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P}
  (h : dist p₁ p₂ = dist p₁ p₃) : |(∡ p₂ p₃ p₁).to_real| < π / 2 :=
(oangle_eq_oangle_of_dist_eq h) ▸ abs_oangle_right_to_real_lt_pi_div_two_of_dist_eq h

/-- The cosine of the oriented angle at `p` between two points not equal to `p` equals that of the
unoriented angle. -/
lemma cos_oangle_eq_cos_angle {p p₁ p₂ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) :
  real.angle.cos (∡ p₁ p p₂) = real.cos (∠ p₁ p p₂) :=
(o).cos_oangle_eq_cos_angle (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

/-- The oriented angle at `p` between two points not equal to `p` is plus or minus the unoriented
angle. -/
lemma oangle_eq_angle_or_eq_neg_angle {p p₁ p₂ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) :
  ∡ p₁ p p₂ = ∠ p₁ p p₂ ∨ ∡ p₁ p p₂ = -∠ p₁ p p₂ :=
(o).oangle_eq_angle_or_eq_neg_angle (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

/-- The unoriented angle at `p` between two points not equal to `p` is the absolute value of the
oriented angle. -/
lemma angle_eq_abs_oangle_to_real {p p₁ p₂ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) :
  ∠ p₁ p p₂ = |(∡ p₁ p p₂).to_real| :=
(o).angle_eq_abs_oangle_to_real (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

/-- If the sign of the oriented angle at `p` between two points is zero, either one of the points
equals `p` or the unoriented angle is 0 or π. -/
lemma eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero {p p₁ p₂ : P}
  (h : (∡ p₁ p p₂).sign = 0) : p₁ = p ∨ p₂ = p ∨ ∠ p₁ p p₂ = 0 ∨ ∠ p₁ p p₂ = π :=
begin
  convert (o).eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero h;
    simp
end

/-- If two unoriented angles are equal, and the signs of the corresponding oriented angles are
equal, then the oriented angles are equal (even in degenerate cases). -/
lemma oangle_eq_of_angle_eq_of_sign_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆)
  (hs : (∡ p₁ p₂ p₃).sign = (∡ p₄ p₅ p₆).sign) : ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆ :=
(o).oangle_eq_of_angle_eq_of_sign_eq h hs

/-- If the signs of two nondegenerate oriented angles between points are equal, the oriented
angles are equal if and only if the unoriented angles are equal. -/
lemma angle_eq_iff_oangle_eq_of_sign_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (hp₁ : p₁ ≠ p₂) (hp₃ : p₃ ≠ p₂)
  (hp₄ : p₄ ≠ p₅) (hp₆ : p₆ ≠ p₅) (hs : (∡ p₁ p₂ p₃).sign = (∡ p₄ p₅ p₆).sign) :
  ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆ ↔ ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆ :=
(o).angle_eq_iff_oangle_eq_of_sign_eq (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₃)
                                      (vsub_ne_zero.2 hp₄) (vsub_ne_zero.2 hp₆) hs

/-- The oriented angle between three points equals the unoriented angle if the sign is
positive. -/
lemma oangle_eq_angle_of_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) :
  ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃ :=
(o).oangle_eq_angle_of_sign_eq_one h

/-- The oriented angle between three points equals minus the unoriented angle if the sign is
negative. -/
lemma oangle_eq_neg_angle_of_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) :
  ∡ p₁ p₂ p₃ = -∠ p₁ p₂ p₃ :=
(o).oangle_eq_neg_angle_of_sign_eq_neg_one h

/-- The unoriented angle at `p` between two points not equal to `p` is zero if and only if the
unoriented angle is zero. -/
lemma oangle_eq_zero_iff_angle_eq_zero {p p₁ p₂ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) :
  ∡ p₁ p p₂ = 0 ↔ ∠ p₁ p p₂ = 0 :=
(o).oangle_eq_zero_iff_angle_eq_zero (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

/-- The oriented angle between three points is `π` if and only if the unoriented angle is `π`. -/
lemma oangle_eq_pi_iff_angle_eq_pi {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ ∠ p₁ p₂ p₃ = π :=
(o).oangle_eq_pi_iff_angle_eq_pi

/-- If the oriented angle between three points is `π / 2`, so is the unoriented angle. -/
lemma angle_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  ∠ p₁ p₂ p₃ = π / 2 :=
begin
  rw [angle, ←inner_product_geometry.inner_eq_zero_iff_angle_eq_pi_div_two],
  exact (o).inner_eq_zero_of_oangle_eq_pi_div_two h
end

/-- If the oriented angle between three points is `π / 2`, so is the unoriented angle
(reversed). -/
lemma angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
  ∠ p₃ p₂ p₁ = π / 2 :=
begin
  rw angle_comm,
  exact angle_eq_pi_div_two_of_oangle_eq_pi_div_two h,
end

/-- If the oriented angle between three points is `-π / 2`, the unoriented angle is `π / 2`. -/
lemma angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P}
  (h : ∡ p₁ p₂ p₃ = ↑(-π / 2)) : ∠ p₁ p₂ p₃ = π / 2 :=
begin
  rw [angle, ←inner_product_geometry.inner_eq_zero_iff_angle_eq_pi_div_two],
  exact (o).inner_eq_zero_of_oangle_eq_neg_pi_div_two h
end

/-- If the oriented angle between three points is `-π / 2`, the unoriented angle (reversed) is
`π / 2`. -/
lemma angle_rev_eq_pi_div_two_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P}
  (h : ∡ p₁ p₂ p₃ = ↑(-π / 2)) : ∠ p₃ p₂ p₁ = π / 2 :=
begin
  rw angle_comm,
  exact angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two h
end

/-- Swapping the first and second points in an oriented angle negates the sign of that angle. -/
lemma oangle_swap₁₂_sign (p₁ p₂ p₃ : P) : -(∡ p₁ p₂ p₃).sign = (∡ p₂ p₁ p₃).sign :=
begin
  rw [eq_comm, oangle, oangle, ←(o).oangle_neg_neg, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev,
      ←vsub_sub_vsub_cancel_left p₁ p₃ p₂, ←neg_vsub_eq_vsub_rev p₃ p₂, sub_eq_add_neg,
      neg_vsub_eq_vsub_rev p₂ p₁, add_comm, ←@neg_one_smul ℝ],
  nth_rewrite 1 [←one_smul ℝ (p₁ -ᵥ p₂)],
  rw (o).oangle_sign_smul_add_smul_right,
  simp
end

/-- Swapping the first and third points in an oriented angle negates the sign of that angle. -/
lemma oangle_swap₁₃_sign (p₁ p₂ p₃ : P) : -(∡ p₁ p₂ p₃).sign = (∡ p₃ p₂ p₁).sign :=
by rw [oangle_rev, real.angle.sign_neg, neg_neg]

/-- Swapping the second and third points in an oriented angle negates the sign of that angle. -/
lemma oangle_swap₂₃_sign (p₁ p₂ p₃ : P) : -(∡ p₁ p₂ p₃).sign = (∡ p₁ p₃ p₂).sign :=
by rw [oangle_swap₁₃_sign, ←oangle_swap₁₂_sign, oangle_swap₁₃_sign]

/-- Rotating the points in an oriented angle does not change the sign of that angle. -/
lemma oangle_rotate_sign (p₁ p₂ p₃ : P) : (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign :=
by rw [←oangle_swap₁₂_sign, oangle_swap₁₃_sign]

/-- The oriented angle between three points is π if and only if the second point is strictly
between the other two. -/
lemma oangle_eq_pi_iff_sbtw {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ sbtw ℝ p₁ p₂ p₃ :=
by rw [oangle_eq_pi_iff_angle_eq_pi, angle_eq_pi_iff_sbtw]

/-- If the second of three points is strictly between the other two, the oriented angle at that
point is π. -/
lemma _root_.sbtw.oangle₁₂₃_eq_pi {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∡ p₁ p₂ p₃ = π :=
oangle_eq_pi_iff_sbtw.2 h

/-- If the second of three points is strictly between the other two, the oriented angle at that
point (reversed) is π. -/
lemma _root_.sbtw.oangle₃₂₁_eq_pi {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∡ p₃ p₂ p₁ = π :=
by rw [oangle_eq_pi_iff_oangle_rev_eq_pi, ←h.oangle₁₂₃_eq_pi]

/-- If the second of three points is weakly between the other two, the oriented angle at the
first point is zero. -/
lemma _root_.wbtw.oangle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : wbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₁ p₃ = 0 :=
begin
  by_cases hp₂p₁ : p₂ = p₁, { simp [hp₂p₁] },
  by_cases hp₃p₁ : p₃ = p₁, { simp [hp₃p₁] },
  rw oangle_eq_zero_iff_angle_eq_zero hp₂p₁ hp₃p₁,
  exact h.angle₂₁₃_eq_zero_of_ne hp₂p₁
end

/-- If the second of three points is strictly between the other two, the oriented angle at the
first point is zero. -/
lemma _root_.sbtw.oangle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₁ p₃ = 0 :=
h.wbtw.oangle₂₁₃_eq_zero

/-- If the second of three points is weakly between the other two, the oriented angle at the
first point (reversed) is zero. -/
lemma _root_.wbtw.oangle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : wbtw ℝ p₁ p₂ p₃) : ∡ p₃ p₁ p₂ = 0 :=
by rw [oangle_eq_zero_iff_oangle_rev_eq_zero, h.oangle₂₁₃_eq_zero]

/-- If the second of three points is strictly between the other two, the oriented angle at the
first point (reversed) is zero. -/
lemma _root_.sbtw.oangle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∡ p₃ p₁ p₂ = 0 :=
h.wbtw.oangle₃₁₂_eq_zero

/-- If the second of three points is weakly between the other two, the oriented angle at the
third point is zero. -/
lemma _root_.wbtw.oangle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : wbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₃ p₁ = 0 :=
h.symm.oangle₂₁₃_eq_zero

/-- If the second of three points is strictly between the other two, the oriented angle at the
third point is zero. -/
lemma _root_.sbtw.oangle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₃ p₁ = 0 :=
h.wbtw.oangle₂₃₁_eq_zero

/-- If the second of three points is weakly between the other two, the oriented angle at the
third point (reversed) is zero. -/
lemma _root_.wbtw.oangle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : wbtw ℝ p₁ p₂ p₃) : ∡ p₁ p₃ p₂ = 0 :=
h.symm.oangle₃₁₂_eq_zero

/-- If the second of three points is strictly between the other two, the oriented angle at the
third point (reversed) is zero. -/
lemma _root_.sbtw.oangle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∡ p₁ p₃ p₂ = 0 :=
h.wbtw.oangle₁₃₂_eq_zero

/-- The oriented angle between three points is zero if and only if one of the first and third
points is weakly between the other two. -/
lemma oangle_eq_zero_iff_wbtw {p₁ p₂ p₃ : P} :
  ∡ p₁ p₂ p₃ = 0 ↔ wbtw ℝ p₂ p₁ p₃ ∨ wbtw ℝ p₂ p₃ p₁ :=
begin
  by_cases hp₁p₂ : p₁ = p₂, { simp [hp₁p₂] },
  by_cases hp₃p₂ : p₃ = p₂, { simp [hp₃p₂] },
  rw [oangle_eq_zero_iff_angle_eq_zero hp₁p₂ hp₃p₂, angle_eq_zero_iff_ne_and_wbtw],
  simp [hp₁p₂, hp₃p₂]
end

/-- An oriented angle is unchanged by replacing the first point by one weakly further away on the
same ray. -/
lemma _root_.wbtw.oangle_eq_left {p₁ p₁' p₂ p₃ : P} (h : wbtw ℝ p₂ p₁ p₁') (hp₁p₂ : p₁ ≠ p₂) :
  ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃ :=
begin
  by_cases hp₃p₂ : p₃ = p₂, { simp [hp₃p₂] },
  by_cases hp₁'p₂ : p₁' = p₂, { rw [hp₁'p₂, wbtw_self_iff] at h, exact false.elim (hp₁p₂ h) },
  rw [←oangle_add hp₁'p₂ hp₁p₂ hp₃p₂, h.oangle₃₁₂_eq_zero, zero_add]
end

/-- An oriented angle is unchanged by replacing the first point by one strictly further away on
the same ray. -/
lemma _root_.sbtw.oangle_eq_left {p₁ p₁' p₂ p₃ : P} (h : sbtw ℝ p₂ p₁ p₁') :
  ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃ :=
h.wbtw.oangle_eq_left h.ne_left

/-- An oriented angle is unchanged by replacing the third point by one weakly further away on the
same ray. -/
lemma _root_.wbtw.oangle_eq_right {p₁ p₂ p₃ p₃' : P} (h : wbtw ℝ p₂ p₃ p₃') (hp₃p₂ : p₃ ≠ p₂) :
  ∡ p₁ p₂ p₃ = ∡ p₁ p₂ p₃' :=
by rw [oangle_rev, h.oangle_eq_left hp₃p₂, ←oangle_rev]

/-- An oriented angle is unchanged by replacing the third point by one strictly further away on
the same ray. -/
lemma _root_.sbtw.oangle_eq_right {p₁ p₂ p₃ p₃' : P} (h : sbtw ℝ p₂ p₃ p₃') :
  ∡ p₁ p₂ p₃ = ∡ p₁ p₂ p₃' :=
h.wbtw.oangle_eq_right h.ne_left

/-- An oriented angle is unchanged by replacing the first point with the midpoint of the segment
between it and the second point. -/
@[simp] lemma oangle_midpoint_left (p₁ p₂ p₃ : P) : ∡ (midpoint ℝ p₁ p₂) p₂ p₃ = ∡ p₁ p₂ p₃ :=
begin
  by_cases h : p₁ = p₂, { simp [h] },
  exact (sbtw_midpoint_of_ne ℝ h).symm.oangle_eq_left
end

/-- An oriented angle is unchanged by replacing the first point with the midpoint of the segment
between the second point and that point. -/
@[simp] lemma oangle_midpoint_rev_left (p₁ p₂ p₃ : P) : ∡ (midpoint ℝ p₂ p₁) p₂ p₃ = ∡ p₁ p₂ p₃ :=
by rw [midpoint_comm, oangle_midpoint_left]

/-- An oriented angle is unchanged by replacing the third point with the midpoint of the segment
between it and the second point. -/
@[simp] lemma oangle_midpoint_right (p₁ p₂ p₃ : P) : ∡ p₁ p₂ (midpoint ℝ p₃ p₂) = ∡ p₁ p₂ p₃ :=
begin
  by_cases h : p₃ = p₂, { simp [h] },
  exact (sbtw_midpoint_of_ne ℝ h).symm.oangle_eq_right
end

/-- An oriented angle is unchanged by replacing the third point with the midpoint of the segment
between the second point and that point. -/
@[simp] lemma oangle_midpoint_rev_right (p₁ p₂ p₃ : P) : ∡ p₁ p₂ (midpoint ℝ p₂ p₃) = ∡ p₁ p₂ p₃ :=
by rw [midpoint_comm, oangle_midpoint_right]

/-- Replacing the first point by one on the same line but the opposite ray adds π to the oriented
angle. -/
lemma _root_.sbtw.oangle_eq_add_pi_left {p₁ p₁' p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₁')
  (hp₃p₂ : p₃ ≠ p₂) : ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃ + π :=
by rw [←h.oangle₁₂₃_eq_pi, oangle_add_swap h.left_ne h.right_ne hp₃p₂]

/-- Replacing the third point by one on the same line but the opposite ray adds π to the oriented
angle. -/
lemma _root_.sbtw.oangle_eq_add_pi_right {p₁ p₂ p₃ p₃' : P} (h : sbtw ℝ p₃ p₂ p₃')
  (hp₁p₂ : p₁ ≠ p₂) : ∡ p₁ p₂ p₃ = ∡ p₁ p₂ p₃' + π :=
by rw [←h.oangle₃₂₁_eq_pi, oangle_add hp₁p₂ h.right_ne h.left_ne]

/-- Replacing both the first and third points by ones on the same lines but the opposite rays
does not change the oriented angle (vertically opposite angles). -/
lemma _root_.sbtw.oangle_eq_left_right {p₁ p₁' p₂ p₃ p₃' : P} (h₁ : sbtw ℝ p₁ p₂ p₁')
  (h₃ : sbtw ℝ p₃ p₂ p₃') : ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃' :=
by rw [h₁.oangle_eq_add_pi_left h₃.left_ne, h₃.oangle_eq_add_pi_right h₁.right_ne, add_assoc,
       real.angle.coe_pi_add_coe_pi, add_zero]

/-- Replacing the first point by one on the same line does not change twice the oriented angle. -/
lemma _root_.collinear.two_zsmul_oangle_eq_left {p₁ p₁' p₂ p₃ : P}
  (h : collinear ℝ ({p₁, p₂, p₁'} : set P)) (hp₁p₂ : p₁ ≠ p₂) (hp₁'p₂ : p₁' ≠ p₂) :
  (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₁' p₂ p₃ :=
begin
  by_cases hp₃p₂ : p₃ = p₂, { simp [hp₃p₂] },
  rcases h.wbtw_or_wbtw_or_wbtw with hw | hw | hw,
  { have hw' : sbtw ℝ p₁ p₂ p₁' := ⟨hw, hp₁p₂.symm, hp₁'p₂.symm⟩,
    rw [hw'.oangle_eq_add_pi_left hp₃p₂, smul_add, real.angle.two_zsmul_coe_pi, add_zero] },
  { rw hw.oangle_eq_left hp₁'p₂ },
  { rw hw.symm.oangle_eq_left hp₁p₂ }
end

/-- Replacing the third point by one on the same line does not change twice the oriented angle. -/
lemma _root_.collinear.two_zsmul_oangle_eq_right {p₁ p₂ p₃ p₃' : P}
  (h : collinear ℝ ({p₃, p₂, p₃'} : set P)) (hp₃p₂ : p₃ ≠ p₂) (hp₃'p₂ : p₃' ≠ p₂) :
  (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₁ p₂ p₃' :=
by rw [oangle_rev, smul_neg, h.two_zsmul_oangle_eq_left hp₃p₂ hp₃'p₂, ←smul_neg, ←oangle_rev]

/-- Two different points are equidistant from a third point if and only if that third point
equals some multiple of a `π / 2` rotation of the vector between those points, plus the midpoint
of those points. -/
lemma dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint {p₁ p₂ p : P} (h : p₁ ≠ p₂) :
  dist p₁ p = dist p₂ p ↔
    ∃ r : ℝ, r • ((o).rotation (π / 2 : ℝ) (p₂ -ᵥ p₁)) +ᵥ midpoint ℝ p₁ p₂ = p :=
begin
  refine ⟨λ hd, _, λ hr, _⟩,
  { have hi : ⟪p₂ -ᵥ p₁, p -ᵥ midpoint ℝ p₁ p₂⟫ = 0,
    { rw [@dist_eq_norm_vsub' V, @dist_eq_norm_vsub' V,
          ←mul_self_inj (norm_nonneg _) (norm_nonneg _), ←real_inner_self_eq_norm_mul_norm,
          ←real_inner_self_eq_norm_mul_norm] at hd,
      simp_rw [vsub_midpoint, ←vsub_sub_vsub_cancel_left p₂ p₁ p, inner_sub_left,
               inner_add_right, inner_smul_right, hd, real_inner_comm (p -ᵥ p₁)],
      abel },
    rw [@orientation.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two V _ _ _ o,
        or_iff_right (vsub_ne_zero.2 h.symm)] at hi,
    rcases hi with ⟨r, hr⟩,
    rw [eq_comm, ←eq_vadd_iff_vsub_eq] at hr,
    exact ⟨r, hr.symm⟩ },
  { rcases hr with ⟨r, rfl⟩,
    simp_rw [@dist_eq_norm_vsub V, vsub_vadd_eq_vsub_sub, left_vsub_midpoint,
             right_vsub_midpoint, inv_of_eq_inv, ←neg_vsub_eq_vsub_rev p₂ p₁,
             ←mul_self_inj (norm_nonneg _) (norm_nonneg _), ←real_inner_self_eq_norm_mul_norm,
             inner_sub_sub_self],
    simp [-neg_vsub_eq_vsub_rev] }
end

open affine_subspace

/-- Given two pairs of distinct points on the same line, such that the vectors between those
pairs of points are on the same ray (oriented in the same direction on that line), and a fifth
point, the angles at the fifth point between each of those two pairs of points have the same
sign. -/
lemma _root_.collinear.oangle_sign_of_same_ray_vsub {p₁ p₂ p₃ p₄ : P} (p₅ : P) (hp₁p₂ : p₁ ≠ p₂)
  (hp₃p₄ : p₃ ≠ p₄) (hc : collinear ℝ ({p₁, p₂, p₃, p₄} : set P))
  (hr : same_ray ℝ (p₂ -ᵥ p₁) (p₄ -ᵥ p₃)) : (∡ p₁ p₅ p₂).sign = (∡ p₃ p₅ p₄).sign :=
begin
  by_cases hc₅₁₂ : collinear ℝ ({p₅, p₁, p₂} : set P),
  { have hc₅₁₂₃₄ : collinear ℝ ({p₅, p₁, p₂, p₃, p₄} : set P) :=
      (hc.collinear_insert_iff_of_ne (set.mem_insert _ _)
                                     (set.mem_insert_of_mem _ (set.mem_insert _ _)) hp₁p₂).2 hc₅₁₂,
    have hc₅₃₄ : collinear ℝ ({p₅, p₃, p₄} : set P) :=
      (hc.collinear_insert_iff_of_ne
        (set.mem_insert_of_mem _ (set.mem_insert_of_mem _ (set.mem_insert _ _)))
        (set.mem_insert_of_mem _ (set.mem_insert_of_mem _ (set.mem_insert_of_mem _
          (set.mem_singleton _)))) hp₃p₄).1 hc₅₁₂₃₄,
    rw set.insert_comm at hc₅₁₂ hc₅₃₄,
    have hs₁₅₂ := oangle_eq_zero_or_eq_pi_iff_collinear.2 hc₅₁₂,
    have hs₃₅₄ := oangle_eq_zero_or_eq_pi_iff_collinear.2 hc₅₃₄,
    rw ←real.angle.sign_eq_zero_iff at hs₁₅₂ hs₃₅₄,
    rw [hs₁₅₂, hs₃₅₄] },
  { let s : set (P × P × P) :=
      (λ x : line[ℝ, p₁, p₂] × V, (x.1, p₅, x.2 +ᵥ x.1)) ''
        set.univ ×ˢ {v | same_ray ℝ (p₂ -ᵥ p₁) v ∧ v ≠ 0},
    have hco : is_connected s,
    { haveI : connected_space line[ℝ, p₁, p₂] := add_torsor.connected_space _ _,
      exact (is_connected_univ.prod (is_connected_set_of_same_ray_and_ne_zero
        (vsub_ne_zero.2 hp₁p₂.symm))).image _
          ((continuous_fst.subtype_coe.prod_mk
            (continuous_const.prod_mk
              (continuous_snd.vadd continuous_fst.subtype_coe))).continuous_on) },
    have hf : continuous_on (λ p : P × P × P, ∡ p.1 p.2.1 p.2.2) s,
    { refine continuous_at.continuous_on (λ p hp, continuous_at_oangle _ _),
      all_goals { simp_rw [s, set.mem_image, set.mem_prod, set.mem_univ, true_and,
                           prod.ext_iff] at hp,
                  obtain ⟨q₁, q₅, q₂⟩ := p,
                  dsimp only at ⊢ hp,
                  obtain ⟨⟨⟨q, hq⟩, v⟩, hv, rfl, rfl, rfl⟩ := hp,
                  dsimp only [subtype.coe_mk, set.mem_set_of] at ⊢ hv,
                  obtain ⟨hvr, -⟩ := hv,
                  rintro rfl,
                  refine hc₅₁₂ ((collinear_insert_iff_of_mem_affine_span _).2
                                  (collinear_pair _ _ _)) },
      { exact hq },
      { refine vadd_mem_of_mem_direction _ hq,
        rw ←exists_nonneg_left_iff_same_ray (vsub_ne_zero.2 hp₁p₂.symm) at hvr,
        obtain ⟨r, -, rfl⟩ := hvr,
        rw direction_affine_span,
        exact smul_vsub_rev_mem_vector_span_pair _ _ _ } },
    have hsp : ∀ p : P × P × P, p ∈ s → ∡ p.1 p.2.1 p.2.2 ≠ 0 ∧ ∡ p.1 p.2.1 p.2.2 ≠ π,
    { intros p hp,
      simp_rw [s, set.mem_image, set.mem_prod, set.mem_set_of, set.mem_univ, true_and,
               prod.ext_iff] at hp,
      obtain ⟨q₁, q₅, q₂⟩ := p,
      dsimp only at ⊢ hp,
      obtain ⟨⟨⟨q, hq⟩, v⟩, hv, rfl, rfl, rfl⟩ := hp,
      dsimp only [subtype.coe_mk, set.mem_set_of] at ⊢ hv,
      obtain ⟨hvr, hv0⟩ := hv,
      rw ←exists_nonneg_left_iff_same_ray (vsub_ne_zero.2 hp₁p₂.symm) at hvr,
      obtain ⟨r, -, rfl⟩ := hvr,
      change q ∈ line[ℝ, p₁, p₂] at hq,
      rw [oangle_ne_zero_and_ne_pi_iff_affine_independent],
      refine affine_independent_of_ne_of_mem_of_not_mem_of_mem _ hq
        (λ h, hc₅₁₂ ((collinear_insert_iff_of_mem_affine_span h).2 (collinear_pair _ _ _))) _,
      { rwa [←@vsub_ne_zero V, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, neg_ne_zero] },
      { refine vadd_mem_of_mem_direction _ hq,
        rw direction_affine_span,
        exact smul_vsub_rev_mem_vector_span_pair _ _ _ } },
    have hp₁p₂s : (p₁, p₅, p₂) ∈ s,
    { simp_rw [s, set.mem_image, set.mem_prod, set.mem_set_of, set.mem_univ, true_and,
               prod.ext_iff],
      refine ⟨⟨⟨p₁, left_mem_affine_span_pair _ _ _⟩, p₂ -ᵥ p₁⟩,
              ⟨same_ray.rfl, vsub_ne_zero.2 hp₁p₂.symm⟩, _⟩,
      simp },
    have hp₃p₄s : (p₃, p₅, p₄) ∈ s,
    { simp_rw [s, set.mem_image, set.mem_prod, set.mem_set_of, set.mem_univ, true_and,
               prod.ext_iff],
      refine ⟨⟨⟨p₃,
                hc.mem_affine_span_of_mem_of_ne
                  (set.mem_insert _ _)
                  (set.mem_insert_of_mem _ (set.mem_insert _ _))
                  (set.mem_insert_of_mem _ (set.mem_insert_of_mem _ (set.mem_insert _ _)))
                  hp₁p₂⟩, p₄ -ᵥ p₃⟩, ⟨hr, vsub_ne_zero.2 hp₃p₄.symm⟩, _⟩,
      simp },
    convert real.angle.sign_eq_of_continuous_on hco hf hsp hp₃p₄s hp₁p₂s }
end

/-- Given three points in strict order on the same line, and a fourth point, the angles at the
fourth point between the first and second or second and third points have the same sign. -/
lemma _root_.sbtw.oangle_sign_eq {p₁ p₂ p₃ : P} (p₄ : P) (h : sbtw ℝ p₁ p₂ p₃) :
  (∡ p₁ p₄ p₂).sign = (∡ p₂ p₄ p₃).sign :=
begin
  have hc : collinear ℝ ({p₁, p₂, p₂, p₃} : set P), { simpa using h.wbtw.collinear },
  exact hc.oangle_sign_of_same_ray_vsub _ h.left_ne h.ne_right h.wbtw.same_ray_vsub
end

/-- Given three points in weak order on the same line, with the first not equal to the second,
and a fourth point, the angles at the fourth point between the first and second or first and
third points have the same sign. -/
lemma _root_.wbtw.oangle_sign_eq_of_ne_left {p₁ p₂ p₃ : P} (p₄ : P) (h : wbtw ℝ p₁ p₂ p₃)
  (hne : p₁ ≠ p₂) : (∡ p₁ p₄ p₂).sign = (∡ p₁ p₄ p₃).sign :=
begin
  have hc : collinear ℝ ({p₁, p₂, p₁, p₃} : set P),
  { simpa [set.insert_comm p₂] using h.collinear },
  exact hc.oangle_sign_of_same_ray_vsub _ hne (h.left_ne_right_of_ne_left hne.symm)
    h.same_ray_vsub_left
end

/-- Given three points in strict order on the same line, and a fourth point, the angles at the
fourth point between the first and second or first and third points have the same sign. -/
lemma _root_.sbtw.oangle_sign_eq_left {p₁ p₂ p₃ : P} (p₄ : P) (h : sbtw ℝ p₁ p₂ p₃) :
  (∡ p₁ p₄ p₂).sign = (∡ p₁ p₄ p₃).sign :=
h.wbtw.oangle_sign_eq_of_ne_left _ h.left_ne

/-- Given three points in weak order on the same line, with the second not equal to the third,
and a fourth point, the angles at the fourth point between the second and third or first and
third points have the same sign. -/
lemma _root_.wbtw.oangle_sign_eq_of_ne_right {p₁ p₂ p₃ : P} (p₄ : P) (h : wbtw ℝ p₁ p₂ p₃)
  (hne : p₂ ≠ p₃) : (∡ p₂ p₄ p₃).sign = (∡ p₁ p₄ p₃).sign :=
by simp_rw [oangle_rev p₃, real.angle.sign_neg, h.symm.oangle_sign_eq_of_ne_left _ hne.symm]

/-- Given three points in strict order on the same line, and a fourth point, the angles at the
fourth point between the second and third or first and third points have the same sign. -/
lemma _root_.sbtw.oangle_sign_eq_right {p₁ p₂ p₃ : P} (p₄ : P) (h : sbtw ℝ p₁ p₂ p₃) :
  (∡ p₂ p₄ p₃).sign = (∡ p₁ p₄ p₃).sign :=
h.wbtw.oangle_sign_eq_of_ne_right _ h.ne_right

/-- Given two points in an affine subspace, the angles between those two points at two other
points on the same side of that subspace have the same sign. -/
lemma _root_.affine_subspace.s_same_side.oangle_sign_eq {s : affine_subspace ℝ P}
  {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃p₄ : s.s_same_side p₃ p₄) :
  (∡ p₁ p₄ p₂).sign = (∡ p₁ p₃ p₂).sign :=
begin
  by_cases h : p₁ = p₂, { simp [h] },
  let sp : set (P × P × P) := (λ p : P, (p₁, p, p₂)) '' {p | s.s_same_side p₃ p},
  have hc : is_connected sp := (is_connected_set_of_s_same_side hp₃p₄.2.1 hp₃p₄.nonempty).image
    _ (continuous_const.prod_mk (continuous.prod.mk_left _)).continuous_on,
  have hf : continuous_on (λ p : P × P × P, ∡ p.1 p.2.1 p.2.2) sp,
  { refine continuous_at.continuous_on (λ p hp, continuous_at_oangle _ _),
    all_goals { simp_rw [sp, set.mem_image, set.mem_set_of] at hp,
                obtain ⟨p', hp', rfl⟩ := hp,
                dsimp only,
                rintro rfl },
    { exact hp'.2.2 hp₁ },
    { exact hp'.2.2 hp₂ } },
  have hsp : ∀ p : P × P × P, p ∈ sp → ∡ p.1 p.2.1 p.2.2 ≠ 0 ∧ ∡ p.1 p.2.1 p.2.2 ≠ π,
  { intros p hp,
    simp_rw [sp, set.mem_image, set.mem_set_of] at hp,
    obtain ⟨p', hp', rfl⟩ := hp,
    dsimp only,
    rw [oangle_ne_zero_and_ne_pi_iff_affine_independent],
    exact affine_independent_of_ne_of_mem_of_not_mem_of_mem h hp₁ hp'.2.2 hp₂ },
  have hp₃ : (p₁, p₃, p₂) ∈ sp :=
    set.mem_image_of_mem _ (s_same_side_self_iff.2 ⟨hp₃p₄.nonempty, hp₃p₄.2.1⟩),
  have hp₄ : (p₁, p₄, p₂) ∈ sp := set.mem_image_of_mem _ hp₃p₄,
  convert real.angle.sign_eq_of_continuous_on hc hf hsp hp₃ hp₄
end

/-- Given two points in an affine subspace, the angles between those two points at two other
points on opposite sides of that subspace have opposite signs. -/
lemma _root_.affine_subspace.s_opp_side.oangle_sign_eq_neg {s : affine_subspace ℝ P}
  {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃p₄ : s.s_opp_side p₃ p₄) :
  (∡ p₁ p₄ p₂).sign = -(∡ p₁ p₃ p₂).sign :=
begin
  have hp₁p₃ : p₁ ≠ p₃, { rintro rfl, exact hp₃p₄.left_not_mem hp₁ },
  rw [←(hp₃p₄.symm.trans (s_opp_side_point_reflection hp₁ hp₃p₄.left_not_mem)).oangle_sign_eq
          hp₁ hp₂, ←oangle_rotate_sign p₁, ←oangle_rotate_sign p₁, oangle_swap₁₃_sign,
      (sbtw_point_reflection_of_ne ℝ hp₁p₃).symm.oangle_sign_eq _],
end

end euclidean_geometry
