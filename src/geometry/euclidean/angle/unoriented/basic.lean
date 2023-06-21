/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
import analysis.inner_product_space.basic
import analysis.special_functions.trigonometric.inverse

/-!
# Angles between vectors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines unoriented angles in real inner product spaces.

## Main definitions

* `inner_product_geometry.angle` is the undirected angle between two vectors.

-/

assert_not_exists has_fderiv_at
assert_not_exists conformal_at

noncomputable theory
open real set
open_locale big_operators
open_locale real
open_locale real_inner_product_space

namespace inner_product_geometry

variables {V : Type*} [normed_add_comm_group V] [inner_product_space ℝ V] {x y : V}

/-- The undirected angle between two vectors. If either vector is 0,
this is π/2. See `orientation.oangle` for the corresponding oriented angle
definition. -/
def angle (x y : V) : ℝ := real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖))

lemma continuous_at_angle {x : V × V} (hx1 : x.1 ≠ 0) (hx2 : x.2 ≠ 0) :
  continuous_at (λ y : V × V, angle y.1 y.2) x :=
real.continuous_arccos.continuous_at.comp $ continuous_inner.continuous_at.div
  ((continuous_norm.comp continuous_fst).mul (continuous_norm.comp continuous_snd)).continuous_at
  (by simp [hx1, hx2])

lemma angle_smul_smul {c : ℝ} (hc : c ≠ 0) (x y : V) :
  angle (c • x) (c • y) = angle x y :=
have c * c ≠ 0, from mul_ne_zero hc hc,
by rw [angle, angle, real_inner_smul_left, inner_smul_right, norm_smul, norm_smul, real.norm_eq_abs,
  mul_mul_mul_comm _ (‖x‖), abs_mul_abs_self, ← mul_assoc c c, mul_div_mul_left _ _ this]

@[simp] lemma _root_.linear_isometry.angle_map {E F : Type*}
  [normed_add_comm_group E] [normed_add_comm_group F]
  [inner_product_space ℝ E] [inner_product_space ℝ F] (f : E →ₗᵢ[ℝ] F) (u v : E) :
  angle (f u) (f v) = angle u v :=
by rw [angle, angle, f.inner_map_map, f.norm_map, f.norm_map]

@[simp, norm_cast] lemma _root_.submodule.angle_coe {s : submodule ℝ V} (x y : s) :
  angle (x : V) (y : V) = angle x y :=
s.subtypeₗᵢ.angle_map x y

/-- The cosine of the angle between two vectors. -/
lemma cos_angle (x y : V) : real.cos (angle x y) = ⟪x, y⟫ / (‖x‖ * ‖y‖) :=
real.cos_arccos (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1
                (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2

/-- The angle between two vectors does not depend on their order. -/
lemma angle_comm (x y : V) : angle x y = angle y x :=
begin
  unfold angle,
  rw [real_inner_comm, mul_comm]
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
  rw [←real_inner_self_eq_norm_mul_norm, div_self (inner_self_ne_zero.2 hx : ⟪x, x⟫ ≠ 0),
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
lemma cos_angle_mul_norm_mul_norm (x y : V) : real.cos (angle x y) * (‖x‖ * ‖y‖) = ⟪x, y⟫ :=
begin
  rw [cos_angle, div_mul_cancel_of_imp],
  simp [or_imp_distrib] { contextual := tt },
end

/-- The sine of the angle between two vectors, multiplied by the
product of their norms. -/
lemma sin_angle_mul_norm_mul_norm (x y : V) : real.sin (angle x y) * (‖x‖ * ‖y‖) =
    real.sqrt (⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫) :=
begin
  unfold angle,
  rw [real.sin_arccos,
      ←real.sqrt_mul_self (mul_nonneg (norm_nonneg x) (norm_nonneg y)),
      ←real.sqrt_mul' _ (mul_self_nonneg _), sq,
      real.sqrt_mul_self (mul_nonneg (norm_nonneg x) (norm_nonneg y)),
      real_inner_self_eq_norm_mul_norm,
      real_inner_self_eq_norm_mul_norm],
  by_cases h : (‖x‖ * ‖y‖) = 0,
  { rw [(show ‖x‖ * ‖x‖ * (‖y‖ * ‖y‖) = (‖x‖ * ‖y‖) * (‖x‖ * ‖y‖), by ring), h, mul_zero, mul_zero,
        zero_sub],
    cases eq_zero_or_eq_zero_of_mul_eq_zero h with hx hy,
    { rw norm_eq_zero at hx,
      rw [hx, inner_zero_left, zero_mul, neg_zero] },
    { rw norm_eq_zero at hy,
      rw [hy, inner_zero_right, zero_mul, neg_zero] } },
  { field_simp [h], ring_nf }
end

/-- The angle between two vectors is zero if and only if they are
nonzero and one is a positive multiple of the other. -/
lemma angle_eq_zero_iff {x y : V} : angle x y = 0 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), 0 < r ∧ y = r • x) :=
begin
  rw [angle, ← real_inner_div_norm_mul_norm_eq_one_iff, real.arccos_eq_zero, has_le.le.le_iff_eq,
    eq_comm],
  exact (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2
end

/-- The angle between two vectors is π if and only if they are nonzero
and one is a negative multiple of the other. -/
lemma angle_eq_pi_iff {x y : V} : angle x y = π ↔ (x ≠ 0 ∧ ∃ (r : ℝ), r < 0 ∧ y = r • x) :=
begin
  rw [angle, ← real_inner_div_norm_mul_norm_eq_neg_one_iff, real.arccos_eq_pi, has_le.le.le_iff_eq],
  exact (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1
end

/-- If the angle between two vectors is π, the angles between those
vectors and a third vector add to π. -/
lemma angle_add_angle_eq_pi_of_angle_eq_pi {x y : V} (z : V) (h : angle x y = π) :
  angle x z + angle y z = π :=
begin
  rcases angle_eq_pi_iff.1 h with ⟨hx, ⟨r, ⟨hr, rfl⟩⟩⟩,
  rw [angle_smul_left_of_neg x z hr, angle_neg_left, add_sub_cancel'_right]
end

/-- Two vectors have inner product 0 if and only if the angle between
them is π/2. -/
lemma inner_eq_zero_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2 :=
iff.symm $ by simp [angle, or_imp_distrib] { contextual := tt }

/-- If the angle between two vectors is π, the inner product equals the negative product
of the norms. -/
lemma inner_eq_neg_mul_norm_of_angle_eq_pi {x y : V} (h : angle x y = π) : ⟪x, y⟫ = - (‖x‖ * ‖y‖) :=
by simp [← cos_angle_mul_norm_mul_norm, h]

/-- If the angle between two vectors is 0, the inner product equals the product of the norms. -/
lemma inner_eq_mul_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) : ⟪x, y⟫ = ‖x‖ * ‖y‖ :=
by simp [← cos_angle_mul_norm_mul_norm, h]

/-- The inner product of two non-zero vectors equals the negative product of their norms
if and only if the angle between the two vectors is π. -/
lemma inner_eq_neg_mul_norm_iff_angle_eq_pi {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  ⟪x, y⟫ = - (‖x‖ * ‖y‖) ↔ angle x y = π :=
begin
  refine ⟨λ h, _, inner_eq_neg_mul_norm_of_angle_eq_pi⟩,
  have h₁ : (‖x‖ * ‖y‖) ≠ 0 := (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)).ne',
  rw [angle, h, neg_div, div_self h₁, real.arccos_neg_one],
end

/-- The inner product of two non-zero vectors equals the product of their norms
if and only if the angle between the two vectors is 0. -/
lemma inner_eq_mul_norm_iff_angle_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  ⟪x, y⟫ = ‖x‖ * ‖y‖ ↔ angle x y = 0 :=
begin
  refine ⟨λ h, _, inner_eq_mul_norm_of_angle_eq_zero⟩,
  have h₁ : (‖x‖ * ‖y‖) ≠ 0 := (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)).ne',
  rw [angle, h, div_self h₁, real.arccos_one],
end

/-- If the angle between two vectors is π, the norm of their difference equals
the sum of their norms. -/
lemma norm_sub_eq_add_norm_of_angle_eq_pi {x y : V} (h : angle x y = π) : ‖x - y‖ = ‖x‖ + ‖y‖ :=
begin
  rw ← sq_eq_sq (norm_nonneg (x - y)) (add_nonneg (norm_nonneg x) (norm_nonneg y)),
  rw [norm_sub_pow_two_real, inner_eq_neg_mul_norm_of_angle_eq_pi h],
  ring,
end

/-- If the angle between two vectors is 0, the norm of their sum equals
the sum of their norms. -/
lemma norm_add_eq_add_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) : ‖x + y‖ = ‖x‖ + ‖y‖ :=
begin
  rw ← sq_eq_sq (norm_nonneg (x + y)) (add_nonneg (norm_nonneg x) (norm_nonneg y)),
  rw [norm_add_pow_two_real, inner_eq_mul_norm_of_angle_eq_zero h],
  ring,
end

/-- If the angle between two vectors is 0, the norm of their difference equals
the absolute value of the difference of their norms. -/
lemma norm_sub_eq_abs_sub_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) :
  ‖x - y‖ = |‖x‖ - ‖y‖| :=
begin
  rw [← sq_eq_sq (norm_nonneg (x - y)) (abs_nonneg (‖x‖ - ‖y‖)),
      norm_sub_pow_two_real, inner_eq_mul_norm_of_angle_eq_zero h, sq_abs (‖x‖ - ‖y‖)],
  ring,
end

/-- The norm of the difference of two non-zero vectors equals the sum of their norms
if and only the angle between the two vectors is π. -/
lemma norm_sub_eq_add_norm_iff_angle_eq_pi {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  ‖x - y‖ = ‖x‖ + ‖y‖ ↔ angle x y = π :=
begin
  refine ⟨λ h, _, norm_sub_eq_add_norm_of_angle_eq_pi⟩,
  rw ← inner_eq_neg_mul_norm_iff_angle_eq_pi hx hy,
  obtain ⟨hxy₁, hxy₂⟩ := ⟨norm_nonneg (x - y), add_nonneg (norm_nonneg x) (norm_nonneg y)⟩,
  rw [← sq_eq_sq hxy₁ hxy₂, norm_sub_pow_two_real] at h,
  calc ⟪x, y⟫ = (‖x‖ ^ 2 + ‖y‖ ^ 2 - (‖x‖ + ‖y‖) ^ 2) / 2 : by linarith
  ...         = -(‖x‖ * ‖y‖) : by ring,
end

/-- The norm of the sum of two non-zero vectors equals the sum of their norms
if and only the angle between the two vectors is 0. -/
lemma norm_add_eq_add_norm_iff_angle_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  ‖x + y‖ = ‖x‖ + ‖y‖ ↔ angle x y = 0 :=
begin
  refine ⟨λ h, _, norm_add_eq_add_norm_of_angle_eq_zero⟩,
  rw ← inner_eq_mul_norm_iff_angle_eq_zero hx hy,
  obtain ⟨hxy₁, hxy₂⟩ := ⟨norm_nonneg (x + y), add_nonneg (norm_nonneg x) (norm_nonneg y)⟩,
  rw [← sq_eq_sq hxy₁ hxy₂, norm_add_pow_two_real] at h,
  calc ⟪x, y⟫ = ((‖x‖ + ‖y‖) ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2)/ 2 : by linarith
  ...         = ‖x‖ * ‖y‖ : by ring,
end

/-- The norm of the difference of two non-zero vectors equals the absolute value
of the difference of their norms if and only the angle between the two vectors is 0. -/
lemma norm_sub_eq_abs_sub_norm_iff_angle_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  ‖x - y‖ = |‖x‖ - ‖y‖| ↔ angle x y = 0 :=
begin
  refine ⟨λ h, _, norm_sub_eq_abs_sub_norm_of_angle_eq_zero⟩,
  rw ← inner_eq_mul_norm_iff_angle_eq_zero hx hy,
  have h1 : ‖x - y‖ ^ 2 = (‖x‖ - ‖y‖) ^ 2, { rw h, exact sq_abs (‖x‖ - ‖y‖) },
  rw norm_sub_pow_two_real at h1,
  calc ⟪x, y⟫ = ((‖x‖ + ‖y‖) ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2)/ 2 : by linarith
  ...         = ‖x‖ * ‖y‖ : by ring,
end

/-- The norm of the sum of two vectors equals the norm of their difference if and only if
the angle between them is π/2. -/
lemma norm_add_eq_norm_sub_iff_angle_eq_pi_div_two (x y : V) :
  ‖x + y‖ = ‖x - y‖ ↔ angle x y = π / 2 :=
begin
  rw [← sq_eq_sq (norm_nonneg (x + y)) (norm_nonneg (x - y)),
      ← inner_eq_zero_iff_angle_eq_pi_div_two x y, norm_add_pow_two_real, norm_sub_pow_two_real],
  split; intro h; linarith,
end

/-- The cosine of the angle between two vectors is 1 if and only if the angle is 0. -/
lemma cos_eq_one_iff_angle_eq_zero : cos (angle x y) = 1 ↔ angle x y = 0 :=
begin
  rw ← cos_zero,
  exact inj_on_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩ (left_mem_Icc.2 pi_pos.le),
end

/-- The cosine of the angle between two vectors is 0 if and only if the angle is π / 2. -/
lemma cos_eq_zero_iff_angle_eq_pi_div_two : cos (angle x y) = 0 ↔ angle x y = π / 2 :=
begin
  rw ← cos_pi_div_two,
  apply inj_on_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩,
  split; linarith [pi_pos],
end

/-- The cosine of the angle between two vectors is -1 if and only if the angle is π. -/
lemma cos_eq_neg_one_iff_angle_eq_pi : cos (angle x y) = -1 ↔ angle x y = π :=
begin
  rw ← cos_pi,
  exact inj_on_cos.eq_iff ⟨angle_nonneg x y, angle_le_pi x y⟩ (right_mem_Icc.2 pi_pos.le),
end

/-- The sine of the angle between two vectors is 0 if and only if the angle is 0 or π. -/
lemma sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi :
  sin (angle x y) = 0 ↔ angle x y = 0 ∨ angle x y = π :=
by rw [sin_eq_zero_iff_cos_eq, cos_eq_one_iff_angle_eq_zero, cos_eq_neg_one_iff_angle_eq_pi]

/-- The sine of the angle between two vectors is 1 if and only if the angle is π / 2. -/
lemma sin_eq_one_iff_angle_eq_pi_div_two : sin (angle x y) = 1 ↔ angle x y = π / 2 :=
begin
  refine ⟨λ h, _, λ h, by rw [h, sin_pi_div_two]⟩,
  rw [←cos_eq_zero_iff_angle_eq_pi_div_two, ←abs_eq_zero, abs_cos_eq_sqrt_one_sub_sin_sq, h],
  simp,
end

end inner_product_geometry
