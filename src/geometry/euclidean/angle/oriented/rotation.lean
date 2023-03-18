/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Heather Macbeth
-/
import geometry.euclidean.angle.oriented.basic

/-!
# Rotations by oriented angles.

This file defines rotations by oriented angles in real inner product spaces.

## Main definitions

* `orientation.rotation` is the rotation by an oriented angle with respect to an orientation.

-/

noncomputable theory

open finite_dimensional complex
open_locale real real_inner_product_space complex_conjugate

namespace orientation

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ
local attribute [instance] complex.finrank_real_complex_fact

variables {V V' : Type*} [inner_product_space ℝ V] [inner_product_space ℝ V']
variables [fact (finrank ℝ V = 2)] [fact (finrank ℝ V' = 2)] (o : orientation ℝ V (fin 2))

local notation `J` := o.right_angle_rotation

/-- Auxiliary construction to build a rotation by the oriented angle `θ`. -/
def rotation_aux (θ : real.angle) : V →ₗᵢ[ℝ] V :=
linear_map.isometry_of_inner
  (real.angle.cos θ • linear_map.id
        + real.angle.sin θ • ↑(linear_isometry_equiv.to_linear_equiv J))
  begin
    intros x y,
    simp only [is_R_or_C.conj_to_real, id.def, linear_map.smul_apply, linear_map.add_apply,
      linear_map.id_coe, linear_equiv.coe_coe, linear_isometry_equiv.coe_to_linear_equiv,
      orientation.area_form_right_angle_rotation_left,
      orientation.inner_right_angle_rotation_left,
      orientation.inner_right_angle_rotation_right,
      inner_add_left, inner_smul_left, inner_add_right, inner_smul_right],
    linear_combination inner x y * θ.cos_sq_add_sin_sq,
  end

@[simp] lemma rotation_aux_apply (θ : real.angle) (x : V) :
  o.rotation_aux θ x = real.angle.cos θ • x + real.angle.sin θ • J x :=
rfl

/-- A rotation by the oriented angle `θ`. -/
def rotation (θ : real.angle) : V ≃ₗᵢ[ℝ] V :=
linear_isometry_equiv.of_linear_isometry
  (o.rotation_aux θ)
  (real.angle.cos θ • linear_map.id - real.angle.sin θ • ↑(linear_isometry_equiv.to_linear_equiv J))
  begin
    ext x,
    convert congr_arg (λ t : ℝ, t • x) θ.cos_sq_add_sin_sq using 1,
    { simp only [o.right_angle_rotation_right_angle_rotation, o.rotation_aux_apply,
        function.comp_app, id.def, linear_equiv.coe_coe, linear_isometry.coe_to_linear_map,
        linear_isometry_equiv.coe_to_linear_equiv, map_smul, map_sub, linear_map.coe_comp,
        linear_map.id_coe, linear_map.smul_apply, linear_map.sub_apply, ← mul_smul, add_smul,
        smul_add, smul_neg, smul_sub, mul_comm, sq],
      abel },
    { simp },
  end
  begin
    ext x,
    convert congr_arg (λ t : ℝ, t • x) θ.cos_sq_add_sin_sq using 1,
    { simp only [o.right_angle_rotation_right_angle_rotation, o.rotation_aux_apply,
        function.comp_app, id.def, linear_equiv.coe_coe, linear_isometry.coe_to_linear_map,
        linear_isometry_equiv.coe_to_linear_equiv, map_add, map_smul, linear_map.coe_comp,
        linear_map.id_coe, linear_map.smul_apply, linear_map.sub_apply, add_smul, ← mul_smul,
        mul_comm, smul_add, smul_neg, sq],
      abel },
    { simp },
  end

lemma rotation_apply (θ : real.angle) (x : V) :
  o.rotation θ x = real.angle.cos θ • x + real.angle.sin θ • J x :=
rfl

lemma rotation_symm_apply (θ : real.angle) (x : V) :
  (o.rotation θ).symm x = real.angle.cos θ • x - real.angle.sin θ • J x :=
rfl

attribute [irreducible] rotation

lemma rotation_eq_matrix_to_lin (θ : real.angle) {x : V} (hx : x ≠ 0) :
  (o.rotation θ).to_linear_map
  = matrix.to_lin
      (o.basis_right_angle_rotation x hx) (o.basis_right_angle_rotation x hx)
      !![θ.cos, -θ.sin; θ.sin, θ.cos] :=
begin
  apply (o.basis_right_angle_rotation x hx).ext,
  intros i,
  fin_cases i,
  { rw matrix.to_lin_self,
    simp [rotation_apply, fin.sum_univ_succ] },
  { rw matrix.to_lin_self,
    simp [rotation_apply, fin.sum_univ_succ, add_comm] },
end

/-- The determinant of `rotation` (as a linear map) is equal to `1`. -/
@[simp] lemma det_rotation (θ : real.angle) :
  (o.rotation θ).to_linear_map.det = 1 :=
begin
  haveI : nontrivial V :=
    finite_dimensional.nontrivial_of_finrank_eq_succ (fact.out (finrank ℝ V = 2)),
  obtain ⟨x, hx⟩ : ∃ x, x ≠ (0:V) := exists_ne (0:V),
  rw o.rotation_eq_matrix_to_lin θ hx,
  simpa [sq] using θ.cos_sq_add_sin_sq,
end

/-- The determinant of `rotation` (as a linear equiv) is equal to `1`. -/
@[simp] lemma linear_equiv_det_rotation (θ : real.angle) :
  (o.rotation θ).to_linear_equiv.det = 1 :=
units.ext $ o.det_rotation θ

/-- The inverse of `rotation` is rotation by the negation of the angle. -/
@[simp] lemma rotation_symm (θ : real.angle) : (o.rotation θ).symm = o.rotation (-θ) :=
by ext; simp [o.rotation_apply, o.rotation_symm_apply, sub_eq_add_neg]

/-- Rotation by 0 is the identity. -/
@[simp] lemma rotation_zero : o.rotation 0 = linear_isometry_equiv.refl ℝ V :=
by ext; simp [rotation]

/-- Rotation by π is negation. -/
@[simp] lemma rotation_pi : o.rotation π = linear_isometry_equiv.neg ℝ :=
begin
  ext x,
  simp [rotation]
end

/-- Rotation by π is negation. -/
lemma rotation_pi_apply (x : V) : o.rotation π x = -x :=
by simp

/-- Rotation by π / 2 is the "right-angle-rotation" map `J`. -/
lemma rotation_pi_div_two : o.rotation (π / 2 : ℝ) = J :=
begin
  ext x,
  simp [rotation],
end

/-- Rotating twice is equivalent to rotating by the sum of the angles. -/
@[simp] lemma rotation_rotation (θ₁ θ₂ : real.angle) (x : V) :
  o.rotation θ₁ (o.rotation θ₂ x) = o.rotation (θ₁ + θ₂) x :=
begin
  simp only [o.rotation_apply, ←mul_smul, real.angle.cos_add, real.angle.sin_add, add_smul,
    sub_smul, linear_isometry_equiv.trans_apply, smul_add, linear_isometry_equiv.map_add,
    linear_isometry_equiv.map_smul, right_angle_rotation_right_angle_rotation, smul_neg],
  ring_nf,
  abel,
end

/-- Rotating twice is equivalent to rotating by the sum of the angles. -/
@[simp] lemma rotation_trans (θ₁ θ₂ : real.angle) :
  (o.rotation θ₁).trans (o.rotation θ₂) = o.rotation (θ₂ + θ₁) :=
linear_isometry_equiv.ext $ λ _, by rw [←rotation_rotation, linear_isometry_equiv.trans_apply]

/-- Rotating the first of two vectors by `θ` scales their Kahler form by `cos θ - sin θ * I`. -/
@[simp] lemma kahler_rotation_left (x y : V) (θ : real.angle) :
  o.kahler (o.rotation θ x) y = conj (θ.exp_map_circle : ℂ) * o.kahler x y :=
begin
  simp only [o.rotation_apply, map_add, map_mul, linear_map.map_smulₛₗ, ring_hom.id_apply,
    linear_map.add_apply, linear_map.smul_apply, real_smul, kahler_right_angle_rotation_left,
    real.angle.coe_exp_map_circle, is_R_or_C.conj_of_real, conj_I],
  ring,
end

/-- Negating a rotation is equivalent to rotation by π plus the angle. -/
lemma neg_rotation (θ : real.angle) (x : V) : -o.rotation θ x = o.rotation (π + θ) x :=
by rw [←o.rotation_pi_apply, rotation_rotation]

/-- Negating a rotation by -π / 2 is equivalent to rotation by π / 2. -/
@[simp] lemma neg_rotation_neg_pi_div_two (x : V) :
  -o.rotation (-π / 2 : ℝ) x = o.rotation (π / 2 : ℝ) x :=
by rw [neg_rotation, ←real.angle.coe_add, neg_div, ←sub_eq_add_neg, sub_half]

/-- Negating a rotation by π / 2 is equivalent to rotation by -π / 2. -/
lemma neg_rotation_pi_div_two (x : V) : -o.rotation (π / 2 : ℝ) x = o.rotation (-π / 2 : ℝ) x :=
(neg_eq_iff_eq_neg.mp $ o.neg_rotation_neg_pi_div_two _).symm

/-- Rotating the first of two vectors by `θ` scales their Kahler form by `cos (-θ) + sin (-θ) * I`.
-/
lemma kahler_rotation_left' (x y : V) (θ : real.angle) :
  o.kahler (o.rotation θ x) y = (-θ).exp_map_circle * o.kahler x y :=
by simpa [coe_inv_circle_eq_conj, -kahler_rotation_left] using o.kahler_rotation_left x y θ

/-- Rotating the second of two vectors by `θ` scales their Kahler form by `cos θ + sin θ * I`. -/
@[simp] lemma kahler_rotation_right (x y : V) (θ : real.angle) :
  o.kahler x (o.rotation θ y) = θ.exp_map_circle * o.kahler x y :=
begin
  simp only [o.rotation_apply, map_add, linear_map.map_smulₛₗ, ring_hom.id_apply, real_smul,
    kahler_right_angle_rotation_right, real.angle.coe_exp_map_circle],
  ring,
end

/-- Rotating the first vector by `θ` subtracts `θ` from the angle between two vectors. -/
@[simp] lemma oangle_rotation_left {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : real.angle) :
  o.oangle (o.rotation θ x) y = o.oangle x y - θ :=
begin
  simp only [oangle, o.kahler_rotation_left'],
  rw [complex.arg_mul_coe_angle, real.angle.arg_exp_map_circle],
  { abel },
  { exact ne_zero_of_mem_circle _ },
  { exact o.kahler_ne_zero hx hy },
end

/-- Rotating the second vector by `θ` adds `θ` to the angle between two vectors. -/
@[simp] lemma oangle_rotation_right {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : real.angle) :
  o.oangle x (o.rotation θ y) = o.oangle x y + θ :=
begin
  simp only [oangle, o.kahler_rotation_right],
  rw [complex.arg_mul_coe_angle, real.angle.arg_exp_map_circle],
  { abel },
  { exact ne_zero_of_mem_circle _ },
  { exact o.kahler_ne_zero hx hy },
end

/-- The rotation of a vector by `θ` has an angle of `-θ` from that vector. -/
@[simp] lemma oangle_rotation_self_left {x : V} (hx : x ≠ 0) (θ : real.angle) :
  o.oangle (o.rotation θ x) x = -θ :=
by simp [hx]

/-- A vector has an angle of `θ` from the rotation of that vector by `θ`. -/
@[simp] lemma oangle_rotation_self_right {x : V} (hx : x ≠ 0) (θ : real.angle) :
  o.oangle x (o.rotation θ x) = θ :=
by simp [hx]

/-- Rotating the first vector by the angle between the two vectors results an an angle of 0. -/
@[simp] lemma oangle_rotation_oangle_left (x y : V) :
  o.oangle (o.rotation (o.oangle x y) x) y = 0 :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  { by_cases hy : y = 0,
    { simp [hy] },
    { simp [hx, hy] } }
end

/-- Rotating the first vector by the angle between the two vectors and swapping the vectors
results an an angle of 0. -/
@[simp] lemma oangle_rotation_oangle_right (x y : V) :
  o.oangle y (o.rotation (o.oangle x y) x) = 0 :=
begin
  rw [oangle_rev],
  simp
end

/-- Rotating both vectors by the same angle does not change the angle between those vectors. -/
@[simp] lemma oangle_rotation (x y : V) (θ : real.angle) :
  o.oangle (o.rotation θ x) (o.rotation θ y) = o.oangle x y :=
begin
  by_cases hx : x = 0; by_cases hy : y = 0;
    simp [hx, hy]
end

/-- A rotation of a nonzero vector equals that vector if and only if the angle is zero. -/
@[simp] lemma rotation_eq_self_iff_angle_eq_zero {x : V} (hx : x ≠ 0) (θ : real.angle) :
  o.rotation θ x = x ↔ θ = 0 :=
begin
  split,
  { intro h,
    rw eq_comm,
    simpa [hx, h] using o.oangle_rotation_right hx hx θ },
  { intro h,
    simp [h] }
end

/-- A nonzero vector equals a rotation of that vector if and only if the angle is zero. -/
@[simp] lemma eq_rotation_self_iff_angle_eq_zero {x : V} (hx : x ≠ 0) (θ : real.angle) :
  x = o.rotation θ x ↔ θ = 0 :=
by rw [←o.rotation_eq_self_iff_angle_eq_zero hx, eq_comm]

/-- A rotation of a vector equals that vector if and only if the vector or the angle is zero. -/
lemma rotation_eq_self_iff (x : V) (θ : real.angle) :
  o.rotation θ x = x ↔ x = 0 ∨ θ = 0 :=
begin
  by_cases h : x = 0;
    simp [h]
end

/-- A vector equals a rotation of that vector if and only if the vector or the angle is zero. -/
lemma eq_rotation_self_iff (x : V) (θ : real.angle) :
  x = o.rotation θ x ↔ x = 0 ∨ θ = 0 :=
by rw [←rotation_eq_self_iff, eq_comm]

/-- Rotating a vector by the angle to another vector gives the second vector if and only if the
norms are equal. -/
@[simp] lemma rotation_oangle_eq_iff_norm_eq (x y : V) :
  o.rotation (o.oangle x y) x = y ↔ ‖x‖ = ‖y‖ :=
begin
  split,
  { intro h,
    rw [←h, linear_isometry_equiv.norm_map] },
  { intro h,
    rw o.eq_iff_oangle_eq_zero_of_norm_eq;
      simp [h] }
end

/-- The angle between two nonzero vectors is `θ` if and only if the second vector is the first
rotated by `θ` and scaled by the ratio of the norms. -/
lemma oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
  (θ : real.angle) : o.oangle x y = θ ↔ y = (‖y‖ / ‖x‖) • o.rotation θ x :=
begin
  have hp := div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx),
  split,
  { rintro rfl,
    rw [←linear_isometry_equiv.map_smul, ←o.oangle_smul_left_of_pos x y hp,
        eq_comm, rotation_oangle_eq_iff_norm_eq, norm_smul, real.norm_of_nonneg hp.le,
        div_mul_cancel _ (norm_ne_zero_iff.2 hx)] },
  { intro hye,
    rw [hye, o.oangle_smul_right_of_pos _ _ hp, o.oangle_rotation_self_right hx] }
end

/-- The angle between two nonzero vectors is `θ` if and only if the second vector is the first
rotated by `θ` and scaled by a positive real. -/
lemma oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
  (θ : real.angle) : o.oangle x y = θ ↔ ∃ r : ℝ, 0 < r ∧ y = r • o.rotation θ x :=
begin
  split,
  { intro h,
    rw o.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy at h,
    exact ⟨‖y‖ / ‖x‖, div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx), h⟩ },
  { rintro ⟨r, hr, rfl⟩,
    rw [o.oangle_smul_right_of_pos _ _ hr, o.oangle_rotation_self_right hx] }
end

/-- The angle between two vectors is `θ` if and only if they are nonzero and the second vector
is the first rotated by `θ` and scaled by the ratio of the norms, or `θ` and at least one of the
vectors are zero. -/
lemma oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero {x y : V} (θ : real.angle) :
  o.oangle x y = θ ↔
    (x ≠ 0 ∧ y ≠ 0 ∧ y = (‖y‖ / ‖x‖) • o.rotation θ x) ∨ (θ = 0 ∧ (x = 0 ∨ y = 0)) :=
begin
  by_cases hx : x = 0,
  { simp [hx, eq_comm] },
  { by_cases hy : y = 0,
    { simp [hy, eq_comm] },
    { rw o.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy,
      simp [hx, hy] } }
end

/-- The angle between two vectors is `θ` if and only if they are nonzero and the second vector
is the first rotated by `θ` and scaled by a positive real, or `θ` and at least one of the
vectors are zero. -/
lemma oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero {x y : V} (θ : real.angle) :
  o.oangle x y = θ ↔
    (x ≠ 0 ∧ y ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • o.rotation θ x) ∨ (θ = 0 ∧ (x = 0 ∨ y = 0)) :=
begin
  by_cases hx : x = 0,
  { simp [hx, eq_comm] },
  { by_cases hy : y = 0,
    { simp [hy, eq_comm] },
    { rw o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero hx hy,
      simp [hx, hy] } }
end

/-- Any linear isometric equivalence in `V` with positive determinant is `rotation`. -/
lemma exists_linear_isometry_equiv_eq_of_det_pos {f : V ≃ₗᵢ[ℝ] V}
  (hd : 0 < (f.to_linear_equiv : V →ₗ[ℝ] V).det) : ∃ θ : real.angle, f = o.rotation θ :=
begin
  haveI : nontrivial V :=
    finite_dimensional.nontrivial_of_finrank_eq_succ (fact.out (finrank ℝ V = 2)),
  obtain ⟨x, hx⟩ : ∃ x, x ≠ (0:V) := exists_ne (0:V),
  use o.oangle x (f x),
  apply linear_isometry_equiv.to_linear_equiv_injective,
  apply linear_equiv.to_linear_map_injective,
  apply (o.basis_right_angle_rotation x hx).ext,
  intros i,
  symmetry,
  fin_cases i,
  { simp },
  have : o.oangle (J x) (f (J x)) = o.oangle x (f x),
  { simp only [oangle, o.linear_isometry_equiv_comp_right_angle_rotation f hd,
      o.kahler_comp_right_angle_rotation] },
  simp [← this],
end

lemma rotation_map (θ : real.angle) (f : V ≃ₗᵢ[ℝ] V') (x : V') :
  (orientation.map (fin 2) f.to_linear_equiv o).rotation θ x
  = f (o.rotation θ (f.symm x)) :=
by simp [rotation_apply, o.right_angle_rotation_map]

@[simp] protected lemma _root_.complex.rotation (θ : real.angle) (z : ℂ) :
  complex.orientation.rotation θ z = θ.exp_map_circle * z :=
begin
  simp only [rotation_apply, complex.right_angle_rotation, real.angle.coe_exp_map_circle,
    real_smul],
  ring
end

/-- Rotation in an oriented real inner product space of dimension 2 can be evaluated in terms of a
complex-number representation of the space. -/
lemma rotation_map_complex (θ : real.angle) (f : V ≃ₗᵢ[ℝ] ℂ)
  (hf : (orientation.map (fin 2) f.to_linear_equiv o) = complex.orientation) (x : V) :
  f (o.rotation θ x) = θ.exp_map_circle * f x :=
begin
  rw [← complex.rotation, ← hf, o.rotation_map],
  simp,
end

/-- Negating the orientation negates the angle in `rotation`. -/
lemma rotation_neg_orientation_eq_neg (θ : real.angle) :
  (-o).rotation θ = o.rotation (-θ) :=
linear_isometry_equiv.ext $ by simp [rotation_apply]

/-- The inner product between a `π / 2` rotation of a vector and that vector is zero. -/
@[simp] lemma inner_rotation_pi_div_two_left (x : V) : ⟪o.rotation (π / 2 : ℝ) x, x⟫ = 0 :=
by rw [rotation_pi_div_two, inner_right_angle_rotation_self]

/-- The inner product between a vector and a `π / 2` rotation of that vector is zero. -/
@[simp] lemma inner_rotation_pi_div_two_right (x : V) : ⟪x, o.rotation (π / 2 : ℝ) x⟫ = 0 :=
by rw [real_inner_comm, inner_rotation_pi_div_two_left]

/-- The inner product between a multiple of a `π / 2` rotation of a vector and that vector is
zero. -/
@[simp] lemma inner_smul_rotation_pi_div_two_left (x : V) (r : ℝ) :
  ⟪r • o.rotation (π / 2 : ℝ) x, x⟫ = 0 :=
by rw [inner_smul_left, inner_rotation_pi_div_two_left, mul_zero]

/-- The inner product between a vector and a multiple of a `π / 2` rotation of that vector is
zero. -/
@[simp] lemma inner_smul_rotation_pi_div_two_right (x : V) (r : ℝ) :
  ⟪x, r • o.rotation (π / 2 : ℝ) x⟫ = 0 :=
by rw [real_inner_comm, inner_smul_rotation_pi_div_two_left]

/-- The inner product between a `π / 2` rotation of a vector and a multiple of that vector is
zero. -/
@[simp] lemma inner_rotation_pi_div_two_left_smul (x : V) (r : ℝ) :
  ⟪o.rotation (π / 2 : ℝ) x, r • x⟫ = 0 :=
by rw [inner_smul_right, inner_rotation_pi_div_two_left, mul_zero]

/-- The inner product between a multiple of a vector and a `π / 2` rotation of that vector is
zero. -/
@[simp] lemma inner_rotation_pi_div_two_right_smul (x : V) (r : ℝ) :
  ⟪r • x, o.rotation (π / 2 : ℝ) x⟫ = 0 :=
by rw [real_inner_comm, inner_rotation_pi_div_two_left_smul]

/-- The inner product between a multiple of a `π / 2` rotation of a vector and a multiple of
that vector is zero. -/
@[simp] lemma inner_smul_rotation_pi_div_two_smul_left (x : V) (r₁ r₂ : ℝ) :
  ⟪r₁ • o.rotation (π / 2 : ℝ) x, r₂ • x⟫ = 0 :=
by rw [inner_smul_right, inner_smul_rotation_pi_div_two_left, mul_zero]

/-- The inner product between a multiple of a vector and a multiple of a `π / 2` rotation of
that vector is zero. -/
@[simp] lemma inner_smul_rotation_pi_div_two_smul_right (x : V) (r₁ r₂ : ℝ) :
  ⟪r₂ • x, r₁ • o.rotation (π / 2 : ℝ) x⟫ = 0 :=
by rw [real_inner_comm, inner_smul_rotation_pi_div_two_smul_left]

/-- The inner product between two vectors is zero if and only if the first vector is zero or
the second is a multiple of a `π / 2` rotation of that vector. -/
lemma inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two {x y : V} :
  ⟪x, y⟫ = 0 ↔ (x = 0 ∨ ∃ r : ℝ, r • o.rotation (π / 2 : ℝ) x = y) :=
begin
  rw ←o.eq_zero_or_oangle_eq_iff_inner_eq_zero,
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with rfl | rfl | h | h,
    { exact or.inl rfl },
    { exact or.inr ⟨0, zero_smul _ _⟩ },
    { obtain ⟨r, hr, rfl⟩ := (o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero
        (o.left_ne_zero_of_oangle_eq_pi_div_two h)
        (o.right_ne_zero_of_oangle_eq_pi_div_two h) _).1 h,
      exact or.inr ⟨r, rfl⟩ },
    { obtain ⟨r, hr, rfl⟩ := (o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero
        (o.left_ne_zero_of_oangle_eq_neg_pi_div_two h)
        (o.right_ne_zero_of_oangle_eq_neg_pi_div_two h) _).1 h,
      refine or.inr ⟨-r, _⟩,
      rw [neg_smul, ←smul_neg, o.neg_rotation_pi_div_two] } },
  { rcases h with rfl | ⟨r, rfl⟩,
    { exact or.inl rfl },
    { by_cases hx : x = 0, { exact or.inl hx },
      rcases lt_trichotomy r 0 with hr | rfl | hr,
      { refine or.inr (or.inr (or.inr _)),
        rw [o.oangle_smul_right_of_neg _ _ hr, o.neg_rotation_pi_div_two,
            o.oangle_rotation_self_right hx] },
      { exact or.inr (or.inl (zero_smul _ _)) },
      { refine or.inr (or.inr (or.inl _)),
        rw [o.oangle_smul_right_of_pos _ _ hr, o.oangle_rotation_self_right hx] } } }
end

end orientation
