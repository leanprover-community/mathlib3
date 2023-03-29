/-
Copyright (c) 2021 François Sunatori. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François Sunatori
-/
import analysis.complex.isometry
import linear_algebra.matrix.general_linear_group

/-!
# Isometries of the Complex Plane as Matrix Rotations

Matrix representation of rotations.

-/

open complex

/-- The matrix representation of `rotation a` is equal to the conformal matrix
`!![re a, -im a; im a, re a]`. -/
lemma to_matrix_rotation (a : circle) :
  linear_map.to_matrix basis_one_I basis_one_I (rotation a).to_linear_equiv =
    matrix.plane_conformal_matrix (re a) (im a) (by simp [pow_two, ←norm_sq_apply]) :=
begin
  ext i j,
  simp [linear_map.to_matrix_apply],
  fin_cases i; fin_cases j; simp
end

/-- The determinant of `rotation` (as a linear map) is equal to `1`. -/
@[simp] lemma det_rotation (a : circle) : ((rotation a).to_linear_equiv : ℂ →ₗ[ℝ] ℂ).det = 1 :=
begin
  rw [←linear_map.det_to_matrix basis_one_I, to_matrix_rotation, matrix.det_fin_two],
  simp [←norm_sq_apply]
end

/-- The determinant of `rotation` (as a linear equiv) is equal to `1`. -/
@[simp] lemma linear_equiv_det_rotation (a : circle) : (rotation a).to_linear_equiv.det = 1 :=
by rw [←units.eq_iff, linear_equiv.coe_det, det_rotation, units.coe_one]
