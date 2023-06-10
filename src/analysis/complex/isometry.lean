/-
Copyright (c) 2021 François Sunatori. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François Sunatori
-/
import analysis.complex.circle
import linear_algebra.determinant
import linear_algebra.matrix.general_linear_group

/-!
# Isometries of the Complex Plane

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The lemma `linear_isometry_complex` states the classification of isometries in the complex plane.
Specifically, isometries with rotations but without translation.
The proof involves:
1. creating a linear isometry `g` with two fixed points, `g(0) = 0`, `g(1) = 1`
2. applying `linear_isometry_complex_aux` to `g`
The proof of `linear_isometry_complex_aux` is separated in the following parts:
1. show that the real parts match up: `linear_isometry.re_apply_eq_re`
2. show that I maps to either I or -I
3. every z is a linear combination of a + b * I

## References

* [Isometries of the Complex Plane](http://helmut.knaust.info/mediawiki/images/b/b5/Iso.pdf)
-/
noncomputable theory

open complex
open_locale complex_conjugate

local notation (name := complex.abs) `|` x `|` := complex.abs x

/-- An element of the unit circle defines a `linear_isometry_equiv` from `ℂ` to itself, by
rotation. -/
def rotation : circle →* (ℂ ≃ₗᵢ[ℝ] ℂ) :=
{ to_fun := λ a,
  { norm_map' := λ x, show |a * x| = |x|, by rw [map_mul, abs_coe_circle, one_mul],
    ..distrib_mul_action.to_linear_equiv ℝ ℂ a },
  map_one' := linear_isometry_equiv.ext $ one_smul _,
  map_mul' := λ _ _, linear_isometry_equiv.ext $ mul_smul _ _ }

@[simp] lemma rotation_apply (a : circle) (z : ℂ) : rotation a z = a * z := rfl

@[simp] lemma rotation_symm (a : circle) : (rotation a).symm = rotation a⁻¹ :=
linear_isometry_equiv.ext $ λ x, rfl

@[simp] lemma rotation_trans (a b : circle) :
  (rotation a).trans (rotation b) = rotation (b * a) :=
by { ext1, simp }

lemma rotation_ne_conj_lie (a : circle) : rotation a ≠ conj_lie :=
begin
  intro h,
  have h1 : rotation a 1 = conj 1 := linear_isometry_equiv.congr_fun h 1,
  have hI : rotation a I = conj I := linear_isometry_equiv.congr_fun h I,
  rw [rotation_apply, ring_hom.map_one, mul_one] at h1,
  rw [rotation_apply, conj_I, ← neg_one_mul, mul_left_inj' I_ne_zero, h1, eq_neg_self_iff] at hI,
  exact one_ne_zero hI,
end

/-- Takes an element of `ℂ ≃ₗᵢ[ℝ] ℂ` and checks if it is a rotation, returns an element of the
unit circle. -/
@[simps]
def rotation_of (e : ℂ ≃ₗᵢ[ℝ] ℂ) : circle :=
⟨(e 1) / complex.abs (e 1), by simp⟩

@[simp]
lemma rotation_of_rotation (a : circle) : rotation_of (rotation a) = a :=
subtype.ext $ by simp

lemma rotation_injective : function.injective rotation :=
function.left_inverse.injective rotation_of_rotation

lemma linear_isometry.re_apply_eq_re_of_add_conj_eq (f : ℂ →ₗᵢ[ℝ] ℂ)
  (h₃ : ∀ z, z + conj z = f z + conj (f z)) (z : ℂ) : (f z).re = z.re :=
by simpa [ext_iff, add_re, add_im, conj_re, conj_im, ←two_mul,
         (show (2 : ℝ) ≠ 0, by simp [two_ne_zero])] using (h₃ z).symm

lemma linear_isometry.im_apply_eq_im_or_neg_of_re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ}
  (h₂ : ∀ z, (f z).re = z.re) (z : ℂ) :
  (f z).im = z.im ∨ (f z).im = -z.im :=
begin
  have h₁ := f.norm_map z,
  simp only [complex.abs_def, norm_eq_abs] at h₁,
  rwa [real.sqrt_inj (norm_sq_nonneg _) (norm_sq_nonneg _), norm_sq_apply (f z), norm_sq_apply z,
    h₂, add_left_cancel_iff, mul_self_eq_mul_self_iff] at h₁,
end

lemma linear_isometry.im_apply_eq_im {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) :
  z + conj z = f z + conj (f z) :=
begin
  have : ‖f z - 1‖ = ‖z - 1‖ := by rw [← f.norm_map (z - 1), f.map_sub, h],
  apply_fun λ x, x ^ 2 at this,
  simp only [norm_eq_abs, ←norm_sq_eq_abs] at this,
  rw [←of_real_inj, ←mul_conj, ←mul_conj] at this,
  rw [ring_hom.map_sub, ring_hom.map_sub] at this,
  simp only [sub_mul, mul_sub, one_mul, mul_one] at this,
  rw [mul_conj, norm_sq_eq_abs, ←norm_eq_abs, linear_isometry.norm_map] at this,
  rw [mul_conj, norm_sq_eq_abs, ←norm_eq_abs] at this,
  simp only [sub_sub, sub_right_inj, mul_one, of_real_pow, ring_hom.map_one, norm_eq_abs] at this,
  simp only [add_sub, sub_left_inj] at this,
  rw [add_comm, ←this, add_comm],
end

lemma linear_isometry.re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) : (f z).re = z.re :=
begin
  apply linear_isometry.re_apply_eq_re_of_add_conj_eq,
  intro z,
  apply linear_isometry.im_apply_eq_im h,
end

lemma linear_isometry_complex_aux {f : ℂ ≃ₗᵢ[ℝ] ℂ} (h : f 1 = 1) :
  f = linear_isometry_equiv.refl ℝ ℂ ∨ f = conj_lie :=
begin
  have h0 : f I = I ∨ f I = -I,
  { have : |f I| = 1 := by simpa using f.norm_map complex.I,
    simp only [ext_iff, ←and_or_distrib_left, neg_re, I_re, neg_im, neg_zero],
    split,
    { rw ←I_re,
      exact @linear_isometry.re_apply_eq_re f.to_linear_isometry h I, },
    { apply @linear_isometry.im_apply_eq_im_or_neg_of_re_apply_eq_re f.to_linear_isometry,
      intro z, rw @linear_isometry.re_apply_eq_re f.to_linear_isometry h } },
  refine h0.imp (λ h' : f I = I, _) (λ h' : f I = -I, _);
  { apply linear_isometry_equiv.to_linear_equiv_injective,
    apply complex.basis_one_I.ext',
    intros i,
    fin_cases i; simp [h, h'] }
end

lemma linear_isometry_complex (f : ℂ ≃ₗᵢ[ℝ] ℂ) :
  ∃ a : circle, f = rotation a ∨ f = conj_lie.trans (rotation a) :=
begin
  let a : circle := ⟨f 1, by simpa using f.norm_map 1⟩,
  use a,
  have : (f.trans (rotation a).symm) 1 = 1,
  { simpa using rotation_apply a⁻¹ (f 1) },
  refine (linear_isometry_complex_aux this).imp (λ h₁, _) (λ h₂, _),
  { simpa using eq_mul_of_inv_mul_eq h₁ },
  { exact eq_mul_of_inv_mul_eq h₂ }
end

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
