/-
Copyright (c) 2021 François Sunatori. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François Sunatori, Shadman Sakib
-/
import analysis.complex.circle
import group_theory.specific_groups.dihedral

/-!
# Isometries of the Complex Plane

The lemma `linear_isometry_complex` states the classification of isometries in the complex plane.
Specifically, isometries with rotations but without translation.
The proof involves:
1. creating a linear isometry `g` with two fixed points, `g(0) = 0`, `g(1) = 1`
2. applying `linear_isometry_complex_aux` to `g`
The proof of `linear_isometry_complex_aux` is separated in the following parts:
1. show that the real parts match up: `linear_isometry.re_apply_eq_re`
2. show that I maps to either I or -I
3. every z is a linear combination of a + b * I

The definition `dihedral_to_complex_hom` provides the canonical homomorphism of the dihedral group
into the linear isometries of ℂ.

## References

* [Isometries of the Complex Plane](http://helmut.knaust.info/mediawiki/images/b/b5/Iso.pdf)
-/
noncomputable theory

open complex dihedral_group

local notation `|` x `|` := complex.abs x
local notation `π` := real.pi

/-- An element of the unit circle defines a `linear_isometry_equiv` from `ℂ` to itself, by
rotation. This is an auxiliary construction; use `rotation`, which has more structure, by
preference. -/
def rotation_aux (a : circle) : ℂ ≃ₗᵢ[ℝ] ℂ :=
{ to_fun := λ z, a * z,
  map_add' := mul_add ↑a,
  map_smul' := λ t z, by { simp only [smul_coe], ring },
  inv_fun := λ z, a⁻¹ * z,
  left_inv := λ z, by { field_simp [nonzero_of_mem_circle], ring },
  right_inv := λ z, by { field_simp [nonzero_of_mem_circle], ring },
  norm_map' := by simp }

/-- An element of the unit circle defines a `linear_isometry_equiv` from `ℂ` to itself, by
rotation. -/
def rotation : circle →* (ℂ ≃ₗᵢ[ℝ] ℂ) :=
{ to_fun := rotation_aux,
  map_one' := by { ext1, simp [rotation_aux] },
  map_mul' := λ a b, by { ext1, simp [rotation_aux] } }

@[simp] lemma rotation_apply (a : circle) (z : ℂ) : rotation a z = a * z := rfl
@[simp] lemma rotation_symm_apply (a : circle) (z : ℂ) : (rotation a).symm z = a⁻¹ * z := rfl

lemma rotation_mul_conj_lie (a : circle): rotation a * conj_lie = conj_lie * (rotation a⁻¹) :=
begin
 ext1 z,
 suffices : (a : ℂ) = conj a⁻¹,
 { simpa using or.inl this },
 rw [←coe_inv_circle, coe_inv_circle_eq_conj, conj_conj],
end

lemma linear_isometry.re_apply_eq_re_of_add_conj_eq (f : ℂ →ₗᵢ[ℝ] ℂ)
  (h₃ : ∀ z, z + conj z = f z + conj (f z)) (z : ℂ) : (f z).re = z.re :=
by simpa [ext_iff, add_re, add_im, conj_re, conj_im, ←two_mul,
         (show (2 : ℝ) ≠ 0, by simp [two_ne_zero'])] using (h₃ z).symm

lemma linear_isometry.im_apply_eq_im_or_neg_of_re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ}
  (h₂ : ∀ z, (f z).re = z.re) (z : ℂ) :
  (f z).im = z.im ∨ (f z).im = -z.im :=
begin
  have h₁ := f.norm_map z,
  simp only [complex.abs, norm_eq_abs] at h₁,
  rwa [real.sqrt_inj (norm_sq_nonneg _) (norm_sq_nonneg _), norm_sq_apply (f z), norm_sq_apply z,
    h₂, add_left_cancel_iff, mul_self_eq_mul_self_iff] at h₁,
end

lemma linear_isometry.im_apply_eq_im {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) :
  z + conj z = f z + conj (f z) :=
begin
  have : ∥f z - 1∥ = ∥z - 1∥ := by rw [← f.norm_map (z - 1), f.map_sub, h],
  apply_fun λ x, x ^ 2 at this,
  simp only [norm_eq_abs, ←norm_sq_eq_abs] at this,
  rw [←of_real_inj, ←mul_conj, ←mul_conj] at this,
  rw [conj.map_sub, conj.map_sub] at this,
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
  have : (f.trans (rotation a).symm) 1 = 1 := by simp,
  refine (linear_isometry_complex_aux this).imp (λ h₁, _) (λ h₂, _),
  { simpa using eq_mul_of_inv_mul_eq h₁ },
  { exact eq_mul_of_inv_mul_eq h₂ }
end

variables {m : ℕ}

/-- The additive homomorphism embedding `zmod m` in the group of real numbers modulo `2 * π`. -/
def zmod_to_angle (hm : m ≠ 0) : zmod m →+ real.angle :=
zmod.lift m ⟨gmultiples_hom real.angle ↑(2 * real.pi /m),
  begin
    suffices : m • (2 * π / ↑m) = 2 * π,
    { simpa using congr_arg (coe : _ → real.angle) this },
    have : (m:ℝ) ≠ 0 := by exact_mod_cast hm,
    field_simp,
    ring
  end⟩

/-- A function mapping `dihedral_group` to linear isometries of ℂ.
Auxiliary construction for `dihedral_to_complex_hom`. -/
def dihedral_to_complex (hm : m ≠ 0) : dihedral_group m → ℂ ≃ₗᵢ[ℝ] ℂ
| (r i) := rotation (angle_to_circle (zmod_to_angle hm i))
| (sr i) := conj_lie * rotation (angle_to_circle (zmod_to_angle hm i))

variables (hm : m ≠ 0)

lemma mul_1 (i j : zmod m) : dihedral_to_complex hm (r i) * dihedral_to_complex hm (r j) =
  dihedral_to_complex hm (r (i + j)) :=
begin
  simp only [dihedral_to_complex],
  rw (zmod_to_angle hm).map_add,
  rw angle_to_circle_add,
  rw rotation.map_mul,
end

lemma mul_2 (i j : zmod m) : dihedral_to_complex hm (r i) * dihedral_to_complex hm (sr j) =
  dihedral_to_complex hm (sr (j - i)) :=
begin
  simp only [dihedral_to_complex],
  rw ← mul_assoc,
  rw rotation_mul_conj_lie,
  rw mul_assoc,
  rw (zmod_to_angle hm).map_sub,
  rw angle_to_circle_sub,
  rw div_eq_mul_inv,
  rw mul_comm,
  rw rotation.map_mul,
end

lemma mul_3 (i j : zmod m) : dihedral_to_complex hm (sr i) * dihedral_to_complex hm (r j) =
  dihedral_to_complex hm (sr (i + j)) :=
begin
  simp only [dihedral_to_complex],
  rw (zmod_to_angle hm).map_add,
  rw angle_to_circle_add,
  rw rotation.map_mul,
  rw mul_assoc,
end

lemma mul_4 (i j : zmod m) : dihedral_to_complex hm (sr i) * dihedral_to_complex hm (sr j) =
  dihedral_to_complex hm (r (j - i)) :=
begin
  simp only [dihedral_to_complex],
  rw ← mul_assoc,
  have : conj_lie * rotation (angle_to_circle ((zmod_to_angle hm) i)) * conj_lie * 
  rotation (angle_to_circle ((zmod_to_angle hm) j)) = conj_lie * 
  (rotation (angle_to_circle ((zmod_to_angle hm) i)) * conj_lie) * 
  rotation (angle_to_circle ((zmod_to_angle hm) j)),
  { simp [mul_assoc], },
  rw this,
  rw rotation_mul_conj_lie,
  rw ← mul_assoc,
  rw mul_assoc,
  rw ← rotation.map_mul,
  have this₁ : ((angle_to_circle ((zmod_to_angle hm) i))⁻¹ * 
  angle_to_circle ((zmod_to_angle hm) j)) = 
  (angle_to_circle ((zmod_to_angle hm) j) / angle_to_circle ((zmod_to_angle hm) i)),
  { rw mul_comm,
    refl, },
  rw this₁,
  rw (zmod_to_angle hm).map_sub,
  rw ← angle_to_circle_sub,
  have this₂ : conj_lie * conj_lie = 1,
  { ext1 z,
    simp[conj_lie], },
  rw this₂,
  rw one_mul,
end

/-- A homomorphism mapping the dihedral group to linear isometries of ℂ. -/
def dihedral_to_complex_hom: dihedral_group m →* (ℂ ≃ₗᵢ[ℝ] ℂ) :=
{ to_fun :=  dihedral_to_complex hm,
  map_one' := begin change dihedral_to_complex hm (r 0) = _, ext1 z, simp [dihedral_to_complex], 
  end,
  map_mul' :=
  begin
    rintros (i | i) (j | j),
    { rw mul_1,
      refl, },
    { rw mul_2,
      refl, },
    { rw mul_3,
      refl, },
    { rw mul_4,
      refl, },
  end }
