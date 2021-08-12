/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/

import linear_algebra.special_linear_group
import analysis.complex.basic
import group_theory.group_action.defs

/-!
# The upper half plane and its automorphisms

This file defines `upper_half_plane` to be the upper half plane in `ℂ`.

We furthermore equip it with the structure of an `SL(2,ℝ)` action by
fractional linear transformations.

We define the notation `ℍ` for the upper half plane available in the locale
`upper_half_plane` so as not to conflict with the quaternions.
-/

noncomputable theory

open matrix matrix.special_linear_group

open_locale classical big_operators matrix_groups

local attribute [instance] fintype.card_fin_even

/-- The upper half plane -/
abbreviation upper_half_plane :=
{point : ℂ // 0 < point.im}

localized "notation `ℍ` := upper_half_plane" in upper_half_plane

namespace upper_half_plane

/-- Imaginary part -/
def im (z : ℍ) := (z : ℂ).im

/-- Real part -/
def re (z : ℍ) := (z : ℂ).re

@[simp] lemma coe_im (z : ℍ) : (z : ℂ).im = z.im := rfl

@[simp] lemma coe_re (z : ℍ) : (z : ℂ).re = z.re := rfl

lemma im_pos (z : ℍ) : 0 < z.im := z.2

lemma im_ne_zero (z : ℍ) : z.im ≠ 0 := z.im_pos.ne'

lemma ne_zero (z : ℍ) : (z : ℂ) ≠ 0 :=
begin
  intros h,
  apply z.im_ne_zero,
  rw [←complex.zero_im, ←h, coe_im]
end

lemma norm_sq_pos (z : ℍ) : 0 < complex.norm_sq (z : ℂ) :=
begin
  rw complex.norm_sq_pos,
  exact z.ne_zero
end

lemma norm_sq_ne_zero (z : ℍ) : complex.norm_sq (z : ℂ) ≠ 0 := ne_of_gt (norm_sq_pos z)

/-- Numerator of the formula for a fractional linear transformation -/
@[simp] def top (g : SL(2, ℝ)) (z : ℍ) : ℂ := (g 0 0) * z + (g 0 1)

/-- Denominator of the formula for a fractional linear transformation -/
@[simp] def bottom (g : SL(2, ℝ)) (z : ℍ) : ℂ := (g 1 0) * z + (g 1 1)

lemma linear_ne_zero (cd : fin 2 → ℝ) (z : ℍ) (hcd : cd ≠ 0) : (cd 0 : ℂ) * z + cd 1 ≠ 0 :=
begin
  intros h,
  apply hcd,
  have : cd 0 = 0,
  { have : ((cd 0 : ℂ)*z+(cd 1)).im = 0 := by simp [h],
    simpa [z.im_ne_zero] using this },
  ext i,
  fin_cases i,
  { exact this,},
  have this1 : ((cd 0 : ℂ)*z+(cd 1)).re = 0 := by simp [h],
  simpa [this] using this1
end

lemma bottom_ne_zero (g : SL(2, ℝ)) (z : ℍ) : bottom g z ≠ 0 :=
linear_ne_zero (g 1) z (g.row_ne_zero 1)

lemma normsq_bottom_pos (g : SL(2, ℝ)) (z : ℍ) : 0 < complex.norm_sq (bottom g z) :=
complex.norm_sq_pos.mpr (bottom_ne_zero g z)

lemma normsq_bottom_ne_zero (g : SL(2, ℝ)) (z : ℍ) : complex.norm_sq (bottom g z) ≠ 0 :=
ne_of_gt (normsq_bottom_pos g z)

/-- Fractional linear transformation -/
def smul_aux' (g : SL(2, ℝ)) (z : ℍ) : ℂ := top g z / bottom g z

lemma im_smul_eq_div_norm_sq' (g : SL(2, ℝ)) (z : ℍ) :
  (smul_aux' g z).im = z.im / (bottom g z).norm_sq :=
begin
  rw [smul_aux', complex.div_im],
  set NsqBot := (bottom g z).norm_sq,
  have : NsqBot ≠ 0 := by simp [complex.norm_sq_pos, bottom_ne_zero g z, NsqBot, -bottom],
  field_simp [smul_aux'],
  convert congr_arg (λ x, x * z.im * NsqBot ^ 2) g.det_coe using 1,
  { rw det_fin_two ↑g,
    ring },
  { ring }
end

/-- Fractional linear transformation -/
def smul_aux (g : SL(2,ℝ)) (z : ℍ) : ℍ :=
⟨ smul_aux' g z,
  begin
    rw im_smul_eq_div_norm_sq',
    exact div_pos z.im_pos (complex.norm_sq_pos.mpr (bottom_ne_zero g z)),
  end ⟩

lemma bot_cocycle (x y : SL(2,ℝ)) (z : ℍ) :
  bottom (x * y) z = bottom x (smul_aux y z) * bottom y z :=
begin
  change _ = (_ * (_ / _) + _) * _,
  field_simp [bottom_ne_zero, -bottom, -top],
  simp [matrix.mul, dot_product, fin.sum_univ_succ],
  ring
end

lemma mul_smul' (x y : SL(2, ℝ)) (z : ℍ) :
  smul_aux (x * y) z = smul_aux x (smul_aux y z) :=
begin
  ext1,
  change _ / _ = (_ * (_ / _) + _)  * _,
  rw bot_cocycle,
  field_simp [bottom_ne_zero, -bottom, -top],
  simp [matrix.mul, dot_product, fin.sum_univ_succ],
  ring
end

/-- The action of `SL(2, ℝ)` on the upper half-plane by fractional linear transformations. -/
instance : mul_action SL(2, ℝ) ℍ :=
{ smul := smul_aux,
  one_smul := λ z, by { ext1, change _ / _ = _, simp },
  mul_smul := mul_smul' }

@[simp] lemma coe_smul (g : SL(2, ℝ)) (z : ℍ) : ↑(g • z) = top g z / bottom g z := rfl
@[simp] lemma re_smul (g : SL(2, ℝ)) (z : ℍ) : (g • z).re = (top g z / bottom g z).re := rfl

lemma im_smul (g : SL(2, ℝ)) (z : ℍ) : (g • z).im = (top g z / bottom g z).im := rfl

lemma im_smul_eq_div_norm_sq (g : SL(2, ℝ)) (z : ℍ) :
  (g • z).im = z.im / (complex.norm_sq (bottom g z)) :=
im_smul_eq_div_norm_sq' g z

@[simp] lemma neg_smul (g : SL(2,ℝ)) (z : ℍ) : -g • z = g • z :=
begin
  ext1,
  change _ / _ = _ / _,
  field_simp [bottom_ne_zero, -bottom, -top],
  simp,
  ring,
end

end upper_half_plane
