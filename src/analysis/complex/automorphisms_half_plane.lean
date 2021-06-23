import linear_algebra.special_linear_group
import analysis.complex.basic
import group_theory.group_action.defs

noncomputable theory

open matrix
open matrix.special_linear_group

open_locale classical
open_locale big_operators

local attribute [instance] fintype.card_fin_even

class upper_half_plane :=
(point : ℂ)
(im_pos' : 0 < point.im)

localized "notation `ℍ` := upper_half_plane" in upper_half_plane

namespace upper_half_plane

instance : has_coe ℍ ℂ :=
{ coe := λ z, z.point }

instance : topological_space ℍ := uniform_space.to_topological_space.induced (coe : ℍ → ℂ)

def im (z : ℍ) := z.point.im

def re (z : ℍ) := z.point.re

@[simp] lemma coe_point (z : ℍ) : z.point = (z:ℂ) := rfl

@[simp] lemma coe_im (z : ℍ) : (z:ℂ).im = z.im := rfl

@[simp] lemma coe_re (z : ℍ) : (z:ℂ).re = z.re := rfl

@[ext] lemma ext {z w : ℍ} (h : (z:ℂ) = (w:ℂ)) : z = w :=
begin
  tactic.unfreeze_local_instances,
  cases z,
  cases w,
  congr'
end

@[ext] lemma ext_iff (z w : ℍ) : z = w ↔ (z:ℂ)=(w:ℂ) := ⟨λ h, by rw h, ext⟩

lemma im_pos (z : ℍ) : 0 < z.im := z.im_pos'

lemma im_nonzero (z : ℍ) : z.im ≠ 0 := z.im_pos.ne'

lemma nonzero (z : ℍ) : (z:ℂ) ≠ 0 :=
begin
  intros h,
  apply z.im_nonzero,
  simp [← complex.zero_im, ← h],
end

lemma norm_sq_pos (z: ℍ) : 0 < complex.norm_sq (z:ℂ) :=
begin
  rw complex.norm_sq_pos,
  exact nonzero z,
end


end upper_half_plane

local notation `SL(` n `,` R `)`:= special_linear_group (fin n) R

def top (g : SL(2, ℝ)) (z : ℍ) : ℂ := (g 0 0) * z + (g 0 1)

def bottom (g : SL(2, ℝ)) (z : ℍ) : ℂ := (g 1 0) * z + (g 1 1)

-- move this to special linear group file
lemma matrix.special_linear_group.det_ne_zero {n : ℕ} (g : SL(n, ℝ)) :
  det g ≠ 0 :=
by { rw g.det_coe_fun, norm_num }

-- move this to special linear group file
lemma matrix.special_linear_group.row_nonzero {n : ℕ} (g : SL(n, ℝ)) (i : fin n):
  g i ≠ 0 :=
λ h, g.det_ne_zero $ det_eq_zero_of_row_eq_zero i $ by simp [h]

lemma bottom_ne_zero (g : SL(2, ℝ)) (z : ℍ) : bottom g z ≠ 0 :=
begin
  intros h,
  apply g.row_nonzero 1,
  have : g 1 0 = 0,
  { have : (bottom g z).im = 0 := by simp [h],
    simpa [bottom, z.im_nonzero] using this, },
  ext i,
  fin_cases i,
  { exact this,},
  have this1 : (bottom g z).re = 0 := by simp [h],
  simpa [bottom, this] using this1,
end

def smul_aux' (g : SL(2, ℝ)) (z : ℍ) : ℂ := top g z / bottom g z

lemma matrix.special_linear_group.im_smul' (g : SL(2, ℝ)) (z : ℍ) :
  (smul_aux' g z).im = z.im / (bottom g z).norm_sq :=
begin
  rw [smul_aux', complex.div_im],
  set NsqBot := (bottom g z).norm_sq,
  have : NsqBot ≠ 0 := by simp [complex.norm_sq_pos, bottom_ne_zero g z, NsqBot],
  field_simp [smul_aux', bottom, top],
  convert congr_arg (λ x, x*z.im*NsqBot^2) g.det_coe_fun using 1,
  { simp [matrix.det_succ_row_zero, fin.sum_univ_succ],
    ring, },
  { ring, },
end

def smul_aux (g : SL(2,ℝ)) (z : ℍ) : ℍ :=
{ point := smul_aux' g z,
  im_pos' := begin
    rw matrix.special_linear_group.im_smul',
    exact div_pos z.im_pos (complex.norm_sq_pos.mpr (bottom_ne_zero g z)),
  end }

lemma bot_cocycle (x y : SL(2,ℝ)) (z : ℍ) :
  bottom (x * y) z = bottom x (smul_aux y z) * bottom y z :=
begin
  change _ = (_ * (_ / _) + _) * _,
  field_simp [bottom_ne_zero],
  simp [top, bottom, matrix.mul, dot_product, fin.sum_univ_succ],
  ring,
end

lemma mul_smul' (x y : SL(2, ℝ)) (z : ℍ) :
  smul_aux (x * y) z = smul_aux x (smul_aux y z) :=
begin
  ext1,
  change _ / _ = (_ * (_ / _) + _)  * _,
  rw bot_cocycle,
  field_simp [bottom_ne_zero],
  simp [top, bottom, matrix.mul, dot_product, fin.sum_univ_succ],
  ring,
end

/-- The action of `SL(2, ℝ)` on the upper half-plane by fractional linear transformations. -/
instance SL2R_action : mul_action SL(2, ℝ) ℍ :=
{ smul := smul_aux,
  one_smul := λ z, by { ext1, change _ / _ = _, simp [top, bottom] },
  mul_smul := mul_smul' }

lemma matrix.special_linear_group.im_smul (g : SL(2, ℝ)) (z : ℍ) :
  (g • z).im = z.im / (complex.norm_sq (g 1 0 * z + g 1 1)) :=
matrix.special_linear_group.im_smul' g z

lemma smul_neg_SL2 (g : SL(2,ℝ)) (z : ℍ) : -g • z = g • z :=
begin
  ext1,
  change _ / _ = _ / _,
  field_simp [bottom_ne_zero],
  simp [top, bottom],
  ring,
end

@[simp] lemma coe_smul (g : SL(2,ℝ)) (z : ℍ) :
  (↑(g • z) : ℂ) = (g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) :=
rfl
