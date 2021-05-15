import linear_algebra.special_linear_group
import data.complex.basic
import group_theory.group_action.defs

noncomputable theory


open matrix
open matrix.special_linear_group

open_locale classical
open_locale big_operators

class upper_half_plane :=
(point : ℂ)
(im_pos' : 0 < point.im)

local notation `ℍ` := upper_half_plane

namespace upper_half_plane

instance : has_coe ℍ ℂ :=
{ coe := λ z, z.point }

def im (z : ℍ) := z.point.im

def re (z : ℍ) := z.point.re

@[simp] lemma coe_point (z : ℍ) : z.point = (z:ℂ) := rfl

@[simp] lemma coe_im (z : ℍ) : (z:ℂ).im = z.im := rfl

@[simp] lemma coe_re (z : ℍ) : (z:ℂ).re = z.re := rfl

@[ext] lemma ext {z w : ℍ} (h : (z:ℂ)=(w:ℂ)) : z = w :=
begin
  --Heather homework :)

  sorry,
end

@[ext] lemma ext_iff (z w : ℍ) : z = w ↔ (z:ℂ)=(w:ℂ) := ⟨λ h, by rw h, ext⟩

lemma im_pos (z : ℍ) : 0 < z.im := z.im_pos'

lemma im_nonzero (z : ℍ) : z.im ≠ 0 := z.im_pos.ne'

end upper_half_plane

local notation `SL(` n `,` R `)`:= special_linear_group (fin n) R

def top (g : SL(2, ℝ)) (z : ℍ) : ℂ := (g 0 0) * z + (g 0 1)

def bottom (g : SL(2, ℝ)) (z : ℍ) : ℂ := (g 1 0) * z + (g 1 1)


-- move this to special linear group file and do for any row
lemma matrix.special_linear_group.row_nonzero {n:ℕ} (g : SL(n, ℝ)) (i : fin n):
g i ≠ 0 :=
begin
  intros h,
  suffices : 0 = (1 : ℝ),
  { norm_num at this, },
  have this2 : ∀ j, g i j = 0 := by simp [h],
  simpa [det_eq_zero_of_row_eq_zero (i : fin n) this2] using g.det_coe_fun,
end


lemma bottom_nonzero (g : SL(2, ℝ)) (z : ℍ) : bottom g z ≠  0 :=
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

lemma im_smul_mat (g : SL(2, ℝ)) (z : ℍ) :
(smul_aux' g z).im = z.im / (bottom g z).norm_sq :=
begin
  rw [smul_aux', complex.div_im],
  set NsqBot := (bottom g z).norm_sq,
  have : NsqBot ≠ 0 := by simp [complex.norm_sq_pos, bottom_nonzero g z, NsqBot],
  field_simp [smul_aux', bottom, top],
  convert congr_arg (λ x, x*z.im*NsqBot^2) g.det_coe_fun using 1,
  { simp [matrix.det_succ_row_zero, fin.sum_univ_succ],
    ring, },
  { ring, },
end


def smul_aux (g : SL(2,ℝ)) (z : ℍ) : ℍ :=
{ point := smul_aux' g z,
  im_pos' := begin
    rw im_smul_mat,
    exact div_pos z.im_pos (complex.norm_sq_pos.mpr (bottom_nonzero g z)),
  end }

@[simp] lemma smul_aux_def {g : SL(2,ℝ)} {z : ℍ} : (smul_aux g z : ℂ) = top g z / bottom g z := by refl

----- TIDY THIS UP LATER...
/-
lemma isZThenReIm {z : ℂ} : z = 0 → z.im = 0 :=
begin
  rintros rfl,
  exact complex.zero_im,
end



lemma czPd_nonZ {g : SL(2, ℝ)} {z : ℍ} :
bottom g z = 0 → z.im = 0 :=
begin

  intros h,
  rw bottom at h,
  simp at h,
  have hIm :=  h.complex.zero_im,
  simp at hIm,
  cases hIm,
  {
    rw hIm at h,
    simp at h,
    exfalso,
    exact bottomRowNonZ hIm h,
  },
  exact hIm,
end

lemma czPd_nonZ_CP {z : ℂ} {g : SL(2, ℝ)} :
 z.im ≠ 0 → bottom g z ≠  0 :=
begin
  contrapose,
  push_neg,
  exact czPd_nonZ,
end


--@[simp] lemma im_pos_of_in_H {z : ℂ} : z ∈ H ↔ 0 < z.im := by refl


lemma GactsHtoH {g : SL(2, ℝ)} {z : ℍ} :
smul_aux g z ∈ H :=
begin
  simp at h ⊢,
  rw [←smul_aux_def, im_smul_mat_complex],
  exact div_pos h (norm_sq_pos.mpr (bottom_nonzero h)),
end

-/



lemma bot_cocycle (x y : SL(2,ℝ)) (z : ℍ) :
  bottom (x * y) z = bottom x (smul_aux y z) * bottom y z :=
begin
  simp only [smul_aux, smul_aux'],
  set botYZ := bottom y z,
  have d1 : botYZ ≠ 0 := bottom_nonzero _ z,
  simp only [top, bottom],
  rw ← upper_half_plane.coe_point {point := ((y 0 0) * z + (y 0 1)) / botYZ, im_pos' := _},
  field_simp,
  simp [botYZ, bottom, matrix.mul, dot_product, fin.sum_univ_succ],
  ring,
end

lemma smul_mul (x y : SL(2, ℝ)) (z : ℍ) :
smul_aux (x * y) z = smul_aux x (smul_aux y z) :=
begin
  set YZ := smul_aux y z,
  simp only [smul_aux, smul_aux'],
  set botxYZ := bottom x YZ,
  set botxyZ := bottom (x*y) z,
  rw upper_half_plane.ext_iff,
--  rw ← upper_half_plane.coe_point {point := top (x * y) z / botxyZ, im_pos' := _},
  have : (({point := top (x * y) z / botxyZ, im_pos' := _}:ℍ):ℂ) = top (x * y) z / botxyZ := rfl,
  rw this, clear this,
--  rw ← upper_half_plane.coe_point,
  have : (({point := top x YZ / botxYZ, im_pos' := _}:ℍ):ℂ) = top x YZ / botxYZ := rfl,
  rw this, clear this,
  have xYZ_nonzero : botxYZ ≠ 0 := bottom_nonzero _ YZ,
  have xyZ_nonzero : botxyZ ≠ 0 := bottom_nonzero _ z,
  field_simp,
  simp only [botxYZ, bottom, YZ, smul_aux],
  simp only [smul_aux'],
  set botYZ := bottom y z,
--  rw ← upper_half_plane.coe_point,
  have : (({point := top y z / botYZ, im_pos' := _}:ℍ):ℂ) = top y z / botYZ := rfl,
  rw this, clear this,
  simp only [top],

  have : (({point := ((y 0 0) * z + (y 0 1)) / botYZ, im_pos' := _}:ℍ):ℂ)=
    ((y 0 0) * z + (y 0 1)) / botYZ := rfl,
  rw this, clear this,
  have YZ_nonzero : botYZ ≠ 0 := bottom_nonzero _ z,
  field_simp *,
  --field_simp [YZ_nonzero],
  simp only [botYZ, botxyZ, bottom],

  --simp only [matrix.mul, dot_product, fin.sum_univ_succ],
  --simp,
  --simp only [matrix.mul, dot_product, fin.sum_univ_succ],
  --ring,
  --simp,
--  ring_nf,


  have : matrix.mul x y 0 0 = (x 0 0)*(y 0 0)+(x 0 1)*(y 1 0)
    := by simp [matrix.mul, dot_product, fin.sum_univ_succ],
  rw this, clear this,

  have : matrix.mul x y 0 1 = (x 0 0)*(y 0 1)+(x 0 1)*(y 1 1)
    := by simp [matrix.mul, dot_product, fin.sum_univ_succ],
  rw this, clear this,

  --have : ((x*y) : matrix (fin 2) (fin 2) ℝ) = matrix.mul x y := rfl,
  have : ⇑(x * y) = matrix.mul x y := rfl,
  rw this, clear this,


  have : matrix.mul x y 1 1 = (x 1 0)*(y 0 1)+(x 1 1)*(y 1 1)
    := sorry, --by simp [matrix.mul, dot_product, fin.sum_univ_succ],
  rw this, clear this,

  have : matrix.mul x y 1 0 = (x 1 0)*(y 0 0)+(x 1 1)*(y 1 0)
    := sorry, --by simp [matrix.mul, dot_product, fin.sum_univ_succ],
  rw this, clear this,

--  ring,
  sorry,

/-
  simp only [top, botxyZ, botxYZ, bottom, YZ, smul_aux],

  set topYZ := top y z,
  have d1 : botYZ ≠ 0 := bottom_nonzero _ z,

  have d2 : botXYZ ≠ 0 := bottom_nonzero _ z,
  set botXZ := bottom x {point := top y z / botYZ, im_pos' := _},
  have d3 : botXZ ≠ 0 := bottom_nonzero _ _,
  simp only [top],

  rw upper_half_plane.ext_iff,


  have : (({point := top (x * y) z / botXYZ, im_pos' := _}:ℍ ):ℂ) = top (x * y) z / botXYZ := rfl,
  rw this, clear this,
--  rw ← upper_half_plane.coe_point,
  have : (({point := top x {point := top y z / botYZ, im_pos' := _} /
   bottom x {point := top y z / botYZ, im_pos' := _}, im_pos' := _}:ℍ ):ℂ ) =
   top x {point := top y z / botYZ, im_pos' := _} /
   bottom x {point := top y z / botYZ, im_pos' := _} := rfl,
  rw this, clear this,

  simp only [top],


  --Alex homework
  simp,
  rw bot_cocycle,
  have d1 : bottom ( x * y) z ≠ 0 := bottom_nonzero _ z,
  have d2 : bottom y z ≠ 0 := bottom_nonzero h,
  have hyz : top y z / bottom y z ∈ H,
  {
    rw ←smul_aux_def,
    exact GactsHtoH h,
  },
  have d3 : bottom x (top y z / bottom y z) ≠ 0 := bottom_nonzero hyz,
  field_simp [d3],
  suffices : top (x * y) z  = top x (top y z / bottom y z) * bottom y z,
  {
    simp [this],
    ring,
  },
  rw [top, bottom],
  simp [matrix.mul, dot_product, fin.sum_univ_succ],
  field_simp *,
  ring,
  exact h,
  -/
end


@[simp]
lemma bottom_def' {g : SL(2,ℝ)} {z : ℂ} : bottom g z = g.1 1 0 * z + g.1 1 1 := by refl

@[simp]
lemma top_def' {g : SL(2,ℝ)} {z : ℂ} : top g z = g.1 0 0 * z + g.1 0 1 := by refl



/-- The action of `SL(2, ℝ)` on the upper half-plane by fractional linear transformations. -/
instance SL2R_action : mul_action SL(2, ℝ) ℍ :=
{ smul := smul_aux,
  one_smul := λ z, by {ext1, unfold_coes, simp [smul_aux, top, bottom, z.2], norm_num},
  mul_smul := λ g1 g2 z, by simpa using smul_mul z.2 }

lemma im_smul_SL (g : SL(2, ℝ)) (z : H) :
(g • z).val.im = z.val.im / (complex.norm_sq (g.1 1 0 * z + g.1 1 1)) := im_smul_mat_complex

@[simp]
lemma smul_def (g : SL(2,ℝ)) (z : H) : ↑(g • z) = smul_aux g z := rfl

lemma smul_neg_SL2 (g : SL(2,ℝ)) (z : H) : -g • z = g • z :=
begin
  rw subtype.ext_iff,
  simp only [smul_def, smul_aux_def, top, bottom],
  rw ← neg_div_neg_eq,
  congr' 1; simp; ring,
end
