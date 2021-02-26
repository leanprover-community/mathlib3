import linear_algebra.special_linear_group
import data.complex.basic
import group_theory.group_action.defs

noncomputable theory


open matrix
open complex
open matrix.special_linear_group

open_locale classical
open_locale big_operators

def H : set ℂ := { z | 0 < z.im }

local notation `SL(` n `,` R `)`:= special_linear_group (fin n) R

def top : --SL2R --
SL(2, ℝ)  → ℂ → ℂ :=
λ g, λ z, (g.1 0 0) * z + (g.1 0 1)

def bottom : --SL2R --
SL(2, ℝ)
 → ℂ → ℂ :=
λ g, λ z, (g.1 1 0) * z + (g.1 1 1)

def smul_aux : --SL2R --
SL(2, ℝ) → ℂ → ℂ :=
λ g, λ z, (top g z) / (bottom g z)

lemma split_fin2 (i : fin 2) : i = 0 ∨ i = 1 :=
begin
  fin_cases i; tauto,
end


lemma det2 {F : Type*} [comm_ring F] {g: matrix (fin 2) (fin 2) F} :
g.det = g 0 0 * g 1 1 - g 1 0 * g 0 1 :=
begin
calc g.det = ((0 + 1) * (g 0 0 * (g 1 1 * 1))) + ((_ * (g 1 0 * (g 0 1 * 1))) + 0) : refl g.det
  ... = g 0 0 * g 1 1 - g 1 0 * g 0 1 : by {simp, ring}
end

lemma im_smul_mat_complex {g : SL(2, ℝ)} {z: ℂ} :
(smul_aux g z).im = z.im / (complex.norm_sq (bottom g z)) :=
begin
  by_cases bot_zero : bottom g z = 0,
  {
    rw smul_aux,
    simp,
    simp [bot_zero],
  },
  have : complex.norm_sq (bottom g z) ≠ 0,
  { refine ne.symm (ne_of_lt _),
    simp [norm_sq_pos, bot_zero] },
  field_simp,
  have eq1 : (smul_aux g z).im * norm_sq (bottom g z) = ((smul_aux g z) * norm_sq (bottom g z)).im,
    by simp,
  rw [eq1, ← mul_conj (bottom g z), smul_aux],
  simp only [mul_neg_eq_neg_mul_symm,  sub_neg_eq_add],
  ring,
  field_simp [top, bottom],
  ring,
  have := matrix.special_linear_group.det_coe_matrix g,
  rw det2 at this,
  ring,
  convert congr_arg (λ t, t * z.im) this using 1; ring,
end

lemma isZThenReIm {z : ℂ} : z = 0 → z.im = 0 :=
begin
  intros h,
  rw h,
  exact complex.zero_im,
end

lemma bottomRowNonZ {g : SL(2, ℝ)} :
g.val 1 0 = 0 → g.val 1 1 = 0 → false :=
begin
  intros h1 h2,
  have detIs := g.2,
  rw det2 at detIs,
  rw [h1, h2] at detIs,
  simp at detIs,
  exact detIs,
end

lemma czPd_nonZ {z : ℂ} {g : SL(2, ℝ)} :
bottom g z = 0 → z.im = 0 :=
begin
  intros h,
  rw bottom at h,
  simp at h,
  have hIm := isZThenReIm h,
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

lemma bottom_nonzero {g : SL(2, ℝ)} {z : ℂ} (h : z ∈ H) :
  bottom g z ≠  0 := czPd_nonZ_CP (ne_of_gt h)

@[simp] lemma im_pos_of_in_H {z : ℂ} : z ∈ H ↔ 0 < z.im := by refl

lemma im_pos_of_in_H' {z : H} : 0 < z.val.im := im_pos_of_in_H.mp z.2

@[simp] lemma smul_aux_def {g : SL(2,ℝ)} {z : ℂ} : smul_aux g z = top g z / bottom g z := by refl

lemma GactsHtoH {g : SL(2, ℝ)} {z : ℂ} (h : z ∈ H) :
smul_aux g z ∈ H :=
begin
  simp at h ⊢,
  rw [←smul_aux_def, im_smul_mat_complex],
  exact div_pos h (norm_sq_pos.mpr (bottom_nonzero h)),
end

lemma bot_cocycle {x y : SL(2,ℝ)} {z : ℂ} (h : z ∈ H) :
  bottom (x * y) z = bottom x (smul_aux y z) * bottom y z :=
begin
  rw smul_aux_def,
  have d1 : bottom y z ≠ 0 := bottom_nonzero h,
  simp [top, bottom],
  field_simp,
  simp [matrix.mul, dot_product, fin.sum_univ_succ],
  ring,
end

lemma smul_mul {x y : SL(2, ℝ)} { z : ℂ } (h : z ∈ H) :
smul_aux (x * y) z = smul_aux x (smul_aux y z) :=
begin
  rw smul_aux,
  simp,
  rw bot_cocycle,
  have d1 : bottom ( x * y) z ≠ 0 := bottom_nonzero h,
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
end


@[simp]
lemma bottom_def' {g : SL(2,ℝ)} {z : ℂ} : bottom g z = g.1 1 0 * z + g.1 1 1 := by refl

@[simp]
lemma top_def' {g : SL(2,ℝ)} {z : ℂ} : top g z = g.1 0 0 * z + g.1 0 1 := by refl



/-- The action of `SL(2, ℝ)` on the upper half-plane by fractional linear transformations. -/
instance SL2R_action : mul_action SL(2, ℝ) H :=
{ smul := λ g, λ z, ⟨smul_aux g z, GactsHtoH z.2⟩,
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
