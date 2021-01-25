import linear_algebra.special_linear_group
import data.complex.basic
import analysis.calculus.deriv
import data.matrix.notation
import group_theory.group_action.defs

namespace tactic.interactive
noncomputable theory

meta def show_nonzero := `[
  apply_rules [
    mul_ne_zero,
    sub_ne_zero_of_ne,
    pow_ne_zero,
    ne_of_gt,
    ne_of_lt,
    bottom_nonzero
    ] 10,
  all_goals {try {norm_cast}, try {norm_num}}
]

meta def show_pos := `[
  apply_rules [
    nat.succ_pos,
    mul_pos,
    div_pos,
    inv_pos.mpr,
    pow_pos
    ] 10,
  all_goals {try {norm_cast}, try {norm_num}, try {nlinarith}}
]


meta def clear_denoms := `[
  try {rw div_eq_div_iff},
  try {rw eq_div_iff},
  try {symmetry, rw eq_div_iff},
  try { ring_exp },
  all_goals {show_nonzero}
]

meta def discrete_field := `[
  try {field_simp *},
  try {clear_denoms},
  try {ring_exp},
  try {norm_num},
  try {linarith}
]

end tactic.interactive

noncomputable theory

open matrix
open complex
open matrix.special_linear_group

open_locale classical
open_locale big_operators


def H : set ℂ := { z | 0 < z.im }

local notation `|` x `|` := _root_.abs x

notation `SL(` n `,` R `)`:= special_linear_group (fin n) R

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
  refine or.imp _ _ (em (i.val ≤ 0)),
  all_goals
  { intros hi,
    ext },
  { have : 0 ≤ i.val := zero_le i.val,
    have : i.val = 0 := by linarith,
    exact this },
  { have : i.val < 2 := i.2,
    have : i.val = 1 := by linarith,
    exact this },
end

lemma det2 {F : Type*} [comm_ring F] (g: matrix (fin 2) (fin 2) F) :
g.det = (g 0 0 )*(g 1 1)- (g 1 0 ) * (g  0 1 ) := sorry

lemma im_mat_smul_complex (g : SL(2, ℝ)) (z: ℂ) :
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
  rw det2 g at this,
  ring,
  calc
  -(g 0 1 * z.im * g 1 0) + z.im * g 0 0 * g 1 1
  = ( g 0 0 * g 1 1 - g 1 0  * g 0 1  ) * z.im  : by {ring}
  ... = z.im : by {rw this, simp}
end

lemma isZThenReIm (z:ℂ ) : z=0 → z.im=0:=
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
  have hIm := isZThenReIm ((g.1 1 0) * z + (g.1 1 1)) h,
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
 z.im ≠  0 →  bottom g z ≠  0 :=
begin
  intros h1,
  by_contra,
  simp at h,
  have h2 := czPd_nonZ h,
  exact h1 h2,
end

lemma bottom_nonzero  {g : SL(2, ℝ)} {z : ℂ} (h : z ∈ H) :
  bottom g z ≠  0 := czPd_nonZ_CP (ne_of_gt h)

lemma geNotEge {x : ℝ} : 0 ≤ x → x ≠ 0 → 0 <x :=
begin
  intros h1 h2,
  exact (ne.symm h2).le_iff_lt.mp h1,
end

@[simp] lemma im_pos_of_in_H {z : ℂ} : z ∈ H ↔ 0 < z.im := by refl

@[simp] lemma smul_aux_def {g : SL(2,ℝ)} {z : ℂ} : smul_aux g z = top g z / bottom g z := by refl

lemma GactsHtoH {g : SL(2, ℝ)} {z : ℂ} (h : z ∈ H) :
smul_aux g z ∈ H :=
begin
  simp at h ⊢,
  rw [←smul_aux_def, im_mat_smul_complex],
  by_cases bot_zero : bottom g z = 0,
  { linarith [czPd_nonZ bot_zero] },
  have norm2NonNeg : 0 ≤  norm_sq (bottom g z),
  { apply complex.norm_sq_nonneg },
  have norm2Pos : 0 < norm_sq (bottom g z),
  {
    by_cases norm2Z : norm_sq (bottom g z) =0,
    {
      exfalso,
      rw complex.norm_sq_eq_zero at norm2Z,
      exact bot_zero norm2Z,
    },
    exact (ne.symm norm2Z).le_iff_lt.mp norm2NonNeg,
  },
  exact div_pos h norm2Pos
end

@[simp] lemma sumIs01 (f : fin 2 → ℂ ) :
(∑ (x : fin 2), f x) = f 0 + f 1 :=
begin
--  library_search,
  sorry,
end

lemma bot_cocycle {x y : SL(2,ℝ)} {z : ℂ} (h : z ∈ H) :
  bottom (x * y) z = bottom x (smul_aux y z) * bottom y z :=
begin
  rw smul_aux_def,
  have d1 : bottom y z ≠ 0 := by show_nonzero,
  simp [top, bottom],
  field_simp,
  simp [matrix.mul, dot_product],
  unfold_coes,
  discrete_field,
end

lemma smul_mul {x y : SL(2, ℝ)} { z : ℂ } (h : z ∈ H) :
smul_aux (x * y) z = smul_aux x (smul_aux y z) :=
begin
  rw smul_aux,
  simp,
  rw bot_cocycle,
  have d1 : bottom ( x * y) z ≠ 0, by show_nonzero,
  have d2 : bottom y z ≠ 0, by show_nonzero,
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
    discrete_field,
  },
  rw [top, bottom],
  simp [matrix.mul, dot_product],
  unfold_coes,
  discrete_field,
end


/-- The action of `SL(2, ℝ)` on the upper half-plane by fractional linear transformations. -/
instance SL2R_action : mul_action SL(2, ℝ) H :=
{ smul := λ g, λ z, ⟨smul_aux g z, GactsHtoH z.2⟩,
  one_smul := λ z, by {ext1, unfold_coes, simp [smul_aux, top, bottom, z.2], norm_num},
  mul_smul := λ g1 g2 z, by simpa using smul_mul z.2 }

/-- The action of `SL(2, ℤ)` on the upper half-plane, as a restriction of the `SL(2, ℝ)`-action. -/
instance SL2Z_action : mul_action SL(2, ℤ) H :=
mul_action.comp_hom H (SL_n_insertion (int.cast_ring_hom ℝ))

instance has_coe_SL : has_coe SL(2,ℤ) SL(2,ℝ) := ⟨λ x, SL_n_insertion (int.cast_ring_hom ℝ) x⟩

lemma mat_coe { g : SL(2,ℤ) } : (g : SL(2,ℝ)) =
  { val := ![![g.1 0 0, g.1 0 1], ![g.1 1 0, g.1 1 1]], property :=
  by {simp [det2], norm_cast, simpa [det2] using g.2 }} :=
begin
  ext i j,
  dsimp,
  fin_cases i,
  all_goals {fin_cases j, simp, try{ refl }, try{ simp, refl }},
end

lemma mat_coe' { g : SL(2,ℤ) } : (g : SL(2,ℝ)) =
  { val := ![![g 0 0, g 0 1], ![g 1 0, g 1 1]], property :=
  by {simp [det2], norm_cast, simpa [det2] using g.2 }} :=
begin
  sorry
end

@[simp]
lemma mat_compatibility {g : SL(2,ℤ)} {z : H} : ((g:SL(2,ℝ)) • z).1 = smul_aux g z :=
begin
  simp [mat_coe],
  unfold_coes,
  simp [top, bottom],
  norm_cast,
end

def T : SL(2,ℤ) := { val := ![![1, 1], ![0, 1]], property := by simp [det2] }

def S : SL(2,ℤ) := { val := ![![0, -1], ![1, 0]], property := by simp [det2] }

lemma T_real : (T : SL(2,ℝ)) = { val := ![![(1:ℝ), (1:ℝ)], ![(0:ℝ), (1:ℝ)]],
  property := by simp [det2] } :=
begin
  simp [T, mat_coe],
end

lemma S_real : (S : SL(2,ℝ)) = { val := ![![(0:ℤ), (-1:ℤ)], ![(1:ℤ), (0:ℤ)]],
  property := by simp [det2] } :=
begin
  simp [S, mat_coe],
end

/- lemma mat_real {m : SL(2,ℝ) } : (m : SL(2,ℝ)) = { val := ![![m.1 0 0, m.1 0 1], ![m.1 1 0, m.1 1 1]],
  property := by sorry } :=
begin
  simp [m, mat_coe],
end
 -/

example : T⁻¹ * T = 1 := inv_mul_self T

example { R : SL(2,ℤ) } : R * T = 1 → R = T⁻¹ := eq_inv_of_mul_eq_one

example { R : SL(2,ℤ) } : T * R = 1 → T⁻¹ = R := inv_eq_of_mul_eq_one

lemma mul_congr { x y : SL(2,ℤ)} : x.1 * y.1 = 1 ↔ x * y = 1 :=
begin
  sorry
end

lemma T_inv : T⁻¹ = { val := ![![1, -1], ![0, 1]], property := by simp [det2] } :=
begin
  suffices : T * { val := ![![1, -1], ![0, 1]], property := by simp [det2] } = 1,
  { exact inv_eq_of_mul_eq_one this},
  have hh : matrix.mul T.1  ![![1, -1], ![0, 1]] = ![![1, 0], ![0, 1]], by simp [T],
  simp [T],
  rw ← mul_congr,
  dsimp,
  simp [hh],
  ext,
  fin_cases i,
  all_goals {fin_cases j, try { simp }, tauto },
end

lemma T_n_def {n : ℤ} :  T^(-n) = (T⁻¹)^n:=
begin
  simp [inv_gpow, gpow_neg],
end

lemma T_pow {n : ℤ} : T^n = { val := ![![1, n], ![0, 1]], property := by simp [det2] } :=
begin
  sorry
end

lemma T_action {z : H} : (T • z).1 = z + 1 :=
begin
  change ((T:SL(2,ℝ)) • z).1 = z + 1,
  simp only [mat_compatibility],
  simp [smul_aux_def, T_real, top, bottom],
  discrete_field,
end


lemma Tn_action {z : H} {n : ℤ} : (T^n • z).1 = z + n :=
begin
  sorry
end

lemma S_action (z : H) : (S • z).1 = -z⁻¹ :=
begin
  change ((S:SL(2,ℝ)) • z).1 = -z⁻¹,
  simp only [mat_compatibility],
  simp [smul_aux_def, S_real, top, bottom],
  discrete_field,
end


def fundamental_domain : set H :=
{ z | 1 ≤ (complex.norm_sq z) ∧ (-1:ℝ) / 2 ≤ (complex.re z) ∧ (complex.re z) ≤ (1 :ℝ)/ 2 }

notation `𝒟` := fundamental_domain

notation `𝒟°` := interior 𝒟

lemma finite_integers {M : ℝ} :
  set.finite {c : ℤ | |(c : ℝ)| ≤ M } :=
begin
  sorry
end

lemma finite_pairs {M : ℝ} {z : ℂ} :
  set.finite {cd : ℤ × ℤ | ((cd.1 : ℂ) * z + (cd.2 : ℂ)).abs ≤ M} :=
begin
  sorry
end

variables {g : SL(2,ℤ)} {z : H}

lemma exists_g_with_max_Im (z : H) :
  ∃ g : SL(2,ℤ), ∀ g' : SL(2,ℤ),  (g' • z).val.im ≤ (g • z).val.im :=
begin
  sorry
end

lemma find_appropriate_T {z : H} : ∃ (n : ℤ), | (T^n • z).val.re | ≤ 1/2 :=
begin
  sorry
end


example : linear_ordered_ring ℝ := real.linear_ordered_ring

lemma is_fundom {z : H} : ∃ g : SL(2, ℤ),  (g • z) ∈ 𝒟 :=
begin
  sorry
end


-- define fundamental domain
-- open region, g.z=w -> g=1
-- all z in H, exists g in G such that g.z in closure F

-- define std domain {|z|>1, |z.re| <1/2}

-- proof std domain is a fund dom for G

-- define modular form1

-- define Eisenstein series

-- prove E-sereis are modular

-- E(z,k):= sum _{(c,d)∈ Z^2\ {0,0}} 1/(cz+d)^k

/-
  human:
  d/ dz E(z,k):= sum _{(c,d)∈ Z^2\ {0,0}}  d/ dz 1/(cz+d)^k

  OR

  E(z,k) - E(w,k)
  =
  sum _{(c,d)∈ Z^2\ {0,0}}  ( 1/(cz+d)^k -  1/(cw+d)^k)
=
(z-w)   *
  sum _{(c,d)∈ Z^2\ {0,0}}  ( 1/(cz+d)^k -  1/(cw+d)^k)

-/

/- define Ramanujan delta

-/
