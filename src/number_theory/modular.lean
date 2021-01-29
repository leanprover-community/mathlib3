import linear_algebra.special_linear_group
import data.complex.basic
import analysis.calculus.deriv
import data.matrix.notation
import group_theory.group_action.defs


noncomputable theory

--set_option profiler true

namespace tactic.interactive
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
g.det = g 0 0 * g 1 1 - g 1 0 * g 0 1 :=
begin
calc g.det = ((0 + 1) * (g 0 0 * (g 1 1 * 1))) + ((_ * (g 1 0 * (g 0 1 * 1))) + 0) : refl g.det
  ... = g 0 0 * g 1 1 - g 1 0 * g 0 1 : by {simp, ring}
end

lemma im_smul_mat_complex (g : SL(2, ℝ)) (z: ℂ) :
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
  contrapose,
  push_neg,
  exact czPd_nonZ,
end

lemma bottom_nonzero  {g : SL(2, ℝ)} {z : ℂ} (h : z ∈ H) :
  bottom g z ≠  0 := czPd_nonZ_CP (ne_of_gt h)

lemma geNotEge {x : ℝ} : 0 ≤ x → x ≠ 0 → 0 <x :=
begin
  intros h1 h2,
  exact (ne.symm h2).le_iff_lt.mp h1,
end

@[simp] lemma im_pos_of_in_H {z : ℂ} : z ∈ H ↔ 0 < z.im := by refl

lemma im_pos_of_in_H' {z : H} : 0 < z.val.im :=
begin
  have h : z.val ∈ H := z.2,
  exact im_pos_of_in_H.mp h,
end

@[simp] lemma smul_aux_def {g : SL(2,ℝ)} {z : ℂ} : smul_aux g z = top g z / bottom g z := by refl

lemma GactsHtoH {g : SL(2, ℝ)} {z : ℂ} (h : z ∈ H) :
smul_aux g z ∈ H :=
begin
  simp at h ⊢,
  rw [←smul_aux_def, im_smul_mat_complex],
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

@[simp] lemma expand_sum_01 (f : fin 2 → ℂ ) :
(∑ (x : fin 2), f x) = f 0 + f 1 :=
calc (∑ (x : fin 2), f x) = _ + _ : by {refl}
  ... = f 0 + f 1 : by {simp}

lemma bot_cocycle {x y : SL(2,ℝ)} {z : ℂ} (h : z ∈ H) :
  bottom (x * y) z = bottom x (smul_aux y z) * bottom y z :=
begin
  rw smul_aux_def,
  have d1 : bottom y z ≠ 0 := bottom_nonzero h,
  simp [top, bottom],
  field_simp,
  simp [matrix.mul, dot_product],
  unfold_coes,
  field_simp *,
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
  simp [matrix.mul, dot_product],
  unfold_coes,
  field_simp *,
  ring,
  exact h,
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



lemma bottom_def' {g : SL(2,ℝ)} {z : ℂ} : bottom g z = g.1 1 0 * z + g.1 1 1 := by refl

lemma bottom_def {g : SL(2,ℤ)} {z : ℂ} : bottom g z = g.1 1 0 * z + g.1 1 1 :=
begin
  rw bottom_def',
  sorry
end


lemma im_smul_SL (g : SL(2, ℝ)) (z : H) :
(g • z).val.im = z.val.im / (complex.norm_sq (g.1 1 0 * z + g.1 1 1)) :=
begin
  sorry
end

lemma mat_coe { g : SL(2,ℤ) } : (g : SL(2,ℝ)) =
  { val := ![![g.1 0 0, g.1 0 1], ![g.1 1 0, g.1 1 1]], property :=
  by {simp [det2], norm_cast, simpa [det2] using g.2 }} :=
begin
  ext i j,
  dsimp,
  fin_cases i,
  all_goals {fin_cases j, simp, try{ refl }, try{ simp, refl }},
end

lemma im_smul_SL' (g : SL(2, ℤ)) (z : H) :
(g • z).val.im = z.val.im / (complex.norm_sq (g.1 1 0 * z + g.1 1 1)) :=
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

example : T⁻¹ * T = 1 := inv_mul_self T

example { R : SL(2,ℤ) } : R * T = 1 → R = T⁻¹ := eq_inv_of_mul_eq_one

example { R : SL(2,ℤ) } : T * R = 1 → T⁻¹ = R := inv_eq_of_mul_eq_one

example { x y : SL(2,ℤ)} (h : x.1 = y.1) : x = y := subtype.eq h

@[simp]
lemma mat_congr_SL { x y : SL(2,ℤ) } : x = y ↔ x.val = y.val := subtype.ext_iff_val

@[simp]
lemma mat_congr  {F : Type*} [comm_ring F] (x y : matrix (fin 2) (fin 2) F) :
  x = y ↔ x 0 0 = y 0 0 ∧ x 0 1 = y 0 1 ∧ x 1 0 = y 1 0 ∧ x 1 1 = y 1 1 :=
begin
  split,
  { intro h,
    rw h,
    tauto },
  {
    rintro ⟨h1, h2, h3, h4⟩,
    ext,
    fin_cases i,
    all_goals {fin_cases j},
    all_goals {assumption},
  }
end


@[simp]
lemma mat_one {F : Type*} [comm_ring F] : (![![1,0], ![0,1]] : matrix (fin 2) (fin 2) F)
  = (1 : matrix (fin 2) (fin 2) F) := by {simp}

@[simp]
lemma mul_congr { x y : SL(2,ℤ)} : x * y = 1 ↔ x.1 * y.1 = 1 := by {simp at *, tauto}

lemma T_inv : T⁻¹ = { val := ![![1, -1], ![0, 1]], property := by simp [det2] } :=
begin
  suffices : T * { val := ![![1, -1], ![0, 1]], property := by simp [det2] } = 1,
  { exact inv_eq_of_mul_eq_one this},
  simp [T],
end

lemma T_n_def {n : ℤ} :  T^(-n) = (T⁻¹)^n := by {simp [inv_gpow, gpow_neg]}

lemma T_pow {n : ℤ} : T^n = { val := ![![1, n], ![0, 1]], property := by simp [det2] } :=
begin
  sorry
end

lemma T_action {z : H} : (T • z).1 = z + 1 :=
begin
  change ((T:SL(2,ℝ)) • z).1 = z + 1,
  simp only [mat_compatibility],
  simp [smul_aux_def, T_real, top, bottom],
  field_simp *,
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
  field_simp *,
end


def fundamental_domain : set H :=
{ z | 1 ≤ (complex.norm_sq z) ∧ |(complex.re z)| ≤ (1 :ℝ)/ 2 }

notation `𝒟` := fundamental_domain

notation `𝒟°` := interior 𝒟

lemma finite_integers {M : ℝ} :
  set.finite {c : ℤ | |(c : ℝ)| ≤ M } :=
begin
    let s:= finset.Ico_ℤ (⌊-M⌋) (⌊M⌋+1),
    suffices : {c : ℤ | |↑c| ≤ M} ⊆  s,
    {
      refine set.finite.subset s.finite_to_set this,
    },
    intros c,
    simp [s],
    intros h,
    rw abs_le at h,
    have h1 := h.1,
    have h2 := h.2,
    split,
    {
      have : (⌊-M⌋ :ℝ ) ≤ -M :=  floor_le (-M),
      have := le_trans this h1,
      exact_mod_cast this,
    },
    {
      --- AK homework
      sorry,
    },
end

def coprime_ints := { cd :  ℤ × ℤ //  euclidean_domain.gcd cd.1 cd.2 = 1 }

instance : has_coe coprime_ints (ℤ×ℤ) := ⟨ λ x, x.val⟩

lemma finite_pairs (M : ℝ) (z : ℂ) :
  set.finite {cd : coprime_ints | (((cd : ℤ×ℤ).1 : ℂ) * z + ((cd : ℤ × ℤ ).2 : ℂ)).norm_sq ≤ M} :=
begin
    -- AK homework!!!
  -- prove that |cz+d| < max |c|,|d| * (|z|+1), so
  -- max |c|,|d| < M / |z|+1
  -- contained in a finite set -> finite...???
  -- set.finite.subset


  sorry
end

variables {g : SL(2,ℤ)} {z : H}

lemma exists_g_with_min_bottom (z : H) :
  ∃ g : SL(2,ℤ), ∀ g' : SL(2,ℤ), (bottom g z).norm_sq ≤ (bottom g' z).norm_sq  :=
begin
  let f : coprime_ints → ℝ := λ cd,  (((cd : ℤ×ℤ).1:ℂ) * z + (cd : ℤ×ℤ).2).norm_sq,
  let s : finset coprime_ints := set.finite.to_finset (finite_pairs (1) z),
  have in_s_then_ge_1 : ∀ x, x ∈ s ↔ f x ≤ 1 := by simp [s],
  have : s.nonempty,
  {
    use (0,1),
    simp,
    simp,
  },
  obtain ⟨⟨ cd, hhcd⟩ , cdInS, hcd⟩ := finset.exists_min_image s f this,
  let a := euclidean_domain.gcd_b cd.1 cd.2,
  let b := -euclidean_domain.gcd_a cd.1 cd.2,
  let g := ![![a,b],![cd.1,cd.2]],
  have : 1 = det g,
  {
    rw det2,
    suffices : 1 = a * cd.2 - cd.1 * b ,
    convert this,
    simp [g],
    rw ←  hhcd,
    convert euclidean_domain.gcd_eq_gcd_ab cd.1 cd.2 using 1,
    ring,
  },
  use ⟨ g, this.symm⟩ ,
  intros,
  have hcd' : ∀ (x' : coprime_ints), f ⟨cd,hhcd⟩ ≤ f x',
  {
    intros ,
    by_cases hx' : x' ∈ s,
    {
      exact hcd x' hx',
    },
    {
      rw in_s_then_ge_1  at hx',
      rw in_s_then_ge_1  at cdInS,
      linarith,
    },
  },
  have : euclidean_domain.gcd  (g'.val 1 0) (g'.val 1 1) = 1,
  {
    --- Zulip homework??? :)
    sorry,
  },
  convert hcd' ⟨ (g'.val 1 0 , g'.val 1 1) , this ⟩ ,
  {
    rw bottom,
    simp [g],
    --refl,
    --- Heather homework
    sorry,
  },
  rw bottom,
  simp,
  --norm_cast,
    --- Heather homework
  sorry,
end

lemma exists_g_with_max_Im (z : H) :
  ∃ g : SL(2,ℤ), ∀ g' : SL(2,ℤ),  (g' • z).val.im ≤ (g • z).val.im :=
begin
  -- Alex homework
  sorry,
end

def G' : subgroup SL(2,ℤ) := subgroup.closure {S, T}

example : T ∈ (subgroup.closure ({S, T} : set SL(2,ℤ))) :=
begin
  apply subgroup.mem_closure',
  simp only [set.mem_insert_iff, true_or, set.mem_singleton, or_true, eq_self_iff_true],
end

example {G' : subgroup SL(2,ℤ)} {x y : SL(2,ℤ)} (hx : x ∈ G') (hy : y ∈ G') : x * y ∈ G' :=
begin
  exact subgroup.mul_mem G' hx hy,
end

example {n : ℤ} {g : SL(2,ℤ)} (hg : g ∈ G') : S * T^n * g ∈ G' :=
begin
  have hS : S ∈ G' :=
    by {apply subgroup.mem_closure', simp},
  have hT : T ∈ G' :=
    by {apply subgroup.mem_closure', simp},
  have hTn : T^n ∈ G' :=
    by {apply subgroup.gpow_mem G' hT},
  apply subgroup.mul_mem G',
  { apply subgroup.mul_mem G' hS hTn },
  exact hg,
end

example {g : SL(2,ℤ)} {z z' : H} : g • z = z' ↔ z = g⁻¹ • z' :=
begin
  exact eq_inv_smul_iff.symm,
end

lemma exists_g_with_max_Im' (z : H) :
  ∃ g : SL(2,ℤ), (g ∈ G') ∧  ∀ g' : SL(2,ℤ), g' ∈ G' → ((g' : SL(2,ℤ)) • z).val.im ≤ ((g : SL(2,ℤ)) • z).val.im :=
begin
  sorry
end

lemma find_appropriate_T (z : H) : ∃ (n : ℤ), | (T^n • z).val.re | ≤ 1/2 :=
begin
  sorry
end

lemma im_S_z {z : H} : (S • z).val.im = z.val.im / z.val.norm_sq :=
begin
  sorry
end

lemma im_Tn_z {z : H} {n : ℤ} : (T^n • z).val.im = z.val.im :=
begin
  sorry
end

lemma im_lt_im_S {z : H} (h: norm_sq z.val < 1) : z.val.im < (S • z).val.im :=
begin
  rw im_S_z,
  have imz : 0 < z.val.im := im_pos_of_in_H',
  have hnz : 0 < norm_sq z.val,
  {
    rw norm_sq_pos,
    intro h,
    rw h at imz,
    rw zero_im at imz,
    linarith,
  },
  set N := norm_sq z.val with hN,
  set zim := z.val.im with hzim,
  have : zim * N < zim, by nlinarith,
  exact (lt_div_iff hnz).mpr this,
end

/- TODO : prove directly instead of by contraadiction
-/
lemma norm_sq_ge_one_of_act_S {z : H} (h : (S • z).val.im ≤ z.val.im) : 1 ≤ norm_sq z.val :=
begin
  by_contradiction hcontra,
  push_neg at hcontra,
  have := im_lt_im_S hcontra,
  linarith,
end

/- By choosing from g or -g, we can impose conditions on the coefficients of g -/
lemma sign_coef { z z' : H } (h : ∃ g : SL(2, ℤ), z' = g • z) :
  ∃ g : SL(2, ℤ), 0 ≤ g.1 1 0 ∧ (g.1 1 0 = 0 → g.1 1 1 = 1 ∧ g.1 0 0 = 1) ∧ z' = g • z :=
begin
  sorry
end

lemma is_fundom {z : H} : ∃ g : SL(2,ℤ), g ∈ G' ∧ g • z ∈ 𝒟 :=
begin
  obtain ⟨g, hg1, hg2⟩ := exists_g_with_max_Im' z,
  obtain ⟨n, hn⟩ := find_appropriate_T ((g : SL(2,ℤ)) • z),
  use (T^n * g),
  have hS : S ∈ G' := by {apply subgroup.mem_closure', simp},
  have hT : T ∈ G' := by {apply subgroup.mem_closure', simp},
  have hTn : T^n ∈ G' := by {apply subgroup.gpow_mem G' hT},
  have hTng : T^n * g ∈ G' := G'.mul_mem hTn hg1,
  have hSTg : S * T^n * g ∈ G' := G'.mul_mem (G'.mul_mem hS hTn) hg1,
  replace hg2 := hg2 (S * T^n * g) hSTg,
  set z' := (T^n * g) • z with z'df,
  have imz' : z'.val.im = ((g : SL(2,ℤ)) • z).val.im,
  { rw [z'df, ← smul_smul, im_Tn_z] },
  rw smul_smul at hn,
  change |z'.val.re| ≤ 1 / 2 at hn,
  suffices : 1 ≤ z'.1.norm_sq, by exact ⟨hTng,⟨this, hn⟩⟩,
  set w := (S * T^n * g) • z with hw,
  apply norm_sq_ge_one_of_act_S,
  replace hw : w = S•z',
  {rw [hw, z'df, smul_smul, mul_assoc]},
  rw [imz', ← hw],
  exact hg2,
end

@[simp]
lemma fundom_aux_1 {z : H} (hz : z ∈ 𝒟) (h' : T • z ∈ 𝒟) : z.val.re = -1/2 := sorry

@[simp]
lemma fundom_aux_2 {z : H} (hz : z ∈ 𝒟) (h' : T⁻¹ • z ∈ 𝒟) : z.val.re = 1/2 := sorry

@[simp]
lemma fundom_aux_3 {z : H} (hz : z ∈ 𝒟) (h' : S • z ∈ 𝒟) : z.val.abs = 1 := sorry

/- Why is this not doable by linarith directly? -/
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a ≤ a / b) : b ≤ 1 :=
begin
  suffices: a * b ≤ a, nlinarith,
  rw le_div_iff hb at h,
  exact h,
end

lemma fundom_no_repeats (z z' : H) (h : ∃ g : SL(2,ℤ), z' = g • z) (hz : z ∈ 𝒟) (hz' : z' ∈ 𝒟) :
  (z = z') ∨
  (z.val.re = -1/2 ∧ z' = T • z) ∨
  (z'.val.re = -1/2 ∧ z = T • z') ∨
  (z.val.abs = 1 ∧ z'.val.abs = 1 ∧ z' = S • z ∧ z = S • z') :=
begin
  wlog hwlog : z.val.im ≤ z'.val.im,
  {
    by_cases hne : z = z', tauto,
    right,
    replace h := sign_coef h,
    obtain ⟨g, hcpos, hac, hg⟩ := h,
    set a := g.1 0 0,
    set b := g.1 0 1,
    set c := g.1 1 0 with ←cdf,
    set d := g.1 1 1 with ←ddf,
    have hcd : complex.norm_sq (c * z + d) ≤ 1,
    {
      have himzpos : 0 < z.val.im := im_pos_of_in_H',
      have hnz : 0 < complex.norm_sq (c * z + d),
      {
        rw norm_sq_pos,
        intro hcontra,
        rw [← cdf, ← ddf, ← bottom_def] at hcontra,
        exact czPd_nonZ_CP (ne.symm (ne_of_lt himzpos)) hcontra,
      },
      suffices: z.val.im * complex.norm_sq (c * z + d) ≤ z.val.im, nlinarith,
      rw [hg, im_smul_SL',cdf,ddf, le_div_iff hnz] at hwlog,
      exact hwlog,
    },
    have hc : _root_.abs c ≤ 1,
    {
      sorry
    },
    replace hc : c = 0 ∨ c = 1,
    {
      sorry
    },
    rcases hc with  hc | hc ,
    { -- case c = 0
      have ha : a = 1 := (hac hc).2,
      have hd : d = 1 := (hac hc).1,
      have hgT : g = T^b,
      {
        rw T_pow,
        apply subtype.eq,
        simp,
        tauto,
      },
      have hb : _root_.abs c ≤ 1,
      {
        sorry
      },
      replace hb : b = -1 ∨ b = 0 ∨ b = 1,
      {
        sorry
      },
      rcases hb with hb | hb | hb,
      all_goals {rw hb at hgT, rw hgT at hg, clear hb, clear hgT, simp at hg},
      {
        right, left,
        rw ←inv_smul_eq_iff at hg,
        rw ←hg at hz,
        rw fundom_aux_1 hz' hz,
        tauto,
      },
      { tauto },
      {
        left,
        rw hg at hz',
        rw fundom_aux_1 hz hz',
        tauto,
      }
    },
    { -- case c = 1
      sorry
    }
  },
  obtain ⟨g, hg⟩ := h,
  have hh : ∃ g : SL(2,ℤ), z = g • z' := ⟨g⁻¹, by {simp [eq_inv_smul_iff, hg]}⟩,
  specialize this hh hz' hz,
  tauto,
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
