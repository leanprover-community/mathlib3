import linear_algebra.special_linear_group
import analysis.complex.basic
import data.matrix.notation
import group_theory.group_action.defs
import data.int.basic
import data.int.parity
import data.nat.gcd
import algebra.ordered_ring
import ring_theory.int.basic
import data.real.sqrt

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

@[simp] lemma expand_sum_01 {R : Type*} [ring R] (f : fin 2 → R ) :
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

@[simp] lemma has_coe_SL_apply (g : SL(2, ℤ)) :
  @coe _ (special_linear_group (fin 2) ℝ) _ g
  = ⟨map (@coe _ (matrix (fin 2) (fin 2) ℤ) _ g) (int.cast_ring_hom ℝ),
    ring_hom.map_det_one (int.cast_ring_hom ℝ) (det_coe_matrix g)⟩ :=
SL_n_insertion_apply (int.cast_ring_hom ℝ) g

instance has_neg_SL {R : Type*} [comm_ring R] : has_neg SL(2, R) :=
⟨λ g, ⟨- g.1, by simpa [det2] using g.2⟩⟩

@[simp] lemma special_linear_group.has_neg_coe_mat {R : Type*} [comm_ring R] (g : SL(2, R)) :
  @coe _ (matrix (fin 2) (fin 2) R) _ (-g) = - (@coe _ (matrix (fin 2) (fin 2) R) _ g) :=
rfl

@[simp]
lemma special_linear_group.has_neg_cast {R : Type*} [comm_ring R] (g : SL(2, ℤ)) :
  @coe _ SL(2, ℝ) _ (-g) = - (@coe _ SL(2, ℝ) _ g) :=
subtype.ext $ (@ring_hom.map_matrix (fin 2) _ _ _ _ _ _ (int.cast_ring_hom ℝ)).map_neg g

@[simp]
lemma bottom_def' {g : SL(2,ℝ)} {z : ℂ} : bottom g z = g.1 1 0 * z + g.1 1 1 := by refl

@[simp]
lemma top_def' {g : SL(2,ℝ)} {z : ℂ} : top g z = g.1 0 0 * z + g.1 0 1 := by refl

-- @[simp]
-- lemma coeff_coe {g : SL(2,ℤ)} {i j : fin 2} : (g : SL(2,ℝ)).val i j = ((g.val i j) : ℝ) := by refl

-- @[simp]
-- lemma coeff_coe' {g : SL(2,ℤ)} {i j : fin 2} : (g : SL(2,ℝ)) i j = ((g i j) : ℝ) := by refl

@[simp]
lemma bottom_def {g : SL(2,ℤ)} {z : ℂ} : bottom g z = g.1 1 0 * z + g.1 1 1 := by simp

@[simp]
lemma top_def {g : SL(2,ℤ)} {z : ℂ} : top g z = g.1 0 0 * z + g.1 0 1 := by simp

lemma div_eq_mul_conj_div_norm_sq {z w : ℂ} : z / w = (z * (w.conj)) / complex.norm_sq w :=
begin
  rw [div_eq_mul_inv, inv_def, div_eq_mul_inv, mul_assoc],
  norm_num,
end

lemma im_smul_SL (g : SL(2, ℝ)) (z : H) :
(g • z).val.im = z.val.im / (complex.norm_sq (g.1 1 0 * z + g.1 1 1)) := im_smul_mat_complex

lemma im_smul_SL' (g : SL(2, ℤ)) (z : H) :
(g • z).val.im = z.val.im / (complex.norm_sq (g.1 1 0 * z + g.1 1 1)) :=
by simpa using im_smul_SL g z

lemma im_smul_SL'' (g : SL(2, ℤ)) (z : H) :
(g • z).val.im = z.val.im / (complex.norm_sq (bottom g z)) :=
im_smul_mat_complex


@[simp]
lemma smul_sound {g : SL(2,ℤ)} {z : H} : ((g:SL(2,ℝ)) • z).1 = smul_aux g z :=
rfl

def T : SL(2,ℤ) := { val := ![![1, 1], ![0, 1]], property := by simp [det2] }

def S : SL(2,ℤ) := { val := ![![0, -1], ![1, 0]], property := by simp [det2] }

example : T⁻¹ * T = 1 := inv_mul_self T

example { R : SL(2,ℤ) } : R * T = 1 → R = T⁻¹ := eq_inv_of_mul_eq_one

example { R : SL(2,ℤ) } : T * R = 1 → T⁻¹ = R := inv_eq_of_mul_eq_one

example { x y : SL(2,ℤ)} (h : x.1 = y.1) : x = y := subtype.eq h

@[simp]
lemma mat_congr_SL { x y : SL(2,ℤ) } : x = y ↔ x.val = y.val := subtype.ext_iff_val

@[simp]
lemma mat_ext_iff  {F : Type*} [comm_ring F] (x y : matrix (fin 2) (fin 2) F) :
  x = y ↔ x 0 0 = y 0 0 ∧ x 0 1 = y 0 1 ∧ x 1 0 = y 1 0 ∧ x 1 1 = y 1 1 :=
begin
  rw ←matrix.ext_iff,
  split,
  {
    intro h,
    rw h,
    tauto },
  {
    rintros ⟨h1, h2, h3, h4⟩ i j,
    fin_cases i; fin_cases j; assumption,
  }
end

@[simp]
lemma mat_one {F : Type*} [comm_ring F] : (![![1,0], ![0,1]] : matrix (fin 2) (fin 2) F)
  = (1 : matrix (fin 2) (fin 2) F) := by {simp}

-- @[simp]
-- lemma mul_congr { x y : SL(2,ℤ)} : x * y = 1 ↔ x.1 * y.1 = 1 := by simp

lemma T_inv : T⁻¹ = { val := ![![1, -1], ![0, 1]], property := by simp [det2] } :=
begin
  suffices : T * { val := ![![1, -1], ![0, 1]], property := by simp [det2] } = 1,
  { exact inv_eq_of_mul_eq_one this},
  simp [T],
end

lemma T_n_def {n : ℤ} :  T^(-n) = (T⁻¹)^n := by {simp [inv_gpow, gpow_neg]}

lemma T_pow_ℕ {n : ℕ} : T^n = { val := ![![1, n], ![0, 1]], property := by simp [det2] } :=
begin
  induction n with n hn,
  simp,
  have : T ^ n.succ = (T^n)* T,
  {
    exact pow_succ' T n,
  },
  rw this,
  rw hn,
  rw T,
  simp,
  ring,
end

lemma T_inv_pow_ℕ {n : ℕ} : (T⁻¹)^n = { val := ![![1, -n], ![0, 1]], property := by simp [det2] } :=
begin
  induction n with n hn,
  simp,
  have : (T⁻¹) ^ n.succ = ((T⁻¹)^n)* (T⁻¹),
  {
    exact pow_succ' (T⁻¹) n,
  },
  rw this,
  rw hn,
  rw T_inv,
  simp,
end

@[simp]
lemma smul_def (g : SL(2,ℤ)) (z : H) : ↑(g • z) = smul_aux g z :=
begin
  refl,
end

lemma smul_neg_SL2 (g : SL(2,ℤ)) (z : H) : -g • z = g • z :=
begin
  rw subtype.ext_iff,
  simp only [smul_def, smul_aux_def, top, bottom],
  rw ← neg_div_neg_eq,
  congr' 1; simp; ring,
end

/-
lemma something (k:ℕ) : T ^ (k:ℤ ) = T ^ k :=
begin
    exact gpow_coe_nat T k,
end
-/

lemma T_pow {n : ℤ} : T^n = { val := ![![1, n], ![0, 1]], property := by simp [det2] } :=
begin
  by_cases n_ge_0 : 0 ≤ n,
  lift n to ℕ with n_ge_0,
  refine T_pow_ℕ,
  exact n_ge_0,
  have : T ^ n = T ^ (- (-n)) := by simp,
  rw this,
  rw T_n_def,
  generalize' hk : -n=k,
  have k_ge_0 : 0 ≤ k,
  {
    rw ← hk,
    linarith,
  },
  have : n = -k,
  {
    rw ← hk,
    ring,
  },
  rw this,
  lift k to ℕ using k_ge_0,
  rw gpow_coe_nat,
  norm_cast,
  rw T_inv_pow_ℕ,
end

lemma T_action {z : H} : (T • z).1 = z + 1 :=
begin
  convert @smul_sound T z,
  simp only [smul_aux_def, top, bottom, T, has_coe_SL_apply, subtype.coe_mk, map_cons],
  simp [special_linear_group.cons_apply_zero, special_linear_group.cons_apply_one],
end


lemma Tn_action {z : H} {n : ℤ} : (T^n • z).1 = z + n :=
begin
  have := @smul_sound (T^n) z,
  convert this,
  rw smul_aux,
  rw T_pow,
  rw top,
  rw bottom,
  simp,
end

lemma S_action (z : H) : (S • z).1 = -z⁻¹ :=
begin
  convert @smul_sound S z,
  simp only [smul_aux_def, top, bottom, S, has_coe_SL_apply, subtype.coe_mk, map_cons],
  simp [special_linear_group.cons_apply_zero, special_linear_group.cons_apply_one],
  ring,
end


def fundamental_domain : set H :=
{ z | 1 ≤ (complex.norm_sq z) ∧ |(complex.re z)| ≤ (1 :ℝ)/ 2 }

notation `𝒟` := fundamental_domain

notation `𝒟°` := interior 𝒟

def fundamental_domain' : set H :=
{ z | 1 < (complex.norm_sq z) ∧ |(complex.re z)| < (1 :ℝ)/ 2 }

notation `𝒟'` := fundamental_domain'

notation `𝒟'c` := closure 𝒟'


lemma whatever : 𝒟'c = 𝒟 :=
begin

  sorry,
end


lemma M_lt_Mp1 : ∀ M,  M < (⌊M⌋ :ℝ ) +1 :=
begin
  intros,
  exact lt_floor_add_one M,
end


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
      have : (c:ℝ ) < (⌊M⌋:ℝ) + 1,
      {
        calc
        (c:ℝ) ≤ M           : h2
        ...   < (⌊M⌋:ℝ) + 1 : M_lt_Mp1 M,
      },

      norm_cast at this,
      exact this,
    },
end

--def coprime_ints := { cd :  ℤ × ℤ //  int.gcd cd.1 cd.2 = 1 }
def coprime_ints := { cd :  ℤ × ℤ //  int.gcd cd.1 cd.2 = 1 }

instance : has_coe coprime_ints (ℤ×ℤ) := ⟨ λ x, x.val⟩

lemma cdxy_bnd (x y M :ℝ ) (c d :ℤ ) (h : ( (c:ℝ) * x + d)^2+(c * y)^2 ≤ M) (hy : 0< y) (hM : 0 ≤ M) :
|(c:ℝ)| ≤   real.sqrt (M / y^2) ∧
|(d:ℝ)| ≤ (real.sqrt M) + real.sqrt (M / y^2) * |x|
:=
begin
  have y_sq_nonneg : 0 ≤ y^2 := pow_two_nonneg y,
  have y_sq_pos : 0 < y^2 := pow_pos hy 2,
  have y_sq_nonz : y^2 ≠ 0 := ne_of_gt y_sq_pos,

  have bnd1 : |↑c| ≤ real.sqrt (M / y ^ 2),
  {
    have : (↑c * y) ^ 2 ≤ M,
    {
      have : 0 ≤  ( (c:ℝ) * x + d)^2,
      {
        exact pow_two_nonneg (↑c * x + ↑d),
      },
      linarith,
    },
    have : (↑c) ^ 2 ≤ M / y^2,
    {
      rw (_ : (↑c * y) ^ 2 = (↑c)^2 * y ^ 2 ) at this,
      rw (_ : M = M / y^2 * y ^ 2 ) at this,
      convert div_le_div_of_le y_sq_nonneg this,
      field_simp [y_sq_nonz],
      field_simp [y_sq_nonz],
      field_simp [y_sq_nonz],
      ring,
    },

    refine real.abs_le_sqrt this,
  },

  split,
  exact bnd1,

  have : ((c:ℝ) * x + d) ^ 2 ≤ M,
  {
    have : 0 ≤ ( (c:ℝ) * y)^2,
    {
      exact pow_two_nonneg _,
    },
    linarith,
  },
  have := real.abs_le_sqrt this,
  rw abs_le at this,
  rw abs_le,
  have bnd2 := abs_le.1 bnd1,
  split,
  {
    calc
    -(real.sqrt M + real.sqrt (M / y ^ 2) * |x|)
    = -real.sqrt M - real.sqrt (M / y ^ 2) * |x| : by ring
    ... ≤ -real.sqrt M - |c| * |x| : _
    ... = -real.sqrt M - |c * x| : _
    ... ≤ -real.sqrt M - c * x : _
    ... ≤  ↑d : _,

    have : 0 ≤ |x| := abs_nonneg x,

    simp [bnd1, this],
    exact mul_mono_nonneg this bnd1,

    simp,

    symmetry,
    refine abs_mul _ _, --- NOT WORKING???

    simp,
    exact le_abs_self (↑c * x),

    linarith,
  },
  calc
  ↑d ≤ real.sqrt M + - c * x : _
  ... ≤ real.sqrt M + | -(c:ℝ ) * x| : _
  ... = real.sqrt M + | ((c:ℝ ) * x)| : _
  ... = real.sqrt M + |c| * |x| : _
  ... ≤ real.sqrt M + real.sqrt (M / y ^ 2) * |x| : _,

  linarith,

  have := le_abs_self (-↑c * x),
  refine add_le_add_left this _,

  simp,

  simp,
  refine abs_mul _ _,

  simp [bnd1],
  have : 0 ≤ |x| := abs_nonneg x,
  exact mul_mono_nonneg this bnd1,
end

/-
-/

lemma cdxy_bnd' (z:H) (M :ℝ ) (c d :ℤ ) (h : norm_sq (c*z + d) ≤ M)
(hM : 0 ≤ M) :
(⌊-real.sqrt (M / z.val.im ^ 2)⌋ ≤ c
∧ c < ⌊real.sqrt (M / z.val.im ^ 2)⌋ + 1)
∧ ⌊-(real.sqrt (M / z.val.im ^ 2) * |z.val.re|) + -real.sqrt M⌋ ≤ d
∧ d < ⌊real.sqrt M + real.sqrt (M / z.val.im ^ 2) * |z.val.re|⌋ + 1
:=
begin
  have : norm_sq (↑c * ↑z + ↑d) = (c*z.val.re + d)^2 + (c*z.val.im)^2,
  {
    rw norm_sq,
    simp,
    ring,
  },
  rw this at h,
  have y_pos : 0<z.val.im := im_pos_of_in_H.mp z.2,
  have bnd1 := cdxy_bnd (z.val.re) (z.val.im) M c d h y_pos hM,
  have bnd11 := bnd1.1,
  have bnd12 := bnd1.2,
  clear bnd1,
  rw abs_le at bnd11,
  rw abs_le at bnd12,
  split,
  split,
  {

    suffices :
    (⌊ - real.sqrt (M / z.val.im ^ 2) ⌋:ℝ )  ≤ (c:ℝ )   ,
    {
      norm_cast at this,
      exact this,
    },

    calc
    (⌊ - real.sqrt (M / z.val.im ^ 2) ⌋:ℝ )  ≤
     - real.sqrt (M / z.val.im ^ 2)  : _
    ... ≤ (c:ℝ ) : _,

    refine floor_le _,

    exact bnd11.1,
  },

  {
    suffices :
    (c:ℝ ) < ⌊real.sqrt (M / z.val.im ^ 2)⌋ + 1,
    {
      norm_cast at this,
      exact this,
    },


    calc
    (c:ℝ ) ≤
    real.sqrt (M / z.val.im ^ 2) : bnd11.2
    ... < ⌊real.sqrt (M / z.val.im ^ 2)⌋ + 1 : _,

    refine lt_floor_add_one _,
  },

  split,

  {
    suffices :
    (⌊-(real.sqrt (M / z.val.im ^ 2) * |z.val.re|) + -real.sqrt M⌋:ℝ ) ≤ d,
    {
      norm_cast at this,
      exact this,
    },
    calc
    (⌊-(real.sqrt (M / z.val.im ^ 2) * |z.val.re|) + -real.sqrt M⌋:ℝ ) ≤
    -(real.sqrt (M / z.val.im ^ 2) * |z.val.re|) + -real.sqrt M : _
    ... ≤ d : _,

    refine floor_le _,

    convert bnd12.1 using 1,
    ring,
  },

  suffices :
  (d:ℝ ) < ⌊real.sqrt M + real.sqrt (M / z.val.im ^ 2) * |z.val.re|⌋ + 1,
  {
    norm_cast at this,
    exact this,
  },
  calc
  (d:ℝ ) ≤ real.sqrt M + real.sqrt (M / z.val.im ^ 2) * |z.val.re| : bnd12.2
  ... < ⌊real.sqrt M + real.sqrt (M / z.val.im ^ 2) * |z.val.re|⌋ + 1 : _,

  refine lt_floor_add_one _,
end

lemma finite_pairs (M : ℝ) (z : H) :
  set.finite {cd : coprime_ints | (((cd : ℤ×ℤ).1 : ℂ) * z + ((cd : ℤ × ℤ ).2 : ℂ)).norm_sq ≤ M} :=
begin
  by_cases M_nonneg : M < 0,
  {
    have : {cd : coprime_ints | (((cd : ℤ×ℤ).1 : ℂ) * z + ((cd : ℤ × ℤ ).2 : ℂ)).norm_sq ≤ M} ⊆ ∅ ,
    {
      intros cd,
      intros h,
      simp at h,
      exfalso,
      have : 0 ≤  (((cd : ℤ×ℤ).1 : ℂ) * z + ((cd : ℤ × ℤ ).2 : ℂ)).norm_sq ,
      {
        refine norm_sq_nonneg _,
      },
      linarith,
    },
    have : {cd : coprime_ints | (((cd : ℤ×ℤ).1 : ℂ) * z + ((cd : ℤ × ℤ ).2 : ℂ)).norm_sq ≤ M} = ∅,
    {
      refine set.eq_empty_of_subset_empty  this,
    },
    rw this,
    simp,
  },
  {
    simp at M_nonneg,
    let s1 := finset.Ico_ℤ (⌊-real.sqrt (M / (z.val.im)^2)⌋) (⌊real.sqrt (M / z.val.im^2)⌋+1),
    let s2 := finset.Ico_ℤ (⌊- ((real.sqrt M) + real.sqrt (M / z.val.im^2) * |z.val.re|)⌋) (⌊(real.sqrt M) + real.sqrt (M / z.val.im^2) * |z.val.re|⌋+1),
    let s : finset (ℤ × ℤ ):= s1.product s2,

    suffices : (coe '' {cd : coprime_ints | (((cd : ℤ×ℤ).1 : ℂ) * z + ((cd : ℤ × ℤ ).2 : ℂ)).norm_sq ≤ M}) ⊆  (s : set (ℤ × ℤ)),
--    suffices : ({cd : coprime_ints | (((cd : ℤ×ℤ).1 : ℂ) * z + ((cd : ℤ × ℤ ).2 : ℂ)).norm_sq ≤ M}) ⊆  (((coe ⁻¹' (s : set (ℤ × ℤ))  : set coprime_ints))),
    {
      have := set.finite.subset s.finite_to_set this,
      refine set.finite_of_finite_image _ this,
      apply set.inj_on_of_injective,
      refine subtype.coe_injective,
    },
    intros x hx,
    simp at hx,
    rcases hx with ⟨ w, ⟨nhw1, nhw2⟩⟩ ,
    rw nhw2 at nhw1,
    simp [s, s1, s2],

    exact cdxy_bnd' z M x.1 x.2 nhw1 M_nonneg,
  },
end

variables {g : SL(2,ℤ)} {z : H}

lemma gcd_eq_one_iff_coprime' (a b : ℤ) : gcd a b = 1 ↔ is_coprime a b :=
begin
  rw [←int.coe_gcd, ←int.coe_nat_one, int.coe_nat_inj', int.gcd_eq_one_iff_coprime],
end

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
  let a := int.gcd_b cd.1 cd.2,
  let b := -int.gcd_a cd.1 cd.2,
  let g := ![![a,b],![cd.1,cd.2]],
  have : 1 = det g,
  {
    rw det2,
    suffices : 1 = a * cd.2 - cd.1 * b ,
    convert this,
    suffices : 1 = a * cd.snd + cd.fst * int.gcd_a cd.fst cd.snd,
    {
      simp [g],
      exact this,
    },

    convert int.gcd_eq_gcd_ab cd.1 cd.2 using 1,
    rw  hhcd,
    simp,
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
  have : int.gcd  (g'.val 1 0) (g'.val 1 1) = 1,
  {
    simp,
    let cc : ℤ  := (g'.val 1 0),
    let dd : ℤ  := (g'.val 1 1),
    have : int.gcd (g'.val 1 0) (g'.val 1 1) = int.gcd cc dd := rfl,

    convert this,
    symmetry,
    convert hhcd,
    sorry,
    simp [cc, g', g],
    simp [dd],
    rw gcd_eq_one_iff_coprime',
    use [(- (g'.val 0 1)) , ((g'.val 0 0))],

    have := g'.2,
    rw det2 at this,
    convert this using 1,
    simp [cc, dd],
    ring,
  },
  convert hcd' ⟨ (g'.val 1 0 , g'.val 1 1) , this ⟩ ,
  {
    rw bottom,
    simp [g],
  },
  rw bottom,
  simp,
end

lemma exists_g_with_max_Im (z : H) :
  ∃ g : SL(2,ℤ), ∀ g' : SL(2,ℤ),  (g' • z).val.im ≤ (g • z).val.im :=
begin
  have := exists_g_with_min_bottom z,
  have im_z_pos : 0 < (z:ℂ ).im := im_pos_of_in_H.mp z.2,
  cases this with gg hg,
  use gg,
  intros g',
  rw im_smul_SL'',
  rw im_smul_SL'',
  have bg_n_pos : (bottom gg z).norm_sq > 0,
  {
    have bg : (bottom gg z) ≠ 0,
    {
      refine bottom_nonzero im_z_pos,
    },
    exact norm_sq_pos.mpr bg,
  },
  have bg'_n_pos : (bottom g' z).norm_sq > 0,
  {
    have bg' : (bottom g' z) ≠ 0,
    {
      refine bottom_nonzero im_z_pos,
    },
    exact norm_sq_pos.mpr bg',
  },
  have hgg' := hg g',
  have : 1/ norm_sq (bottom g' z) ≤ 1/ norm_sq (bottom gg z) ,
  {
    exact (one_div_le_one_div bg'_n_pos bg_n_pos).mpr (hg g'),
  },
  exact (div_le_div_left im_z_pos bg'_n_pos bg_n_pos).mpr (hg g'),
end

def G' : subgroup SL(2,ℤ) := subgroup.closure {S, T}

lemma exists_g_with_max_Im' (z : H) :
  ∃ g : SL(2,ℤ), (g ∈ G') ∧  ∀ g' : SL(2,ℤ), g' ∈ G' → ((g' : SL(2,ℤ)) • z).val.im ≤ ((g : SL(2,ℤ)) • z).val.im :=
begin
  -- Alex, can you do this one as well?
  -- I don't understand; how am I supposed to show g ∈ G' without proving S,T generate SL(2,Z)?...
  sorry
end


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

lemma abs_floor_ineq (a : ℝ) : |a + -⌊a + 2⁻¹⌋| ≤ 2⁻¹ :=
begin
  rw abs_le,
  split,
  {
    calc
    -2⁻¹ = a - (a + 2⁻¹)    : by ring
    ... ≤ a - ↑⌊a + 2⁻¹⌋    : _
    ... = a + -↑⌊a + 2⁻¹⌋  : by ring,

    simp,
    exact floor_le _,
  },

  calc
  a + -↑⌊a + 2⁻¹⌋ = a - ↑⌊a + 2⁻¹⌋ : by ring
  ... ≤ a - a + 2⁻¹ : _
  ... = 2⁻¹ : by ring,

  simp,
  apply le_of_lt,
  suffices : a - 2⁻¹ < ↑⌊a + 2⁻¹⌋,
  {
    linarith,
  },
  have := sub_one_lt_floor (a + 2⁻¹),
  convert this using 1,
  ring,
end

lemma find_appropriate_T (z : H) : ∃ (n : ℤ), | (T^n • z).val.re | ≤ 1/2 :=
begin
  let n := -floor ((z:ℂ ).re+1/2),
  use n,
  rw Tn_action,
  simp,
  apply abs_floor_ineq,
end

lemma im_S_z {z : H} : (S • z).val.im = z.val.im / z.val.norm_sq :=
begin
  rw im_smul_SL'',
  rw bottom,
  simp,
  rw S,
  simp,
end

lemma im_Tn_z {z : H} {n : ℤ} : (T^n • z).val.im = z.val.im :=
begin
  rw im_smul_SL'',
  rw bottom,
  simp,
  rw T_pow,
  simp,
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

/- TODO : prove directly instead of by contradiction
-/
lemma norm_sq_ge_one_of_act_S {z : H} (h : (S • z).val.im ≤ z.val.im) : 1 ≤ norm_sq z.val :=
begin
  by_contradiction hcontra,
  push_neg at hcontra,
  have := im_lt_im_S hcontra,
  linarith,
end

example {a b : ℤ} (ha : 0 ≤ a) (hp : a * b = 1) : a = 1 :=
begin
  exact int.eq_one_of_mul_eq_one_right ha hp,
end

/- By choosing from g or -g, we can impose conditions on the coefficients of g -/
lemma sign_coef { z z' : H } (h : ∃ g : SL(2, ℤ), z' = g • z) :
  ∃ g : SL(2, ℤ), 0 ≤ g.1 1 0 ∧ (g.1 1 0 = 0 → g.1 1 1 = 1 ∧ g.1 0 0 = 1) ∧ z' = g • z :=
begin
  obtain ⟨g, hg⟩ := h,
  by_cases hc : g.val 1 0 = 0,
  {
    have hdet := g.2,
    rw det2 at hdet,
    simp [hc] at hdet,
    by_cases hdsgn : 0 ≤ g.val 1 1,
    {
      use g,
      have hd := int.eq_one_of_mul_eq_one_left hdsgn hdet,
      have ha : g.val 0 0 = 1,
      {
        replace hdet : g.val 0 0 * g.val 1 1 = 1, by tauto,
        simpa [hd] using hdet,
      },
      exact ⟨eq.ge hc, λ _, ⟨hd, ha⟩, hg⟩,
    },
    {
      use -g,
      have hd : (-g).val 1 1 = 1,
      {
        suffices : g.val 1 1 = -1,
        {
          simp [this],
          sorry,
        },
        sorry,
      },
      sorry
    },
  },
  {
    by_cases hcpos : 0 < g.val 1 0,
    {
      use g,
      repeat{split},
      { linarith }, { tauto }, { exact hg }
    },
    {
      use -g,
      repeat {split},
      {
        sorry
      },
      {
        sorry
      },
      {
        sorry
      },
    }
  }
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


lemma is_fundom' {z : H} : ∃ g : SL(2,ℤ), g • z ∈ 𝒟 :=
begin
  obtain ⟨g, hg2⟩ := exists_g_with_max_Im z,
  obtain ⟨n, hn⟩ := find_appropriate_T ((g : SL(2,ℤ)) • z),
  use (T^n * g),
  have hS : S ∈ G' := by {apply subgroup.mem_closure', simp},
  have hT : T ∈ G' := by {apply subgroup.mem_closure', simp},
  have hTn : T^n ∈ G' := by {apply subgroup.gpow_mem G' hT},
--  have hTng : T^n * g ∈ G' := G'.mul_mem hTn hg1,
--  have hSTg : S * T^n * g ∈ G' := G'.mul_mem (G'.mul_mem hS hTn) hg1,
  replace hg2 := hg2 (S * T^n * g), -- hSTg,
  set z' := (T^n * g) • z with z'df,
  have imz' : z'.val.im = ((g : SL(2,ℤ)) • z).val.im,
  { rw [z'df, ← smul_smul, im_Tn_z] },
  rw smul_smul at hn,
  change |z'.val.re| ≤ 1 / 2 at hn,
  suffices : 1 ≤ z'.1.norm_sq,
  -- by exact ⟨hTn,⟨this, hn⟩⟩,
  {
    exact ⟨this, hn⟩,
  },

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

lemma namedIs (c :ℕ ) (h: c≤ 1) :  c=0 ∨ c=1 :=
begin
  cases nat.of_le_succ h,
  {
    left,
    exact le_zero_iff.mp h_1,
  },
  right,
  exact h_1,
end

lemma namedIsZ (c :ℤ  ) (h: c≤ 1) (h2: 0≤ c) :  c=0 ∨ c=1 :=
begin
  --lift n to ℕ using hn
  lift c to ℕ using h2,
  norm_cast,
  refine namedIs _ _ ,
  exact_mod_cast h,
end

-- Describe closure of D as union of boundary segments and interior.
-- Then the lemma goes by cases on where z and z'

lemma fundom_no_repeats' (z z' : H) (h : ∃ g : SL(2,ℤ), z' = g • z) (hz : z ∈ 𝒟') (hz' : z' ∈ 𝒟') :
  (z = z') :=
begin
  sorry,
end

lemma is_fundom'' {z : H} : ∃ g : SL(2,ℤ), ((g • z):ℂ) ∈ (closure fundamental_domain') :=
begin
  sorry,
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

      rw abs_le at hc,
      exact namedIsZ c hc.2 hcpos,
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
