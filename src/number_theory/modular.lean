import linear_algebra.special_linear_group
import data.complex.basic
import group_theory.group_action.defs

namespace tactic.interactive

meta def show_nonzero := `[
  apply_rules [
    mul_ne_zero,
    sub_ne_zero_of_ne,
    pow_ne_zero,
    ne_of_gt,
    ne_of_lt,
    bottomNonZ
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
  try {ext},
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


def H : set ℂ := {z | 0< z.im}

--def SL2R := SL(2, ℝ)

notation `SL(` n `,` R `)`:= special_linear_group (fin n) R

def top : --SL2R --
SL(2, ℝ)  → ℂ → ℂ :=
λ g, λ z,
(
  ((g : matrix (fin 2) (fin 2) ℝ) 0 0 ) * z + ((g : matrix (fin 2) (fin 2) ℝ) 0 1 )
)

def bottom : --SL2R --
SL(2, ℝ)
 → ℂ → ℂ :=
λ g, λ z,
(
  ((g : matrix (fin 2) (fin 2) ℝ) 1 0 ) * z + ((g : matrix (fin 2) (fin 2) ℝ) 1 1 )
)
--λ g, λ z, ((special_linear_group.coe_matrix g) 0 0 )

def smul_aux : --SL2R --
SL(2, ℝ) → ℂ → ℂ :=
λ g, λ z,
(top g z)/(bottom g z)

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


lemma ImOfGaction (g : SL(2, ℝ)) (z: ℂ) :
(smul_aux g z).im = z.im / (complex.norm_sq (bottom g z)) :=
begin
  by_cases bot_zero : bottom g z = 0,
  {
    rw smul_aux,
    simp [bot_zero],
  },

  have : complex.norm_sq (bottom g z) ≠ 0,
  { refine ne.symm (ne_of_lt _),
    simp [norm_sq_pos, bot_zero] },

  field_simp,

  rw (_ : (smul_aux g z).im * norm_sq (bottom g z) = ((smul_aux g z) * norm_sq (bottom g z)).im),

  rw ← mul_conj (bottom g z),
  rw smul_aux,
  simp only [mul_neg_eq_neg_mul_symm,  sub_neg_eq_add],
  ring,
  field_simp [top, bottom],
  ring,
  have := matrix.special_linear_group.det_coe_matrix g,
  rw det2 g at this,
  ring,

  calc
  -(g 0 1 * z.im * g 1 0) + z.im * g 0 0 * g 1 1
  = ( g 0 0 * g 1 1 - g 1 0  * g 0 1  ) * z.im  : _
  ... = z.im : _,

  ring,
  rw this,
  simp,

  simp,
  --rw (_ : (⇑g 1 0 * z.re + ⇑g 1 1) * (⇑g 0 0 * z.im) - ⇑g 1 0 * z.im * (⇑g 0 0 * z.re + ⇑g 0 1)
  --= )
--  simp only [conj_im, mul_neg_eq_neg_mul_symm, conj_re, mul_im, mul_re, sub_neg_eq_add],

--  have : (complex.abs (bottom g z))^2  = (complex.abs (bottom g z))^2

end

lemma isZThenReIm (z:ℂ ) : z=0 → z.im=0:=
begin
  intros h,
  rw h,
  exact complex.zero_im,
end

lemma bottomRowNonZ (g : SL(2, ℝ)) :
g.val 1 0 = 0 → g.val 1 1 = 0 → false :=
begin
  intros h1 h2,
  have detIs := g.2,
  rw det2 at detIs,
  rw [h1, h2] at detIs,
  simp at detIs,
  exact detIs,
end


lemma czPd_nonZ (z:ℂ ) (g : SL(2, ℝ)) :
bottom g z = 0 → z.im = 0 :=
begin
  intros h,
  rw bottom at h,
  simp at h,
  have hIm := isZThenReIm ((g 1 0) * z + (g 1 1)) h,
  simp at hIm,
  cases hIm,
  {
    rw hIm at h,
    simp at h,
    exfalso,
    exact bottomRowNonZ g hIm h,
  },
  exact hIm,
end

lemma czPd_nonZ_CP (z:ℂ ) (g : SL(2, ℝ)) :
 z.im ≠  0 →  bottom g z ≠  0 :=
begin
  intros h1,
  by_contra,
  simp at h,
  have h2 := czPd_nonZ _ _ h,
  exact h1 h2,
end

lemma bottomNonZ  (g : SL(2, ℝ)) {z:ℂ} (h : z ∈ H) :
  bottom g z ≠  0 :=
begin
  have : z.im ≠ 0,
  {
    rw H at h,
    simp at h,
    linarith,
  },
  exact czPd_nonZ_CP z g this,
end

lemma im_nonZ_then_nonZ (z : ℂ) : z.im ≠ 0 → z≠ 0
:=
begin
  intros h,
  refine norm_sq_pos.mp _,
  rw norm_sq,
  simp,
  have zRePos : 0 ≤ z.re * z.re,
  {
    exact mul_self_nonneg z.re,
  },
  have zImPos : 0 < z.im * z.im,
  {
    exact mul_self_pos h,
  },
  linarith,
end

lemma geNotEge (x :ℝ ) : 0≤ x → x≠ 0 → 0 <x :=
begin
  intros h1 h2,
  exact (ne.symm h2).le_iff_lt.mp h1,
end

lemma GactsHtoH (g : SL(2, ℝ)) {z : ℂ} (hz : z ∈ H):
smul_aux g z ∈ H :=
begin
  rw H,
  simp,
  rw ImOfGaction,
  have imZpos : 0 < z.im,
  {
    refine hz,
  },

  by_cases bot_zero : bottom g z = 0,
  {
    have zImZero : z.im=0,
    {
      exact czPd_nonZ _ _ bot_zero,
    },
    exfalso,
    linarith,
  },
  have norm2Pos : 0 < norm_sq (bottom g z),
  {
    have norm2NonNeg : 0 ≤  norm_sq (bottom g z),
    {
      refine complex.norm_sq_nonneg _,
    },
    by_cases norm2Z : norm_sq (bottom g z) =0,
    {
      exfalso,
      rw complex.norm_sq_eq_zero at norm2Z,
      exact bot_zero norm2Z,
    },
    exact (ne.symm norm2Z).le_iff_lt.mp norm2NonNeg,
  },
  exact div_pos imZpos norm2Pos
end

--lemma OneActsHtoH  (z: ℂ) : smul_aux 1 z = z :=  by {rw [smul_aux, top, bottom], simp}

lemma sumIs01 (f : fin 2 → ℂ ) :
(∑ (x : fin 2), f x) = f 0 + f 1 :=
begin
--  library_search,
  sorry,
end

lemma GactGpactH (x y : SL(2, ℝ)) {z: ℂ} (hz : z ∈ H ) :
smul_aux (x * y) z = smul_aux x (smul_aux y z) :=
begin
  have bot1NonZ : bottom (x * y) z ≠ 0,
  {
    show_nonzero,
    --refine bottomNonZ _ _,
    --exact hz,
  },
  have bot2NonZ : bottom y z ≠ 0,
  {
    show_nonzero,
    --refine bottomNonZ _ _,
    --exact hz,
  },
  have bot_x_prime_NonZ : bottom x (top y z / bottom y z) ≠ 0,
  {

    sorry
  },
  rw smul_aux,
  simp,
  field_simp,
/-
  rw (_ : top (x * y) z
  =  bottom (x * y) z  * top x (top y z / bottom y z) / bottom x (top y z / bottom y z)),

  ring,
-/
  set B := bottom y z,
  --set T := top y z,
  rw top,
  rw bottom,
  simp,
  rw matrix.mul,
  simp,
  repeat {rw dot_product},
  simp,
  repeat {rw sumIs01},
  field_simp,
  left,
  dsimp [B],
  rw bottom,
  norm_num,
  ring,
end

instance : mul_action (SL(2, ℝ)) H :=
{ smul := λ g, λ z, ⟨smul_aux g z, GactsHtoH g z.property ⟩ ,
  one_smul := λ z, by {apply subtype.ext, simp [smul_aux, top, bottom]},
  mul_smul := λ g1 g2 z, by simpa using GactGpactH g1 g2 z.property }

def fundamental_domain : set ℂ :=
{ z | 1 ≤ (complex.norm_sq z) ∧ (-1:ℝ) / 2 ≤ (complex.re z) ∧ (complex.re z) ≤ (1 :ℝ)/ 2 }

notation `𝒟` := fundamental_domain

notation `𝒟°` := interior 𝒟

def T : SL(2,ℤ) := { val :=  λ i j, if (i = 1 ∧ j = 0) then 0 else 1,
  property := by simp [det2] }

def S : SL(2,ℤ) := { val :=  λ i j, i - j,
  property := by simp [det2] }

def subgroup_SL {R : Type*} [comm_ring R] {S : subring R} {n : ℕ} : subgroup SL(n,R) :=
begin
  sorry
end

lemma T_action {z : H} {n : ℤ} : ((T^n) : SL(2,ℝ)) • z = (z:ℂ) + (n:ℂ) :=
begin
  sorry
end

lemma is_fundom {z : H} : ∃ g : SL(2, ℤ),  (g • z) ∈ 𝒟 :=
begin

  sorry
end

-- define fundamental domain
-- open region, g.z=w -> g=1
-- all z in H, exists g in G such that g.z in closure F

-- define std domain {|z|>1, |z.re| <1/2}

-- proof std domain is a fund dom for G

-- define modular form

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
