import linear_algebra.special_linear_group
import data.complex.basic
import group_theory.group_action.defs

noncomputable theory

open matrix
open complex
open matrix.special_linear_group

open_locale classical
open_locale big_operators


def H : set ℂ := {z | 0< z.im}

--def SL2R := special_linear_group (fin 2) ℝ


def top : --SL2R --
(special_linear_group (fin 2) ℝ)
 → ℂ → ℂ :=
λ g, λ z,
(
  ((g : matrix (fin 2) (fin 2) ℝ) 0 0 ) * z + ((g : matrix (fin 2) (fin 2) ℝ) 0 1 )
)

def bottom : --SL2R --
(special_linear_group (fin 2) ℝ)
 → ℂ → ℂ :=
λ g, λ z,
(
  ((g : matrix (fin 2) (fin 2) ℝ) 1 0 ) * z + ((g : matrix (fin 2) (fin 2) ℝ) 1 1 )
)
--λ g, λ z, ((special_linear_group.coe_matrix g) 0 0 )

def smul_aux : --SL2R --
(special_linear_group (fin 2) ℝ)
 → ℂ → ℂ :=
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


lemma det2 (g: matrix (fin 2) (fin 2) ℝ) :
g.det = (g 0 0 )*(g 1 1)-
(g 1 0 ) * (g  0 1 )
:=
begin
  simp only [det],
--  rw finset.prod_sum,
  --rw det,

  let s : finset (fin 2) := {(1 : fin 2) }ᶜ,

  have univIs : finset.univ = insert (1: fin 2) s,
  {
    ext x,
    simp,
    cases split_fin2 x,
    rw h,
    simp,
    rw h,
    simp,
    -- ALEX HOMEWORK
  },


  have eachPerm : ∀ (σ : equiv.perm (fin 2)),
  ∏ i in finset.univ, g (σ i) i = g (σ 1) 1 * ∏ i in  s , g (σ i) i,
  {
    intros,
    rw univIs,
    refine finset.prod_insert _,
    simp [s],
  },

--  rw sum_add_distrib

/-
  rw this,

  have sIs : s = {(0 : fin 2)},
  {
    simp [s],
    ext x,
    simp,
    cases split_fin2 x,
    rw h,
    simp,
    rw h,
    simp,
    -- ALEX HOMEWORK
--    rw eq_zero_of_ne_one,
  },

  rw sIs,

  rw finset.prod_singleton,
  ring,

-/


--  library_search,
--  rw det,
  sorry,
end
/-
lemma junk (z: ℂ ) : (complex.norm_sq z :ℂ ) = z * (complex.conj z) :=
begin
  exact (complex.mul_conj z).symm,
end
-/

lemma ImOfGaction (g : special_linear_group (fin 2) ℝ) (z: ℂ) :
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

lemma bottomRowNonZ (g : special_linear_group (fin 2) ℝ) :
g.val 1 0 = 0 → g.val 1 1 = 0 → false :=
begin
  intros h1 h2,
  have detIs := g.2,
  rw det2 at detIs,
  rw [h1, h2] at detIs,
  simp at detIs,
  exact detIs,
end


lemma czPd_nonZ (z:ℂ ) (g : special_linear_group (fin 2) ℝ) :
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

lemma czPd_nonZ_CP (z:ℂ ) (g : special_linear_group (fin 2) ℝ) :
 z.im ≠  0 →  bottom g z ≠  0 :=
begin
  intros h1,
  by_contra,
  simp at h,
  have h2 := czPd_nonZ _ _ h,
  exact h1 h2,
end

lemma im_nonZ_then_nonZ (z : ℂ  ) : z.im ≠ 0 → z≠ 0
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

lemma GactsHtoH (g : special_linear_group (fin 2) ℝ) {z: ℂ} (hz : z ∈ H ) :
smul_aux g z ∈ H :=
begin
  rw H,
  simp,
  rw ImOfGaction,
  have imZpos : 0<z.im,
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
  exact div_pos imZpos norm2Pos,
/-
  let czPd2 := bottom g z,

  have : norm_sq (bottom g z) = norm_sq czPd2,
  {
    refl,
  },
  rw this,
  clear this,

  have : 0 <  norm_sq (czPd2),
  {
    rw complex.norm_sq_pos,
    suffices : (czPd2).im ≠ 0,
    refine im_nonZ_then_nonZ _ _,
    exact this,
    have : czPd2.im = (bottom g z).im,
    { refl,},
    rw this,
    have zZero := czPd_nonZ_CP _ _ _,


    sorry,
  },
  refine div_pos imZpos this,
-/
end

--lemma OneActsHtoH  (z: ℂ) : smul_aux 1 z = z :=  by {rw [smul_aux, top, bottom], simp}





instance : mul_action (special_linear_group (fin 2) ℝ) H :=
{ smul := λ g, λ z, ⟨smul_aux g z, GactsHtoH g z.2 ⟩ ,
  one_smul := λ z, by {apply subtype.ext, simp [smul_aux, top, bottom]},
  mul_smul := _
  -- ALEX
  }


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
