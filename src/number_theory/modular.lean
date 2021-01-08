import linear_algebra.special_linear_group
import data.complex.basic
import group_theory.group_action.defs

noncomputable theory

open matrix
open complex
open matrix.special_linear_group

open_locale classical

def H : set ℂ := {z | z.im >0 }

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

lemma det2 (g: matrix (fin 2) (fin 2) ℝ) :
g.det = (g 0 0 )*(g 1 1)-
(g 1 0 ) * (g  0 1 )
:=
begin
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
    sorry,
  },

  have : complex.norm_sq (bottom g z)≠ 0,
  {
    sorry,
  },

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


lemma GactsHtoH (g : special_linear_group (fin 2) ℝ) {z: ℂ} (hz : z ∈ H ) :
smul_aux g z ∈ H :=
begin
  rw H,
  simp,
  rw ImOfGaction,
  sorry,
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
