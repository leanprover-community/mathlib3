import algebra.module.submodule
import .holomorphic_functions
import .modular_group
import analysis.complex.upper_half_plane
import linear_algebra.general_linear_group
import linear_algebra.special_linear_group

universes u v

open complex


noncomputable theory



def upper_half_space := {z : ℂ | z.im > 0}

instance: metric_space upper_half_plane:=infer_instance

lemma hcoe : upper_half_space = coe '' (set.univ : set upper_half_plane) :=
begin
simp, tidy,
end


lemma upper_half_plane_is_open: is_open upper_half_space  :=
begin
have : upper_half_space = complex.im⁻¹' set.Ioi 0 := set.ext (λ z, iff.intro (λ hz, set.mem_preimage.mp hz) $ λ hz, hz),
exact is_open.preimage complex.continuous_im is_open_Ioi,
end




local notation `ℍ'`:=(⟨upper_half_space , upper_half_plane_is_open⟩: open_subs)
local notation `ℍ`:=upper_half_plane

instance : has_coe ℍ ℍ':=
⟨λ (z: ℍ), ⟨z.1, by {simp, cases z, assumption, }⟩⟩

instance : has_coe ℍ' ℍ :=
⟨ λ z, ⟨ z.1, by {simp, cases z, assumption,}, ⟩ ⟩




/-  This is an attempt to update the kbb birthday repo, so most is not orginal to me-/

/-This contains the definition of modular forms of weight `z ∈ ℤ` and level one. -/


/--A function `f:ℍ → ℂ` is Petersson, of weight `k ∈ ℤ` (and level one), if for every matrix in `γ ∈  SL_2(ℤ)` we have
`f(γ  • z)= (c*z+d)^k f(z)` where `γ= ![![a, b], ![c, d]]` (will later generalize to other levels), and it acts on `ℍ` via Moebius trainsformations. -/
def is_modular_of_level_and_weight (Γ : subgroup SL2Z) (k : ℤ) :=
{ f : ℍ → ℂ | ∀ M : Γ, ∀ z : ℍ, f  ((M : matrix.GL_pos (fin 2) ℝ) • z) = ((M 1 0 )*z + M 1 1)^k * f z}

variables (Γ : subgroup SL2Z) (k: ℤ)

lemma ext2 (k : ℤ) (f g :  is_modular_of_level_and_weight Γ k): f = g ↔ ∀ (x : ℍ ), f.1 x = g.1 x:=

begin
cases g, cases f, dsimp at *, simp at *, fsplit,
work_on_goal 0 { intros ᾰ x h, induction ᾰ, refl }, intros ᾰ, ext1, cases x,
tactic.ext1 [] {new_goals := tactic.new_goals.all}, work_on_goal 0 { solve_by_elim }, solve_by_elim,
end


@[simp] lemma mem_modular (Γ : subgroup SL2Z) (k : ℤ) (f: ℍ → ℂ) :
  f  ∈ is_modular_of_level_and_weight Γ k  ↔
  ∀ M : Γ , ∀ z : ℍ,
  f ((M : matrix.GL_pos (fin 2) ℝ) •   z) = ((M 1 0 )*z + M 1 1)^k * f z := iff.rfl


/--The sum of two modular forms-/
def Modular_sum   (f g : is_modular_of_level_and_weight Γ k): ℍ → ℂ :=
λ z, f.1 z + g.1 z

/--The definition of the zero modular form, whose values at all points is zero-/
def zero_form  : ℍ → ℂ:=
λ z , (0: ℂ)

/--The negative of a modular form is the modular form whose values at each point are the negative of the original form-/
def neg_form (f : is_modular_of_level_and_weight Γ k) : ℍ → ℂ:=
λ z, - f.1 z

lemma modular_sum_is_modular   (f g : is_modular_of_level_and_weight Γ k):
( Modular_sum Γ k f g ∈  is_modular_of_level_and_weight Γ k):=
begin
simp only [mem_modular], intros M z, rw Modular_sum, simp only [subtype.val_eq_coe],
have h1:=f.property,
simp only [mem_modular, subtype.val_eq_coe] at h1,
 have h2:=g.property, simp only [mem_modular, subtype.val_eq_coe] at h2,
 rw [h1, h2],
 ring,
end

lemma zero_form_is_modular  : (zero_form  ∈ is_modular_of_level_and_weight Γ k):=

begin
simp only [mem_modular], intros M z, rw zero_form, simp only [mul_zero],
end

lemma zero_simp : ∀ (x: ℍ), (⟨zero_form,  zero_form_is_modular Γ k⟩ :
is_modular_of_level_and_weight Γ k).val x = (0: ℂ) :=

begin
intro x, simp [zero_form],
end



def sca_mul_def' :  ℂ →   (is_modular_of_level_and_weight Γ k) →  (ℍ → ℂ):=
λ z f , λ x , z * (f.1 x)

lemma sca_is_modular  (f: is_modular_of_level_and_weight Γ k) (z : ℂ) :
(sca_mul_def' Γ k  z f) ∈ is_modular_of_level_and_weight Γ k :=

begin
simp only [sca_mul_def', mem_modular, subtype.val_eq_coe], intros M x, have h1:=f.property,
simp only [mem_modular, subtype.val_eq_coe] at h1, rw h1, ring,
end



def modular_submodule : submodule (ℂ) (ℍ  → ℂ):={
carrier:= { f : ℍ → ℂ | ∀ M : Γ, ∀ z : ℍ, f  ((M : matrix.GL_pos (fin 2) ℝ) • z) = ((M 1 0 )*z + M 1 1)^k * f z},
zero_mem':= by {simp only [forall_const, pi.zero_apply, implies_true_iff, eq_self_iff_true, set.mem_set_of_eq, mul_zero], },
add_mem' := by {intros a b ha hb,
let f:= (⟨a, ha⟩ : is_modular_of_level_and_weight Γ k),
let g:= (⟨b, hb⟩ : is_modular_of_level_and_weight Γ k),
 apply modular_sum_is_modular Γ k f g ,
 },
 smul_mem' := by {intros c x hx,
 let f:= (⟨x, hx⟩ : is_modular_of_level_and_weight Γ k),
 apply sca_is_modular Γ k f c,
}
}

/--A function ` f : ℍ → ℂ` is bounded at infinity if there exist real numbers `M,A` such that
for all `z ∈ ℍ` with `im z ≥ A` we have `abs(f (z)) ≤ M`. i.e. the function is bounded as you approach `i∞`.  -/
def is_bound_at_infinity := { f : ℍ → ℂ | ∃ (M A : ℝ), ∀ z : ℍ, im z ≥ A → abs (f z) ≤ M }




/--A function ` f : ℍ → ℂ` is zero at infinity if for any `ε > 0` there exist a real number `A` such that
for all `z ∈ ℍ` with `im z ≥ A` we have `abs(f (z)) ≤ ε`. i.e. the function tends to zero as you approach `i∞`.  -/
def is_zero_at_infinity := { f : ℍ → ℂ | ∀ ε : ℝ, ε > 0 → ∃ A : ℝ, ∀ z : ℍ, im z ≥ A → abs (f z) ≤ ε }

@[simp]lemma bound_mem (f: ℍ → ℂ):
(f ∈  is_bound_at_infinity ) ↔ ∃ (M A : ℝ), ∀ z : ℍ, im z ≥ A → abs (f z) ≤ M:=iff.rfl

@[simp]lemma zero_at_inf_mem (f: ℍ → ℂ):
(f ∈  is_zero_at_infinity  ) ↔ ∀ ε : ℝ, ε > 0 → ∃ A : ℝ, ∀ z : ℍ, im z ≥ A → abs (f z) ≤ ε:=iff.rfl


lemma zero_form_is_bound : (zero_form ) ∈  is_bound_at_infinity:=

begin
simp only [ bound_mem, ge_iff_le, set_coe.forall, subtype.coe_mk],
use (0: ℝ ), use (0:ℝ), intros x h1, rw zero_form, simp only [complex.abs_zero],
end

lemma zero_form_is_zero_at_inf : (zero_form ) ∈  is_zero_at_infinity:=

begin
simp only [ zero_at_inf_mem, gt_iff_lt, ge_iff_le,
set_coe.forall, subtype.coe_mk], intros ε he, use (0:ℝ),
intros x  h1, rw zero_form, simp only [complex.abs_zero], rw le_iff_lt_or_eq, simp only [he, true_or],
end

lemma is_zero_at_inf_is_bound (f: ℍ → ℂ): (f ∈ is_zero_at_infinity) → (f ∈ is_bound_at_infinity):=
begin
simp only [ zero_at_inf_mem, gt_iff_lt, bound_mem, ge_iff_le, set_coe.forall,
subtype.coe_mk],intro H, use (1: ℝ), apply H, norm_cast, exact dec_trivial,
end





lemma abs_ew (a b : ℂ) (h : a = b): abs a = abs b:=
begin
rw h,
end



@[simp]lemma smul_sim (f: ℍ → ℂ) (z : ℂ) (x : ℍ): (z • f) x= z* (f x):=

begin
simp only [algebra.id.smul_eq_mul, pi.smul_apply],
end

/--This is the submodule of functions that are bounded at infinity-/
def bounded_at_infty_submodule: submodule (ℂ) (ℍ  → ℂ):={
  carrier :={ f : ℍ → ℂ | ∃ (M A : ℝ), ∀ z : ℍ, im z ≥ A → abs (f z) ≤ M },
  zero_mem' :=by {simp, use (1: ℝ ), use (0: ℝ ), intros x  h1, norm_cast, simp, },
  add_mem' := by  {intros f g hf hg, begin
    cases hf with Mf hMf,
    cases hg with Mg hMg,
    cases hMf with Af hAMf,
    cases hMg with Ag hAMg,
    existsi (Mf + Mg),
    existsi (max Af Ag),
    intros z hz,
    simp,
    apply le_trans (complex.abs_add _ _),
    apply add_le_add,
    { refine hAMf z _,
      exact le_trans (le_max_left _ _) hz },
    { refine hAMg z _,
      exact le_trans (le_max_right _ _) hz }
  end},


  smul_mem' := by {intros c f hyp,  begin
    cases hyp with M hM,
    cases hM with A hAM,
    existsi (complex.abs c * M),
    existsi A,
    intros z hz,
    have h2:=smul_sim  f c z, have h3:=abs_ew ((c• f) z ) (c* f z) h2, rw [complex.abs_mul] at h3,
    have h4:= mul_le_mul_of_nonneg_left (hAM z hz) (complex.abs_nonneg c), rw ← h3 at h4, convert h4,
  end  }, }


 /--The submodule of functions that are zero at infinity-/
def zero_at_infty_submodule: submodule (ℂ) (ℍ  → ℂ):={
  carrier :={ f : ℍ → ℂ | ∀ ε : ℝ, ε > 0 → ∃ A : ℝ, ∀ z : ℍ, im z ≥ A → abs (f z) ≤ ε },
  zero_mem' :=by {simp, intros ε he, use (-1: ℝ ), intros x  h1, tidy, linarith},
  add_mem' := by  {intros f g hf hg ε hε, begin
    cases hf (ε/2) (half_pos hε) with Af hAf,
    cases hg (ε/2) (half_pos hε) with Ag hAg,
    existsi (max Af Ag),
    intros z hz,
    simp,
    apply le_trans (complex.abs_add _ _),
    rw show ε = ε / 2 + ε / 2, by simp,
    apply add_le_add,
    { refine hAf z (le_trans (le_max_left _ _) hz) },
    { refine hAg z (le_trans (le_max_right _ _) hz) }
  end,},


  smul_mem' := by {intros c f hyp ε hε, begin
    by_cases hc : (c = 0),
    { existsi (0 : ℝ ), intros, simp only [hc, pi.zero_apply, complex.abs_zero, zero_smul], exact le_of_lt hε },
    have habsinv: (complex.abs c)⁻¹>0:= by {simp only [gt_iff_lt, complex.abs_pos, ne.def, inv_pos], exact hc,},
    have hcc:  (ε / complex.abs c) > 0 := by {simp, rw div_eq_mul_inv, apply mul_pos hε habsinv,},
    {cases hyp (ε / complex.abs c) (hcc) with A hA,
     existsi A,
      intros z hz,
      simp,
      rw show ε = complex.abs c * (ε / complex.abs c),
      begin
        rw [mul_comm],
        refine (div_mul_cancel _ _).symm,
        simp [hc]
      end,
      apply mul_le_mul_of_nonneg_left (hA z hz) (complex.abs_nonneg c), }

  end }, }



lemma bound_mem' (f: ℍ → ℂ): (f ∈  is_bound_at_infinity ) ↔
  ∃ (M A : ℝ), ∀ z : ℍ, im z ≥ A → abs (f z) ≤ M := iff.rfl


lemma zero_at_inf_mem' (f: ℍ → ℂ):
  (f ∈  is_zero_at_infinity  ) ↔
  ∀ ε : ℝ, ε > 0 → ∃ A : ℝ, ∀ z : ℍ, im z ≥ A → abs (f z) ≤ ε := iff.rfl




lemma is_zero_at_inf_is_bound' (f: ℍ → ℂ): (f ∈ is_zero_at_infinity) → (f ∈ is_bound_at_infinity):=
begin
simp only [zero_at_inf_mem', bound_mem', gt_iff_lt, ge_iff_le, set_coe.forall, subtype.coe_mk],
 intro H,
 use (1: ℝ),
 apply H,
 norm_cast,
 exact dec_trivial,
end


/-- A function `f : ℍ → ℂ` is a modular form of level `Γ` and weight `k ∈ ℤ` if it is holomorphic,
 Petersson and bounded at infinity -/

def hol_extn (f: ℍ → ℂ): ℍ' → ℂ :=
λ (z : ℍ'), (f (z: ℍ) )

structure is_modular_form_of_lvl_and_weight (Γ : subgroup SL2Z) (k : ℤ) (f : ℍ → ℂ) : Prop :=
(hol      : is_holomorphic_on (hol_extn f))
(transf   : is_modular_of_level_and_weight Γ k f)
(infinity : f ∈ is_bound_at_infinity )

def is_modular.mk (Γ : subgroup SL2Z) (k : ℤ) (f: ℍ → ℂ)
  (h :is_holomorphic_on (hol_extn f) )
  (h2: is_modular_of_level_and_weight Γ k f)
  (h3 : f ∈ is_bound_at_infinity ):
  is_modular_form_of_lvl_and_weight Γ k f :={
  hol:= h,
  transf:= h2,
  infinity:= h3,
}

lemma mod_mem (Γ : subgroup SL2Z) (k : ℤ) (f: ℍ → ℂ): is_modular_form_of_lvl_and_weight Γ k f ↔
is_holomorphic_on (hol_extn f) ∧ is_modular_of_level_and_weight Γ k f ∧  f ∈ is_bound_at_infinity :=
begin
split, intro hf, simp [hf.hol, hf.transf, hf.infinity],
intro h,
apply is_modular.mk Γ k f h.1 h.2.1 h.2.2,
end


/-- The zero modular form is a modular form-/
lemma zero_mod_form :  (is_modular_form_of_lvl_and_weight Γ   (k : ℤ) ) (zero_form ):=
{ hol :=  by {rw hol_extn, exact zero_hol ℍ', },
  transf := zero_form_is_modular Γ k,
  infinity := by {simp only [bound_mem', ge_iff_le],
  use (1: ℝ ),
  use (0: ℝ ),
  intros x  h1,
  rw zero_form,
  norm_cast,
  exact dec_trivial}
}

/-- A function `f : ℍ → ℂ` is a cusp form of level one and weight `k ∈ ℤ` if it is holomorphic,
 Petersson and zero at infinity -/


structure is_cusp_form_of_lvl_and_weight (Γ : subgroup SL2Z) (k : ℤ) (f : ℍ → ℂ) : Prop :=
(hol      : is_holomorphic_on (hol_extn f))
(transf   : is_modular_of_level_and_weight Γ k f)
(infinity : f ∈ is_zero_at_infinity )

def is_cuspform.mk (Γ : subgroup SL2Z) (k : ℤ) (f: ℍ → ℂ)
  (h :is_holomorphic_on (hol_extn f) )
  (h2: is_modular_of_level_and_weight Γ k f)
  (h3 : f ∈ is_zero_at_infinity ):
  is_cusp_form_of_lvl_and_weight Γ k f :={
  hol:= h,
  transf:= h2,
  infinity:= h3,
}

lemma cusp_mem (Γ : subgroup SL2Z) (k : ℤ) (f: ℍ → ℂ): is_cusp_form_of_lvl_and_weight Γ k f ↔
is_holomorphic_on (hol_extn f) ∧ is_modular_of_level_and_weight Γ k f ∧  f ∈ is_zero_at_infinity :=
begin
split, intro hf, simp [hf.hol, hf.transf, hf.infinity],
intro h,
apply is_cuspform.mk Γ k f h.1 h.2.1 h.2.2,
end


/-- The zero modular form is a cusp form-/
lemma zero_cusp_form :  (is_cusp_form_of_lvl_and_weight Γ k)  (zero_form ):=
{ hol := by {rw hol_extn, exact zero_hol ℍ', },
  transf := zero_form_is_modular Γ k,
  infinity := by {simp only [zero_at_inf_mem', gt_iff_lt, ge_iff_le], intros ε he, use (-1: ℝ ),
  intros x  h1, rw zero_form, simp,linarith}
}



lemma is_modular_form_of_lvl_and_weight__of_is_cusp_form_of_lvl_and_weight  (f : ℍ → ℂ)
(h : is_cusp_form_of_lvl_and_weight Γ k f) : is_modular_form_of_lvl_and_weight Γ k f :=
⟨h.1, h.2, is_zero_at_inf_is_bound' f h.3⟩


def space_of_mod_forms_of_level_and_weight (Γ : subgroup SL2Z) (k : ℤ): submodule ℂ (ℍ → ℂ):={
  carrier:={ f : ℍ → ℂ | is_modular_form_of_lvl_and_weight Γ k f},
  zero_mem':=by {simp, apply zero_mod_form, },
  add_mem' :=by {simp, intros a b ha hb,
    simp only [mod_mem, pi.add_apply, ge_iff_le, subtype.forall, upper_half_plane.coe_im],
    split,
    apply add_hol,
    simp,
    apply ha.hol,
    apply hb.hol,
    split,
    apply (modular_submodule Γ k).add_mem' ha.transf hb.transf,
    apply bounded_at_infty_submodule.add_mem' ha.infinity hb.infinity, },
  smul_mem' := by {intros c f hf,  simp at *,
    simp only [mod_mem, complex.abs_mul, ge_iff_le, subtype.forall, smul_sim, upper_half_plane.coe_im],
    split,
    apply smul_hol,
    simp [hf.hol],
    exact hf.hol,
    split,
    apply (modular_submodule Γ k).smul_mem',
    apply hf.transf,
    apply bounded_at_infty_submodule.smul_mem' c hf.infinity,},

}


def space_of_cusp_forms_of_level_and_weight (Γ : subgroup SL2Z) (k : ℤ): submodule ℂ (ℍ → ℂ):={
  carrier:={ f : ℍ → ℂ | is_cusp_form_of_lvl_and_weight Γ k f},
  zero_mem':=by {simp, apply zero_cusp_form, },
  add_mem' :=by {simp, intros a b ha hb,
    simp only [cusp_mem, pi.add_apply, ge_iff_le, subtype.forall, upper_half_plane.coe_im],
    split,
    apply add_hol,
    simp,
    apply ha.hol,
    apply hb.hol,
    split,
    apply (modular_submodule Γ k).add_mem' ha.transf hb.transf,
    apply zero_at_infty_submodule.add_mem' ha.infinity hb.infinity, },
  smul_mem' := by {intros c f hf,  simp at *,
    simp only [cusp_mem, complex.abs_mul, ge_iff_le, subtype.forall, smul_sim, upper_half_plane.coe_im],
    split,
    apply smul_hol,
    simp [hf.hol],
    exact hf.hol,
    split,
    apply (modular_submodule Γ k).smul_mem',
    apply hf.transf,
    apply zero_at_infty_submodule.smul_mem' c hf.infinity,},

}




/-
instance (k : ℕ) : is_submodule (is_modular_form k) := is_submodule.inter_submodule

instance (k : ℕ) : is_submodule (is_cusp_form k) := is_submodule.inter_submodule

/- def Hecke_operator {k : ℕ} (m : ℤ) : modular_forms k → modular_forms k :=
λ f,
(m^k.pred : ℂ) • (sorry : modular_forms k) -- why is this • failing?
 -/
 -/


/-
def sca_mul_def : ℂ → (is_modular_of_level_and_weight Γ k) → (is_modular_of_level_and_weight Γ k) :=
λ z f, ⟨ sca_mul_def' Γ k z f, sca_is_modular Γ k f z⟩

@[simp]lemma zere_form_val : ∀ (x : ℍ), (0 : is_modular_of_level_and_weight Γ k ).1 x = (0 : ℂ):=
begin
simp only [set_coe.forall, subtype.val_eq_coe], intros x , refl,
end

@[simp]lemma modular_sum_val  (f g : is_modular_of_level_and_weight Γ k): (f+g).1=f.1+g.1:=
begin
simp only [subtype.val_eq_coe], refl,
end

lemma ad_sum (r s : ℂ ) (f : is_modular_of_level_and_weight Γ k) :
sca_mul_def Γ k (r+s) f = sca_mul_def  Γ k r f +sca_mul_def Γ k s f :=

begin
have:=ext2 Γ k (sca_mul_def Γ k (r+s) f)  (sca_mul_def Γ k r f +sca_mul_def Γ k s f),
  rw this,
  simp only [sca_mul_def,sca_mul_def'],
  intro x,
  simp only [subtype.val_eq_coe], ring_nf,
end


instance  : module ℂ (is_modular_of_level_and_weight Γ k) :=


{ smul:=sca_mul_def Γ k ,
  smul_zero:= by {simp [sca_mul_def, sca_mul_def'], intro r, ext, simp only [zero_re, subtype.coe_mk],
   rw ← subtype.val_eq_coe, simp only [zero_re, zere_form_val], simp only [zero_im, subtype.coe_mk], refl,},
  zero_smul:= by {simp only [zero_re, zero_im, zere_form_val, mem_modular, set_coe.forall, subtype.coe_mk, mul_zero, subtype.val_eq_coe],
  intro x, intro h,
  simp only [sca_mul_def, sca_mul_def', zero_mul], refl,},
  add_smul:= by {simp [sca_mul_def,sca_mul_def'], intros r s h, have:= ad_sum Γ k r s h, assumption,},
  smul_add:= by {simp [sca_mul_def, sca_mul_def'], simp [ext2], intros r f g x b , ring_nf,  },
  one_smul:=by {simp [sca_mul_def, sca_mul_def'],},
  mul_smul:=by {simp [sca_mul_def, sca_mul_def'], intros x y f, ring_nf,},

}


lemma neg_of_modular_is_modular  (f : is_modular_of_level_and_weight Γ k): (neg_form Γ k f ∈ is_modular_of_level_and_weight Γ k ):=

begin
simp only [mem_modular], rw neg_form, intros M z, have h1:=f.property, simp only [mem_modular, subtype.val_eq_coe] at h1, ring_nf,
rw subtype.val_eq_coe, rw h1, ring,
end

lemma add_l_neg  (f : is_modular_of_level_and_weight Γ k ) : Modular_sum Γ k ⟨ neg_form Γ k f, neg_of_modular_is_modular Γ k f ⟩  f = zero_form :=

begin
simp only [Modular_sum, zero_form, neg_form, add_left_neg],
end

lemma modular_sum_commutative  (f g : is_modular_of_level_and_weight Γ k ): Modular_sum Γ k f g =
Modular_sum Γ k g f :=

begin
simp only [Modular_sum, subtype.val_eq_coe],  ext, simp only [add_re], ring, simp only [add_im], ring,
end

instance (k : ℤ): add_comm_group (is_modular_of_level_and_weight Γ k):=
{add:= λ f g, ⟨ Modular_sum Γ k f g,  modular_sum_is_modular Γ k f g⟩,
add_comm:= by {intros f g, have:=modular_sum_commutative Γ k f g, cases g, cases f, dsimp at *, apply subtype.ext, assumption,},
add_assoc:= by {intros f g h, simp only [subtype.mk_eq_mk], rw Modular_sum, simp only [subtype.val_eq_coe], rw Modular_sum,
simp only [subtype.val_eq_coe], rw Modular_sum,
simp only [subtype.val_eq_coe], rw Modular_sum,
simp, ext, simp, ring, ring_nf, },
zero:=⟨zero_form , zero_form_is_modular Γ k⟩,
add_zero:=by {intro f, simp only, ext, simp only [zero_form, subtype.coe_mk], rw Modular_sum,
simp only [add_zero, subtype.val_eq_coe],
simp only [Modular_sum, zero_form, add_zero, subtype.coe_eta, subtype.val_eq_coe],},
zero_add:=by {intro f, simp only, ext, simp only [zero_form, subtype.coe_mk], rw Modular_sum,
simp only [add_zero, subtype.val_eq_coe],
simp, simp [zero_form, Modular_sum],  },
neg:= λ f, ⟨neg_form Γ k f, neg_of_modular_is_modular Γ k f ⟩,
add_left_neg:=by {simp, intros f h, have:=add_l_neg Γ k ⟨f,h⟩, dsimp at *, apply subtype.ext, assumption,}  ,
}


-/

 #lint
