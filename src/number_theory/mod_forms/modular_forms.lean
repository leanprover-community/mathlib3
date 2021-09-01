import algebra.module.submodule
import .holomorphic_functions
import .modular_group
import analysis.complex.upper_half_plane
import linear_algebra.general_linear_group
import linear_algebra.special_linear_group

universes u v

open complex


noncomputable theory
/-  This is an attempt to update the kbb birthday repo, so parts are not orginal to me-/

/--The upper half space as a subset of `ℂ` which is convenient sometimes.-/
def upper_half_space := {z : ℂ | 0 <  z.im}

instance: metric_space upper_half_plane:=infer_instance

lemma hcoe : upper_half_space = coe '' (set.univ : set upper_half_plane) :=
begin
simp, refl,
end

lemma upper_half_plane_is_open: is_open upper_half_space  :=
begin
  have : upper_half_space = complex.im⁻¹' set.Ioi 0 :=
    set.ext (λ z, iff.intro (λ hz, set.mem_preimage.mp hz) $ λ hz, hz),
  exact is_open.preimage complex.continuous_im is_open_Ioi,
end

local notation `ℍ'`:=(⟨upper_half_space , upper_half_plane_is_open⟩: open_subs)

local notation `ℍ`:=upper_half_plane

instance : has_coe ℍ' ℍ :=
⟨ λ z, ⟨ z.1, by {simp, cases z, assumption,}, ⟩ ⟩

/--A function `f:ℍ → ℂ` is Petersson, of weight `k ∈ ℤ` (and level one), if for every matrix in
 `γ ∈  SL_2(ℤ)` we have `f(γ  • z)= (c*z+d)^k f(z)` where `γ= ![![a, b], ![c, d]]`,
 and it acts on `ℍ` via Moebius trainsformations. -/
def is_modular_of_level_and_weight (Γ : subgroup SL2Z) (k : ℤ) :=
{ f : ℍ → ℂ | ∀ M : Γ, ∀ z : ℍ,
    f ((M : matrix.GL_pos (fin 2) ℝ) • z) = ((M 1 0 )*z + M 1 1)^k * f z}

variables (Γ : subgroup SL2Z) (k: ℤ)

@[simp] lemma mem_modular (Γ : subgroup SL2Z) (k : ℤ) (f : ℍ → ℂ) :
  f  ∈ is_modular_of_level_and_weight Γ k  ↔
  ∀ M : Γ , ∀ z : ℍ,
  f ((M : matrix.GL_pos (fin 2) ℝ) •   z) = ((M 1 0 )*z + M 1 1)^k * f z := iff.rfl

/--The sum of two modular forms-/
def Modular_sum   (f g : is_modular_of_level_and_weight Γ k) : ℍ → ℂ :=
λ z, f.1 z + g.1 z

/--The definition of the zero modular form, whose values at all points is zero-/
def zero_form : ℍ → ℂ:= (0 : (ℍ → ℂ))

lemma modular_sum_is_modular   (f g : is_modular_of_level_and_weight Γ k) :
  ( Modular_sum Γ k f g ∈  is_modular_of_level_and_weight Γ k):=
begin
  simp only [mem_modular], intros M z, rw Modular_sum, simp only [subtype.val_eq_coe],
  have h1:=f.property,
  simp only [mem_modular, subtype.val_eq_coe] at h1,
  have h2:=g.property, simp only [mem_modular, subtype.val_eq_coe] at h2,
  rw [h1, h2],
  ring,
end

lemma zero_form_is_modular  : (zero_form  ∈ is_modular_of_level_and_weight Γ k) :=
begin
simp only [mem_modular], intros M z, rw zero_form, simp  [mul_zero],
end

lemma zero_simp : ∀ (x: ℍ), (⟨zero_form,  zero_form_is_modular Γ k⟩ :
is_modular_of_level_and_weight Γ k).val x = (0: ℂ) :=

begin
intro x, simp [zero_form],
end

/--The definition of scalar multiplication on `is_modular_of_level_and_weight`-/
def sca_mul_def' :  ℂ →   (is_modular_of_level_and_weight Γ k) →  (ℍ → ℂ):=
λ z f , λ x , z * (f.1 x)

lemma sca_is_modular  (f: is_modular_of_level_and_weight Γ k) (z : ℂ) :
  (sca_mul_def' Γ k  z f) ∈ is_modular_of_level_and_weight Γ k :=
begin
  simp only [sca_mul_def',
  mem_modular,
  subtype.val_eq_coe],
  intros M x,
  have h1:=f.property,
  simp only [mem_modular, subtype.val_eq_coe] at h1,
  rw h1,
  ring,
end

/--The  space of functions that are modular-/
def modular_submodule : submodule (ℂ) (ℍ  → ℂ) := {
  carrier:= { f : ℍ → ℂ |
        ∀ M : Γ, ∀ z : ℍ, f  ((M : matrix.GL_pos (fin 2) ℝ) • z) = ((M 1 0 )*z + M 1 1)^k * f z},
  zero_mem':= by {simp only [forall_const,
    pi.zero_apply, implies_true_iff, eq_self_iff_true, set.mem_set_of_eq, mul_zero], },
  add_mem' := by {intros a b ha hb,
    let f:= (⟨a, ha⟩ : is_modular_of_level_and_weight Γ k),
    let g:= (⟨b, hb⟩ : is_modular_of_level_and_weight Γ k),
    apply modular_sum_is_modular Γ k f g ,
    },
 smul_mem' := by {intros c x hx,
    let f:= (⟨x, hx⟩ : is_modular_of_level_and_weight Γ k),
    apply sca_is_modular Γ k f c,}}

/--A function ` f : ℍ → ℂ` is bounded at infinity if there exist real numbers `M,A` such that
for all `z ∈ ℍ` with `im z ≥ A` we have `abs(f (z)) ≤ M`,
 i.e. the function is bounded as you approach `i∞`.  -/
def is_bound_at_infinity := { f : ℍ → ℂ | ∃ (M A : ℝ), ∀ z : ℍ, im z ≥ A → abs (f z) ≤ M }

/--A function ` f : ℍ → ℂ` is zero at infinity if for any `ε > 0` there exist a real
number `A` such that for all `z ∈ ℍ` with `im z ≥ A` we have `abs(f (z)) ≤ ε`,
 i.e. the function tends to zero as you approach `i∞`.  -/
def is_zero_at_infinity :=
  { f : ℍ → ℂ | ∀ ε : ℝ, 0 < ε  → ∃ A : ℝ, ∀ z : ℍ, A ≤ im z  → abs (f z) ≤ ε }

@[simp]lemma bound_mem (f : ℍ → ℂ):
  (f ∈  is_bound_at_infinity ) ↔ ∃ (M A : ℝ), ∀ z : ℍ, A ≤ im z  → abs (f z) ≤ M := iff.rfl

@[simp]lemma zero_at_inf_mem (f : ℍ → ℂ) :
  (f ∈  is_zero_at_infinity  ) ↔
  ∀ ε : ℝ, 0 < ε  → ∃ A : ℝ, ∀ z : ℍ, A ≤ im z  → abs (f z) ≤ ε := iff.rfl

lemma zero_form_is_bound : (zero_form ) ∈  is_bound_at_infinity:=
begin
  simp only [ bound_mem, ge_iff_le,
  set_coe.forall,
  subtype.coe_mk],
  use (0: ℝ ),
  use (0:ℝ),
  intros x h1,
  rw zero_form,
  simp  [complex.abs_zero],
end

lemma zero_form_is_zero_at_inf : (zero_form ) ∈  is_zero_at_infinity:=
begin
  simp only [ zero_at_inf_mem, gt_iff_lt, ge_iff_le,
    set_coe.forall, subtype.coe_mk],
  intros ε he,
  use (0:ℝ),
  intros x  h1,
  rw zero_form,
  simp  [complex.abs_zero],
  rw le_iff_lt_or_eq,
  simp only [he, true_or],
end

lemma is_zero_at_inf_is_bound (f: ℍ → ℂ): (f ∈ is_zero_at_infinity) → (f ∈ is_bound_at_infinity):=
begin
  simp only [ zero_at_inf_mem, gt_iff_lt, bound_mem, ge_iff_le, set_coe.forall,
    subtype.coe_mk],
  intro H,
  use (1: ℝ),
  apply H,
  norm_cast,
  exact dec_trivial,
end

@[simp]lemma smul_sim (f: ℍ → ℂ) (z : ℂ) (x : ℍ): (z • f) x= z* (f x):=
begin
simp only [algebra.id.smul_eq_mul, pi.smul_apply],
end

/--This is the submodule of functions that are bounded at infinity-/
def bounded_at_infty_submodule: submodule (ℂ) (ℍ  → ℂ):={
  carrier :={ f : ℍ → ℂ | ∃ (M A : ℝ), ∀ z : ℍ, A ≤ im z → abs (f z) ≤ M },
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
  smul_mem' := by {intros c f hyp,
    begin
     cases hyp with M hM,
     cases hM with A hAM,
     existsi (complex.abs c * M),
     existsi A,
     intros z hz,
     have h2:=smul_sim  f c z,
     have h3: abs ((c• f) z ) = abs (c* f z), by {rw h2,},
     rw [complex.abs_mul] at h3,
     have h4:= mul_le_mul_of_nonneg_left (hAM z hz) (complex.abs_nonneg c),
     rw ← h3 at h4,
     convert h4,
     end  },
    }


 /--The submodule of functions that are zero at infinity-/
def zero_at_infty_submodule: submodule (ℂ) (ℍ  → ℂ) := {
  carrier := { f : ℍ → ℂ | ∀ ε : ℝ, 0 < ε  → ∃ A : ℝ, ∀ z : ℍ, A ≤ im z  → abs (f z) ≤ ε },
  zero_mem' := by {simp, intros ε he, use (-1: ℝ ), intros x  h1, tidy, linarith},
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
  smul_mem' := by {intros c f hyp ε hε,
    begin
      by_cases hc : (c = 0),
      { existsi (0 : ℝ ), intros, simp only [hc, pi.zero_apply, complex.abs_zero, zero_smul],
         exact le_of_lt hε },
      have habsinv: 0 < (complex.abs c)⁻¹ :=
        by {simp only [gt_iff_lt, complex.abs_pos, ne.def, inv_pos], exact hc,},
      have hcc: 0 <  (ε / complex.abs c)  :=
        by { rw div_eq_mul_inv, apply mul_pos hε habsinv,},
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
    end },
  }

lemma is_zero_at_inf_is_bound' (f: ℍ → ℂ): (f ∈ is_zero_at_infinity) → (f ∈ is_bound_at_infinity):=
begin
 simp only [zero_at_inf_mem, bound_mem, gt_iff_lt, ge_iff_le, set_coe.forall, subtype.coe_mk],
 intro H,
 use (1: ℝ),
 apply H,
 norm_cast,
 exact dec_trivial,
end

/--The extension of a function from `ℍ` to `ℍ'`-/
def hol_extn (f : ℍ → ℂ) : ℍ' → ℂ := λ (z : ℍ'), (f (z : ℍ) )

/-- A function `f : ℍ → ℂ` is a modular form of level `Γ` and weight `k ∈ ℤ` if it is holomorphic,
 Petersson and bounded at infinity -/
structure is_modular_form_of_lvl_and_weight (Γ : subgroup SL2Z) (k : ℤ) (f : ℍ → ℂ) : Prop :=
  (hol      : is_holomorphic_on (hol_extn f))
  (transf   : is_modular_of_level_and_weight Γ k f)
  (infinity : f ∈ is_bound_at_infinity )

lemma is_modular.mk (Γ : subgroup SL2Z) (k : ℤ) (f : ℍ → ℂ)
  (h :is_holomorphic_on (hol_extn f) )
  (h2: is_modular_of_level_and_weight Γ k f)
  (h3 : f ∈ is_bound_at_infinity ) :
  is_modular_form_of_lvl_and_weight Γ k f :={
  hol := h,
  transf := h2,
  infinity := h3,
}

lemma mod_mem (Γ : subgroup SL2Z) (k : ℤ) (f : ℍ → ℂ) : is_modular_form_of_lvl_and_weight Γ k f ↔
  is_holomorphic_on (hol_extn f) ∧
  is_modular_of_level_and_weight Γ k f ∧
  f ∈ is_bound_at_infinity :=
begin
  split,
  intro hf,
  simp [hf.hol, hf.transf, hf.infinity],
  intro h,
  apply is_modular.mk Γ k f h.1 h.2.1 h.2.2,
end


/-- The zero modular form is a modular form-/
lemma zero_mod_form :  (is_modular_form_of_lvl_and_weight Γ   (k : ℤ) ) (zero_form ):=
{ hol :=  by {rw hol_extn, exact zero_hol ℍ', },
  transf := zero_form_is_modular Γ k,
  infinity := by {simp only [bound_mem, ge_iff_le],
  use (1: ℝ ),
  use (0: ℝ ),
  intros x  h1,
  rw zero_form,
  simp,}
}

/-- A function `f : ℍ → ℂ` is a cusp form of level one and weight `k ∈ ℤ` if it is holomorphic,
 Petersson and zero at infinity -/
structure is_cusp_form_of_lvl_and_weight (Γ : subgroup SL2Z) (k : ℤ) (f : ℍ → ℂ) : Prop :=
  (hol      : is_holomorphic_on (hol_extn f))
  (transf   : is_modular_of_level_and_weight Γ k f)
  (infinity : f ∈ is_zero_at_infinity )

lemma is_cuspform.mk (Γ : subgroup SL2Z) (k : ℤ) (f : ℍ → ℂ)
  (h : is_holomorphic_on (hol_extn f) )
  (h2 : is_modular_of_level_and_weight Γ k f)
  (h3 : f ∈ is_zero_at_infinity ) :
  is_cusp_form_of_lvl_and_weight Γ k f :={
  hol := h,
  transf := h2,
  infinity := h3,
}

lemma cusp_mem (Γ : subgroup SL2Z) (k : ℤ) (f: ℍ → ℂ): is_cusp_form_of_lvl_and_weight Γ k f ↔
  is_holomorphic_on (hol_extn f) ∧
  is_modular_of_level_and_weight Γ k f ∧
  f ∈ is_zero_at_infinity :=
begin
  split,
  intro hf,
  simp [hf.hol, hf.transf, hf.infinity],
  intro h,
  apply is_cuspform.mk Γ k f h.1 h.2.1 h.2.2,
end


/-- The zero modular form is a cusp form-/
lemma zero_cusp_form :  (is_cusp_form_of_lvl_and_weight Γ k)  (zero_form ) :=
{ hol := by {rw hol_extn, exact zero_hol ℍ', },
  transf := zero_form_is_modular Γ k,
  infinity := by {simp only [zero_at_inf_mem, gt_iff_lt, ge_iff_le],
    intros ε he,
    use (-1: ℝ ),
    intros x  h1,
    rw zero_form,
    simp [complex.abs_zero],
    linarith}
}

lemma is_modular_form_of_lvl_and_weight__of_is_cusp_form_of_lvl_and_weight  (f : ℍ → ℂ)
(h : is_cusp_form_of_lvl_and_weight Γ k f) : is_modular_form_of_lvl_and_weight Γ k f :=
⟨h.1, h.2, is_zero_at_inf_is_bound' f h.3⟩

/-- This is the space of modular forms of level `Γ` and weight `k`-/
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

localized "notation `Mₖ(`Γ`)`:= space_of_mod_forms_of_level_and_weight Γ k" in modular_forms


/-- This is the space of cuspforms of level `Γ` and weigth `k`-/
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

localized "notation `Sₖ(`Γ`)`:= space_of_cusp_forms_of_level_and_weight Γ k" in modular_forms
