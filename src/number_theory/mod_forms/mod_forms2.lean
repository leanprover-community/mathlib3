import algebra.module.submodule
import .holomorphic_functions
import analysis.complex.upper_half_plane
import linear_algebra.general_linear_group
import linear_algebra.special_linear_group
import algebra.direct_sum.ring
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

local notation `SL2Z` := matrix.special_linear_group (fin 2) ℤ

instance : has_coe ℍ' ℍ :=
⟨ λ z, ⟨ z.1, by {simp, cases z, assumption,}, ⟩ ⟩

local notation `GL2P`:= (matrix.GL_pos (fin 2) ℝ)

variable (M : GL2P)

lemma aux (a b c : ℂ) : a*b⁻¹*c⁻¹=a*(b*c)⁻¹:=
begin
field_simp,
end

lemma aux1 (a b c d e: ℂ) (k : ℤ) : (a * b^k * (c * d^k) )⁻¹*e = (a * c * (b * d)^k)⁻¹*e :=
begin
have : a * b^k * (c * d^k) = a * c * (b * d)^k , by  {simp_rw mul_fpow b d k, ring,},
rw this,
end

variables (G : Type*) (α  : Type*) (β : Type*) [group G] [mul_action G α] [mul_action G β]

def my_smul (k : ℤ) : G → (α → β) → (α → β):=
λ g f, (λ (x : α), g^k • f (g⁻¹ • x)    )

def slash_k (k : ℤ) : GL2P → (ℍ → ℂ) → (ℍ → ℂ ) :=
λ M f,
(λ (x : ℍ), f (M  •   x) * ((matrix.general_linear_group.det M.1 ) * ((M 1 0 )*x + M 1 1)^k)⁻¹)

namespace modular_forms

variables (Γ : subgroup SL2Z) (C : GL2P) (k: ℤ) (f  : (ℍ → ℂ))

localized "notation  f  ` ∣ₖ[`:100 k `]`:0 γ :100 := slash_k k γ f" in modular_form

lemma slash_k_right_action (k : ℤ) (A B : GL2P) (f : ℍ → ℂ ) : (f ∣ₖ[k] A) ∣ₖ[k] B = f ∣ₖ[k] (A*B):=
begin
  simp_rw slash_k,
    simp,
  ext1,
  have e1:= upper_half_plane.denom_cocycle A B x,  simp only [upper_half_plane.denom,
    matrix.general_linear_group.coe_mul, coe_fn_coe_base, subgroup.coe_mul,
      matrix.general_linear_group.coe_fn_eq_coe] at e1,
  rw e1,
  simp_rw [upper_half_plane.smul_aux,
    upper_half_plane.smul_aux',upper_half_plane.num,upper_half_plane.denom],
  simp only [coe_fn_coe_base, subtype.coe_mk, matrix.general_linear_group.coe_fn_eq_coe],
  dsimp,
  have e2:= upper_half_plane.mul_smul' A B x,
  have e3: (A * B) • x = A • B • x , by {convert e2,} ,
  rw e3,
  ring_nf,
  simp_rw aux,
  ring_nf,
  simp_rw aux1,
end

lemma slash_k_add (k : ℤ) (A : GL2P) (f g : ℍ → ℂ ) : (f +g )  ∣ₖ[k] A = (f ∣ₖ[k] A) +(g ∣ₖ[k] A) :=
begin
  simp_rw slash_k,
  simp,
  ext1,
  simp,
  ring,
end

lemma slash_k_mul_one (k : ℤ) (f : ℍ → ℂ ) : (f ∣ₖ[k] 1) = f :=
begin
 simp_rw slash_k,
 ext1,
 simp,
end

lemma smul_slash_k (k : ℤ) (A : GL2P) (f : ℍ → ℂ ) (c  : ℂ) : (c • f) ∣ₖ[k] A = c • (f ∣ₖ[k] A) :=
begin
ext1, simp_rw slash_k,
simp,ring,
end



/--The  space of functions that are modular-/
def modular_submodule (k : ℤ)  (Γ : subgroup SL2Z): submodule (ℂ) (ℍ  → ℂ) := {
  carrier:={f : (ℍ → ℂ) | ∀ (γ : Γ),  (f ∣ₖ[k] (γ : GL2P)) = f },
  zero_mem':= by {simp, simp_rw slash_k, simp, refl, },
  add_mem' := by {intros f g hf hg, simp at *, intro γ,  have hff:= hf γ,have hgg:= hg γ,
    rw ← coe_coe at *, rw ← coe_coe at *, rw slash_k_add k γ f g, rw [hff, hgg], },
 smul_mem' := by {intros c f hf, simp at *, intro γ, have hff:= hf γ,
    have: (c • f)  ∣ₖ[k] γ = c • (f  ∣ₖ[k] γ ), by {apply smul_slash_k}, rw ←  coe_coe at *,rw ←  coe_coe at *,
    rw hff at this, apply this,}}

lemma modular_mem (k : ℤ) (Γ : subgroup SL2Z) (f : ℍ → ℂ) :
  f ∈ (modular_submodule k Γ) ↔  ∀ (γ : Γ),  (f ∣ₖ[k] (γ : GL2P)) = f := iff.rfl

lemma det_coe_sl (A: SL2Z): (A: GL (fin 2) ℝ).1.det= (A.1.det: ℝ):=
begin
have:=A.2, rw this, simp, rw ← coe_coe, rw ← coe_coe, simp,
end

lemma det_coe_g (Γ : subgroup SL2Z) (γ : Γ): (((γ : SL2Z ) : GL2P) : GL (fin 2) ℝ).1.det= (γ.1.1.det: ℝ):=
begin
simp,
have h:= γ.1.property,
simp only [ subtype.val_eq_coe] at h,
have h2:= det_coe_sl γ.1, simp only [ subtype.val_eq_coe] at h2,
rw ← coe_coe, rw ←  coe_coe, rw ←  coe_coe, rw ←  coe_coe,
cases γ, cases γ_val, dsimp at *, simp at *,
end

lemma coe_aux (Γ : subgroup SL2Z) (γ : Γ) :  ∀ i j, ((γ : matrix.GL_pos (fin 2) ℝ) i j : ℂ) = ((γ i j : ℤ) : ℝ) :=
begin
intros i j,
have :=SL2Z.mat_vals  γ.1 i j, simp at *,
rw ← coe_coe,
cases j, cases i, cases γ, cases γ_val, dsimp at *,
tactic.ext1 [] {new_goals := tactic.new_goals.all},
work_on_goal 0 { dsimp at *, simp at *, assumption }, dsimp at *, simp at *,
end

/--A function `f:ℍ → ℂ` is modular, of level `Γ` and weight `k ∈ ℤ`, if for every matrix in
 `γ ∈  Γ` we have `f(γ  • z)= (c*z+d)^k f(z)` where `γ= ![![a, b], ![c, d]]`,
 and it acts on `ℍ` via Moebius trainsformations. -/
 @[simp]
lemma modular_mem' (k : ℤ) (Γ : subgroup SL2Z) (f : ℍ → ℂ) :
  f ∈ (modular_submodule k Γ) ↔  ∀ γ : Γ, ∀ z : ℍ,
  f ((γ : matrix.GL_pos (fin 2) ℝ) • z) = ((γ 1 0 )*z + γ 1 1)^k * f z :=
begin
  simp [modular_mem],
  split,
    intros h1 γ z,
    have h2:= h1 γ,
    rw ←  coe_coe at *,rw ←  coe_coe at *,
    have h3: (f ∣ₖ[k] γ) z = f z , by {simp_rw h2},
    rw ← h3,
    simp_rw slash_k,
    simp only [coe_fn_coe_base, matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe,
     matrix.general_linear_group.coe_fn_eq_coe, coe_coe],
    have h5:= upper_half_plane.denom_ne_zero (γ : GL2P) z,
    simp_rw upper_half_plane.denom at h5,
    simp only [coe_fn_coe_base, ne.def, matrix.general_linear_group.coe_fn_eq_coe, coe_coe] at h5,
    rw mul_comm,
    have ents := coe_aux Γ γ ,
    simp only [matrix.special_linear_group.coe_fn_eq_coe, coe_fn_coe_base, of_real_int_cast,
      matrix.general_linear_group.coe_fn_eq_coe, coe_coe] at ents,
    simp_rw ents at *,
    have pown := fpow_ne_zero k h5,
    have h55:= inv_mul_cancel pown,
    have aux : ∀ (a b c d : ℂ), a*(b*c)⁻¹*d= a*b⁻¹*c⁻¹*d, by { field_simp, },
    simp_rw aux,
    have aux2 : ∀ (a b c d : ℂ), a*b⁻¹*c⁻¹*d= (a*b⁻¹)*(c⁻¹*d), by {intros a b c d, ring,},
    simp_rw aux2,
    rw h55,
    simp only [mul_one],
    have hs:= det_coe_g Γ γ,
    simp only [int.cast_one, units.val_eq_coe, matrix.special_linear_group.det_coe,
      subtype.val_eq_coe, coe_coe] at hs,
    rw hs,
    simp,
  intros hf γ,
  simp_rw slash_k,
  simp only [coe_fn_coe_base, matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe,
    matrix.general_linear_group.coe_fn_eq_coe, coe_coe],
  ext1,
  have hff:= hf γ x,
  rw hff,
  have h5:= upper_half_plane.denom_ne_zero (γ : GL2P) x,
    simp_rw upper_half_plane.denom at h5,
    simp only [coe_fn_coe_base, ne.def, matrix.general_linear_group.coe_fn_eq_coe, coe_coe] at h5,
    have ents := coe_aux Γ γ ,
    simp only [matrix.special_linear_group.coe_fn_eq_coe, coe_fn_coe_base, of_real_int_cast,
     matrix.general_linear_group.coe_fn_eq_coe, coe_coe] at ents,
    simp_rw ents at *,
    have pown := fpow_ne_zero k h5,
    have h55:= inv_mul_cancel pown,
    rw mul_comm,
    have aux3 : ∀ (a b c d : ℂ), (a*b)⁻¹*(c*d)= a⁻¹*(b⁻¹*c)*d, by {field_simp,},
    simp_rw aux3,
    rw h55,
    have hs:= det_coe_g Γ γ,
    simp only [int.cast_one, units.val_eq_coe, matrix.special_linear_group.det_coe,
      subtype.val_eq_coe, coe_coe] at hs,
    rw hs,
    simp,
end

lemma mul_modular  (k_1 k_2 : ℤ) (Γ : subgroup SL2Z) (f g : ℍ → ℂ)
(hf : f ∈  modular_submodule k_1 Γ)  (hg : g ∈ modular_submodule k_2 Γ) :
f*g  ∈  modular_submodule (k_1+k_2) Γ :=

begin
simp at *,
intros γ z,
have hff:= hf γ z,
have hgg:= hg γ z,
rw [hff,hgg],
have h5:= upper_half_plane.denom_ne_zero (γ : GL2P) z,
    simp_rw upper_half_plane.denom at h5,
    simp only [coe_fn_coe_base, ne.def, matrix.general_linear_group.coe_fn_eq_coe, coe_coe] at h5,
    have ents := coe_aux Γ γ ,
    simp only [matrix.special_linear_group.coe_fn_eq_coe, coe_fn_coe_base, of_real_int_cast,
     matrix.general_linear_group.coe_fn_eq_coe, coe_coe] at ents,
    simp_rw ents at *,
    have pown := fpow_add h5 k_1 k_2,
    rw pown,
    ring,
end
open_locale direct_sum

instance gmod  (Γ : subgroup SL2Z) : direct_sum.gcomm_monoid (λ k, modular_submodule k Γ) :=
begin
have one_mem : (1 : ℍ → ℂ) ∈ modular_submodule 0 Γ, by {simp only [modular_mem',
   mul_one, forall_const, gpow_zero, implies_true_iff, eq_self_iff_true, pi.one_apply],},
apply direct_sum.gcomm_monoid.of_submodules (λ k, modular_submodule k Γ) (one_mem) ,
intros k_1 k_2 f g,
apply mul_modular k_1 k_2 Γ f g, apply f.property, apply g.property,
end


instance semiring_of_mod_forms (Γ : subgroup SL2Z): comm_semiring (⨁  k, modular_submodule k Γ)
  := infer_instance



/--The definition of the zero modular form, whose values at all points is zero-/
def zero_form : ℍ → ℂ:= (0 : (ℍ → ℂ))

/--A function ` f : ℍ → ℂ` is bounded at infinity if there exist real numbers `M,A` such that
for all `z ∈ ℍ` with `im z ≥ A` we have `abs(f (z)) ≤ M`,
 i.e. the function is bounded as you approach `i∞`.  -/
def is_bound_at_infinity := { f : ℍ → ℂ | ∃ (M A : ℝ), ∀ z : ℍ, A ≤ im z → abs (f z) ≤ M }

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
  (transf   :  f ∈ modular_submodule k Γ )
  (infinity : f ∈ is_bound_at_infinity )

lemma mk (Γ : subgroup SL2Z) (k : ℤ) (f : ℍ → ℂ)
  (h :is_holomorphic_on (hol_extn f) )
  (h2: f ∈ modular_submodule k Γ )
  (h3 : f ∈ is_bound_at_infinity ) :
  is_modular_form_of_lvl_and_weight Γ k f :={
  hol := h,
  transf := h2,
  infinity := h3,
}

lemma mod_mem (Γ : subgroup SL2Z) (k : ℤ) (f : ℍ → ℂ) : is_modular_form_of_lvl_and_weight Γ k f ↔
  is_holomorphic_on (hol_extn f) ∧
  f ∈ modular_submodule k Γ  ∧
  f ∈ is_bound_at_infinity :=
begin
  split,
  intro hf,
  simp [hf.hol, hf.transf, hf.infinity],
  intro h,
  apply mk Γ k f h.1 h.2.1 h.2.2,
end


/-- The zero modular form is a modular form-/
lemma zero_mod_form :  (is_modular_form_of_lvl_and_weight Γ   (k : ℤ) ) (zero_form ):=
{ hol :=  by {rw hol_extn, exact zero_hol ℍ', },
  transf := (modular_submodule k Γ).zero_mem',
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
  (transf   : f ∈ modular_submodule k Γ)
  (infinity : f ∈ is_zero_at_infinity )

lemma is_cuspform_mk (Γ : subgroup SL2Z) (k : ℤ) (f : ℍ → ℂ)
  (h : is_holomorphic_on (hol_extn f) )
  (h2 : f ∈ modular_submodule k Γ)
  (h3 : f ∈ is_zero_at_infinity ) :
  is_cusp_form_of_lvl_and_weight Γ k f :={
  hol := h,
  transf := h2,
  infinity := h3,
}

lemma cusp_mem (Γ : subgroup SL2Z) (k : ℤ) (f: ℍ → ℂ): is_cusp_form_of_lvl_and_weight Γ k f ↔
  is_holomorphic_on (hol_extn f) ∧
  f ∈ modular_submodule k Γ ∧
  f ∈ is_zero_at_infinity :=
begin
  split,
  intro hf,
  simp [hf.hol, hf.transf, hf.infinity],
  intro h,
  apply is_cuspform_mk Γ k f h.1 h.2.1 h.2.2,
end


/-- The zero modular form is a cusp form-/
lemma zero_cusp_form :  (is_cusp_form_of_lvl_and_weight Γ k)  (zero_form ) :=
{ hol := by {rw hol_extn, exact zero_hol ℍ', },
  transf := (modular_submodule k Γ).zero_mem',
  infinity := by {simp only [zero_at_inf_mem, gt_iff_lt, ge_iff_le],
    intros ε he,
    use (-1: ℝ ),
    intros x  h1,
    rw zero_form,
    simp [complex.abs_zero],
    linarith}
}

lemma is_modular_form_of_lvl_and_weight_of_is_cusp_form_of_lvl_and_weight  (f : ℍ → ℂ)
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
    apply (modular_submodule  k Γ).add_mem' ha.transf hb.transf,
    apply bounded_at_infty_submodule.add_mem' ha.infinity hb.infinity, },
  smul_mem' := by {intros c f hf,  simp at *,
    simp only [mod_mem, complex.abs_mul, ge_iff_le, subtype.forall, smul_sim, upper_half_plane.coe_im],
    split,
    apply smul_hol,
    simp [hf.hol],
    exact hf.hol,
    split,
    apply (modular_submodule  k Γ).smul_mem',
    apply hf.transf,
    apply bounded_at_infty_submodule.smul_mem' c hf.infinity,},

}

localized "notation `Mₖ[`k`](`Γ`)`:= space_of_mod_forms_of_level_and_weight Γ k" in modular_forms


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
    apply (modular_submodule  k Γ).add_mem' ha.transf hb.transf,
    apply zero_at_infty_submodule.add_mem' ha.infinity hb.infinity, },
  smul_mem' := by {intros c f hf,  simp at *,
    simp only [cusp_mem, complex.abs_mul, ge_iff_le, subtype.forall, smul_sim, upper_half_plane.coe_im],
    split,
    apply smul_hol,
    simp [hf.hol],
    exact hf.hol,
    split,
    apply (modular_submodule  k Γ).smul_mem',
    apply hf.transf,
    apply zero_at_infty_submodule.smul_mem' c hf.infinity,},

}

localized "notation `Sₖ[`k`](`Γ`)`:= space_of_cusp_forms_of_level_and_weight Γ k" in modular_forms

end modular_forms
