/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
import algebra.module.submodule.basic
import analysis.complex.upper_half_plane
import linear_algebra.general_linear_group
import linear_algebra.special_linear_group
import algebra.direct_sum.ring
import number_theory.modular
import geometry.manifold.mfderiv

/-!
# Modular forms

This file defines modular forms and proves some basic properties about them.

We begin by defining the `slash_k` operator on the space of functions `ℍ → ℂ` and from this
define the notion of weakly modular form.#check

We then define `bounded_at_infinity` and `zero_at_infinity`. Finally we construct the vector
space of modular forms and prove that the product of two modular forms is a modular form
(of higher weight).
-/

universes u v

open complex

open_locale topological_space manifold upper_half_plane

noncomputable theory

local notation `ℍ'`:=(⟨upper_half_plane.upper_half_space ,
 upper_half_plane.upper_half_plane_is_open⟩: topological_space.opens ℂ)

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _

local notation `GL(` n `, ` R `)`⁺:= matrix.GL_pos (fin n) R

local notation `SL(` n `, ` R `)`:= matrix.special_linear_group (fin n) R

variable (M : GL(2, ℝ)⁺)

/--The weight `k` action of `GL(2, ℝ)⁺` on functions `f : ℍ → ℂ`. -/
def slash_k : ℤ → GL(2, ℝ)⁺ → (ℍ → ℂ) → (ℍ → ℂ) := λ k γ f,
  (λ (x : ℍ), f (γ • x) * (((↑ₘ γ).det) : ℝ)^(k-1) * (upper_half_plane.denom γ x)^(-k))

namespace modular_forms

variables (Γ : subgroup SL(2,ℤ)) (k: ℤ) (f : (ℍ → ℂ))

localized "notation f ` ∣[`:100 k `]`:0 γ :100 := slash_k k γ f" in modular_form

lemma slash_k_right_action (k : ℤ) (A B : GL(2, ℝ)⁺) (f : ℍ → ℂ) :
  (f ∣[k] A) ∣[k] B = f ∣[k] (A * B) :=
begin
  ext1,
  simp_rw [slash_k,(upper_half_plane.denom_cocycle A B x)],
  have e3 : (A * B) • x = A • B • x , by { convert (upper_half_plane.mul_smul' A B x), } ,
  rw e3,
  simp only [upper_half_plane.num, upper_half_plane.denom, of_real_mul, subgroup.coe_mul, coe_coe,
    upper_half_plane.coe_smul, units.coe_mul, matrix.mul_eq_mul, matrix.det_mul,
    upper_half_plane.smul_aux, upper_half_plane.smul_aux', subtype.coe_mk] at *,
  field_simp,
  ring_nf,
  have : (((↑(↑A : GL (fin 2) ℝ) : (matrix (fin 2) (fin 2) ℝ)).det : ℂ) *
    ((↑(↑B : GL (fin 2) ℝ) : (matrix (fin 2) (fin 2) ℝ)).det : ℂ))^(k-1) =
    ((↑(↑B : GL (fin 2) ℝ) : (matrix (fin 2) (fin 2) ℝ)).det : ℂ)^(k-1) *
    ((↑(↑A : GL (fin 2) ℝ) : (matrix (fin 2) (fin 2) ℝ)).det : ℂ)^(k-1) ,
    by {simp_rw [←mul_zpow, mul_comm]},
  simp_rw [this, ← mul_assoc, ←mul_zpow],
  end

lemma slash_k_add (k : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) :
  (f + g) ∣[k] A = (f ∣[k] A) + (g ∣[k] A) :=
begin
  simp only [slash_k, pi.add_apply, matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe,
    coe_coe],
  ext1,
  simp only [pi.add_apply],
  ring,
end

lemma slash_k_mul_one (k : ℤ) (f : ℍ → ℂ) : (f ∣[k] 1) = f :=
begin
 simp_rw slash_k,
 ext1,
 simp,
end

lemma smul_slash_k (k : ℤ) (A : GL(2, ℝ)⁺) (f : ℍ → ℂ) (c : ℂ) : (c • f) ∣[k] A = c • (f ∣[k] A):=
begin
  ext1,
  simp_rw slash_k,
  simp only [slash_k, algebra.id.smul_eq_mul, matrix.general_linear_group.coe_det_apply,
    pi.smul_apply, subtype.val_eq_coe, coe_coe],
  ring,
end

lemma slash_k_mul (k1 k2 : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) :
  (f * g) ∣[k1+k2] A = (((↑ₘ A).det) : ℝ) • (f ∣[k1] A) * (g ∣[k2] A) :=
begin
  ext1,
  simp only [slash_k, matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe, ←mul_assoc],
  have h1 : ((((↑ₘ A).det) : ℝ)^(k1 + k2 - 1) : ℂ) =
  (((↑ₘ A).det) : ℝ) * (((↑ₘ A).det) : ℝ)^(k1 - 1) * (((↑ₘ A).det) : ℝ)^(k2 - 1),
  by {simp only [mul_assoc, matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe, coe_coe],
  rw [←zpow_add₀, ←zpow_one_add₀],
  ring_exp,
  all_goals { norm_cast, apply (matrix.GL_pos.det_ne_zero A), }, },
  have h22 : (upper_half_plane.denom A x)^(-(k1+k2)) = (upper_half_plane.denom A x)^(-k1) *
    (upper_half_plane.denom A x)^(-k2),
  by { rw [int.neg_add, zpow_add₀], exact upper_half_plane.denom_ne_zero A x, },
  rw [h1,h22],
  simp only [upper_half_plane.denom, pi.mul_apply, coe_coe, zpow_neg, algebra.smul_mul_assoc,
    pi.smul_apply, real_smul],
  ring,
end

lemma slash_k_mul_SL2 (k1 k2 : ℤ) (A : SL(2,ℤ)) (f g : ℍ → ℂ) :
  (f * g) ∣[k1 + k2] A = (f ∣[k1] A) * (g ∣[k2] A) :=
begin
  have : (((↑ₘ(A : GL(2,ℝ)⁺)).det): ℝ) = 1,
  { simp only [coe_coe,matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
    matrix.special_linear_group.det_coe], },
  simp_rw [slash_k_mul, this, one_smul],
end

/--The space of functions that are modular-/
def weakly_modular_submodule (k : ℤ) (Γ : subgroup SL(2,ℤ)) : submodule ℂ (ℍ → ℂ) :=
  {carrier := { f : (ℍ → ℂ) | ∀ (γ : Γ), (f ∣[k] (γ : GL(2, ℝ)⁺)) = f },
  zero_mem' := by { simp only [slash_k, set.mem_set_of_eq, pi.zero_apply, zero_mul, forall_const],
    refl, },
  add_mem' := by { intros f g hf hg γ,
    rw [slash_k_add k γ f g, hf γ, hg γ], },
  smul_mem' := by { intros c f hf γ,
    have : (c • f) ∣[k] γ = c • (f ∣[k] γ), by {apply smul_slash_k},
    rw (hf γ) at this,
    apply this,} }

lemma wmodular_mem (k : ℤ) (Γ : subgroup SL(2,ℤ)) (f : ℍ → ℂ) :
  f ∈ (weakly_modular_submodule k Γ) ↔ ∀ (γ : Γ), (f ∣[k] (γ : GL(2, ℝ)⁺)) = f := iff.rfl

lemma slash_k_mul_subgroup (k1 k2 : ℤ) (Γ : subgroup SL(2,ℤ)) (A : Γ) (f g : ℍ → ℂ) :
  (f * g) ∣[k1+k2] A = (f ∣[k1] A) * (g ∣[k2] A) :=
begin
  have : (((↑ₘ(A : GL(2,ℝ)⁺)).det): ℝ) = 1,
  by { simp only [coe_coe,matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
    matrix.special_linear_group.det_coe], },
  simp_rw [slash_k_mul, this, one_smul],
end

/--A function `f : ℍ → ℂ` is modular, of level `Γ` and weight `k ∈ ℤ`, if for every matrix in
 `γ ∈ Γ` we have `f(γ • z)= (c*z+d)^k f(z)` where `γ= ![![a, b], ![c, d]]`,
 and it acts on `ℍ` via Moebius trainsformations. -/
@[simp]
lemma wmodular_mem' (k : ℤ) (Γ : subgroup SL(2,ℤ)) (f : ℍ → ℂ) :
  f ∈ (weakly_modular_submodule k Γ) ↔ ∀ γ : Γ, ∀ z : ℍ,
  f (γ • z) = ((↑ₘγ 1 0 : ℝ) * z +(↑ₘγ 1 1 : ℝ))^k * f z :=
begin
  simp only [wmodular_mem],
  split,
  { intros h1 γ z,
  have h3 : (f ∣[k] γ) z = f z , by {simp_rw (h1 γ)},
  rw [←h3, slash_k, mul_comm],
  have h55 := zpow_neg_mul_zpow_self k (upper_half_plane.denom_ne_zero (γ : GL(2, ℝ)⁺) z),
  simp only [upper_half_plane.denom, upper_half_plane.subgroup_to_sl_moeb, upper_half_plane.sl_moeb,
    coe_coe, matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
    matrix.special_linear_group.coe_matrix_coe, int.coe_cast_ring_hom, matrix.map_apply,
    of_real_int_cast] at *,
  rw [mul_assoc, h55, ←int.coe_cast_ring_hom, ←matrix.special_linear_group.coe_matrix_coe,
    matrix.special_linear_group.det_coe ((γ : SL(2, ℤ)) : SL(2, ℝ))],
  simp only [of_real_one, one_zpow, mul_one], },
  { intros hf γ,
  simp_rw slash_k,
  ext1,
  rw [←upper_half_plane.subgroup_moeb, (hf γ x), mul_comm],
  have h55 := zpow_neg_mul_zpow_self k (upper_half_plane.denom_ne_zero (γ : GL(2, ℝ)⁺) x),
  simp_rw upper_half_plane.denom at *,
  simp only [matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix, coe_coe,
    matrix.special_linear_group.coe_matrix_coe, int.coe_cast_ring_hom, matrix.map_apply,
    of_real_int_cast] at h55,
  simp only [coe_coe, matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
    matrix.map_apply, of_real_int_cast],
  rw (matrix.special_linear_group.det_coe ((γ : SL(2, ℤ)) : SL(2, ℝ))),
  simp only [matrix.special_linear_group.coe_matrix_coe, int.coe_cast_ring_hom, matrix.map_apply,
    of_real_int_cast, of_real_one, one_zpow, mul_one],
  simp_rw [← mul_assoc, h55],
  simp },
end

lemma mul_modular (k_1 k_2 : ℤ) (Γ : subgroup SL(2,ℤ)) (f g : ℍ → ℂ)
  (hf : f ∈ weakly_modular_submodule k_1 Γ) (hg : g ∈ weakly_modular_submodule k_2 Γ) :
  f * g ∈ weakly_modular_submodule (k_1 + k_2) Γ :=
begin
  simp only [wmodular_mem', pi.mul_apply, coe_coe] at *,
  intros γ z,
  rw [(hf γ z), (hg γ z)],
  have pown := zpow_add₀ (upper_half_plane.denom_ne_zero (γ : GL(2, ℝ)⁺) z) k_1 k_2,
  simp only [upper_half_plane.denom, coe_fn_coe_base, ne.def,
    matrix.general_linear_group.coe_fn_eq_coe, coe_coe] at pown,
  rw pown,
  ring,
end

/--Fileter for approaching `i∞`-/
def at_I_inf := filter.at_top.comap upper_half_plane.im

lemma at_I_inf_mem (S : set ℍ) : S ∈ at_I_inf ↔ (∃ A : ℝ, ∀ z : ℍ, A ≤ im z → z ∈ S) :=
begin
  simp only [at_I_inf, filter.mem_comap', filter.mem_at_top_sets, ge_iff_le, set.mem_set_of_eq,
    upper_half_plane.coe_im],
  split,
  { intro h, cases h with a h, refine ⟨a, (λ z hz, by {apply h (im z) hz , refl})⟩ },
  { refine (λ h, by {cases h with A h,
    refine ⟨A, (λ b hb x hx, by {apply (h x), rw hx, exact hb})⟩}) }
end

/--A function ` f : ℍ → ℂ` is bounded at infinity if there exist real numbers `M,A` such that
for all `z ∈ ℍ` with `im z ≥ A` we have `abs(f (z)) ≤ M`,
 i.e. the function is bounded as you approach `i∞`. -/
def is_bound_at_inf (f : ℍ → ℂ) : Prop := asymptotics.is_O at_I_inf f (1 : ℍ → ℂ)

/--A function ` f : ℍ → ℂ` is zero at infinity if for any `ε > 0` there exist a real
number `A` such that for all `z ∈ ℍ` with `im z ≥ A` we have `abs(f (z)) ≤ ε`,
 i.e. the function tends to zero as you approach `i∞`. -/
def is_zero_at_inf (f : ℍ → ℂ) : Prop := filter.tendsto f at_I_inf (𝓝 0)

lemma zero_form_is_zero_at_inf : is_zero_at_inf 0 := tendsto_const_nhds

lemma is_zero_at_inf_is_bound (f : ℍ → ℂ) (hf : is_zero_at_inf f) : is_bound_at_inf f :=
begin
  apply asymptotics.is_O_of_div_tendsto_nhds, { simp, }, { convert hf, ext1, simp, }
end

lemma zero_form_is_bound : is_bound_at_inf 0 :=
  is_zero_at_inf_is_bound _ zero_form_is_zero_at_inf

/--Module of funcitons that are zero at infinity.-/
def zero_at_infty_submodule : submodule ℂ (ℍ → ℂ) :=
{ carrier := is_zero_at_inf,
  zero_mem' := zero_form_is_zero_at_inf,
  add_mem' := by { intros a b ha hb, simpa using ha.add hb },
  smul_mem' := by { intros c f hf, simpa using hf.const_mul c }, }

/--Module of funcitons that are bounded at infinity.-/
def bounded_at_infty_submodule : submodule ℂ (ℍ → ℂ) :=
{ carrier := is_bound_at_inf,
  zero_mem' := zero_form_is_bound,
  add_mem' := by { intros f g hf hg, simpa using hf.add hg, },
  smul_mem' := by { intros c f hf, simpa using hf.const_mul_left c }, }

lemma prod_of_bound_is_bound {f g : ℍ → ℂ} (hf : is_bound_at_inf f) (hg : is_bound_at_inf g) :
  is_bound_at_inf (f * g) := by simpa using hf.mul hg

@[simp]lemma bound_mem (f : ℍ → ℂ) :
  is_bound_at_inf f ↔ ∃ (M A : ℝ), ∀ z : ℍ, A ≤ im z → abs (f z) ≤ M :=
begin
  simp [is_bound_at_inf, asymptotics.is_O_iff, filter.eventually, at_I_inf_mem],
end

/-- A function `f : ℍ → ℂ` is a modular form of level `Γ` and weight `k ∈ ℤ` if it is holomorphic,
 weakly modular and bounded at infinity -/
structure is_modular_form_of_weight_and_level (k : ℤ) (Γ : subgroup SL(2,ℤ)) (f : ℍ → ℂ) : Prop :=
  (hol : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (↑f : ℍ' → ℂ))
  (transf : f ∈ weakly_modular_submodule k Γ)
  (infinity : ∀ (A : SL(2,ℤ)), is_bound_at_inf (f ∣[k] A))

/-- A function `f : ℍ → ℂ` is a cusp form of level one and weight `k ∈ ℤ` if it is holomorphic,
 weakly modular, and zero at infinity -/
structure is_cusp_form_of_lvl_and_weight (k : ℤ) (Γ : subgroup SL(2,ℤ)) (f : ℍ → ℂ) : Prop :=
  (hol : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (↑f : ℍ' → ℂ))
  (transf : f ∈ weakly_modular_submodule k Γ)
  (infinity : ∀ (A : SL(2,ℤ)), is_zero_at_inf (f ∣[k] A))

/-- The zero modular form is a cusp form-/
lemma zero_cusp_form : is_cusp_form_of_lvl_and_weight k Γ 0 :=
{ hol := by {apply mdifferentiable_zero,},
  transf := (weakly_modular_submodule k Γ).zero_mem',
  infinity := by { intro A,
    convert zero_form_is_zero_at_inf,
    rw slash_k,
    simp only [pi.zero_apply, zero_mul],
    refl, } }

lemma is_modular_form_of_weight_and_level_of_is_cusp_form_of_lvl_and_weight (f : ℍ → ℂ)
  (h : is_cusp_form_of_lvl_and_weight k Γ f) : is_modular_form_of_weight_and_level k Γ f :=
{ hol := h.1,
  transf := h.2,
  infinity := λ (A : SL(2,ℤ)), is_zero_at_inf_is_bound _ (h.3 A), }

 /-- The zero modular form is a modular form-/
lemma zero_mod_form : is_modular_form_of_weight_and_level k Γ 0 :=
begin
  apply_rules [is_modular_form_of_weight_and_level_of_is_cusp_form_of_lvl_and_weight,
    zero_cusp_form],
end

/-- This is the space of modular forms of weight `k` and level `Γ`-/
def space_of_mod_forms_of_weight_and_level (k : ℤ) (Γ : subgroup SL(2,ℤ)) : submodule ℂ (ℍ → ℂ) :=
{ carrier := { f : ℍ → ℂ | is_modular_form_of_weight_and_level k Γ f},
  zero_mem':= by { simp only [set.mem_set_of_eq], apply zero_mod_form, },
  add_mem' := by
  { intros a b ha hb, split,
    exact mdifferentiable_add _ _ ha.hol hb.hol,
    exact (weakly_modular_submodule k Γ).add_mem' ha.transf hb.transf,
    intro A, rw slash_k_add,
    exact (bounded_at_infty_submodule.add_mem' (ha.infinity A) (hb.infinity A)) },
  smul_mem' := by
  { intros c f hf,
    split,
    exact mdifferentiable_smul _ _ hf.hol,
    exact (weakly_modular_submodule k Γ).smul_mem' _ hf.transf,
    intro A,
    rw smul_slash_k,
    apply (bounded_at_infty_submodule.smul_mem' c (hf.infinity A)), }, }

localized "notation `M(`k`, `Γ`)`:= space_of_mod_forms_of_weight_and_level k Γ" in modular_forms

/-- This is the space of cuspforms of weigth `k` and level `Γ` -/
def space_of_cusp_forms_of_weight_and_level (k : ℤ) (Γ : subgroup SL(2,ℤ)) : submodule ℂ (ℍ → ℂ) :=
{ carrier := is_cusp_form_of_lvl_and_weight k Γ,
  zero_mem' := by apply zero_cusp_form,
  add_mem' := by
  { intros a b ha hb, split,
    exact mdifferentiable_add _ _ ha.hol hb.hol,
    exact (weakly_modular_submodule k Γ).add_mem' ha.transf hb.transf,
    intro A, rw slash_k_add,
    apply (zero_at_infty_submodule.add_mem' (ha.infinity A) (hb.infinity A)) },
  smul_mem' := by
  { intros c f hf, split,
    exact mdifferentiable_smul _ _ hf.hol,
    exact (weakly_modular_submodule k Γ).smul_mem' _ hf.transf,
    intro A,
    rw smul_slash_k,
    apply zero_at_infty_submodule.smul_mem' c (hf.infinity A), }, }

localized "notation `S(`k`, `Γ`)`:= space_of_cusp_forms_of_weight_and_level k Γ" in modular_forms

/--The product of two modular forms is a modular form whose weight is the sum of the weights-/
lemma mul_modform (k_1 k_2 : ℤ) (Γ : subgroup SL(2,ℤ)) (f g : ℍ → ℂ)
  (hf : f ∈ M(k_1, Γ)) (hg : g ∈ M(k_2, Γ)) : f * g ∈ M(k_1 + k_2, Γ) :=
begin
  refine ⟨mdifferentiable_mul _ _ hf.1 hg.1, mul_modular _ _ _ _ _ hf.2 hg.2, _⟩,
  intro A,
  rw slash_k_mul_SL2 k_1 k_2 A f g,
  exact prod_of_bound_is_bound (hf.infinity A) (hg.infinity A),
end

/-! Constant functions are modular forms of weight 0 -/
section const_mod_form

/--A modular form of weight zero-/
def const_one_form : ℍ → ℂ := 1

/-- The constant function is bounded at infinity -/
lemma const_one_form_is_bound : is_bound_at_inf const_one_form :=
  @asymptotics.is_O_const_const _ _ ℂ _ _ 1 _ one_ne_zero _

/-- The constant function 1 is invariant under any subgroup of SL2Z -/
lemma const_one_form_is_invar (A : SL(2,ℤ)) : const_one_form ∣[0] A = const_one_form :=
begin
  rw [slash_k, const_one_form],
  dsimp only,
  have : (((↑ₘ(A : GL(2,ℝ)⁺)).det): ℝ) = 1,
  { simp only [coe_coe,
      matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
      matrix.special_linear_group.det_coe],},
  rw [zero_sub, this],
  simp only [pi.one_apply, of_real_one, one_zpow, mul_one, neg_zero', zpow_zero],
  refl,
end

/-- The constant function 1 is modular of weight 0 -/
lemma const_mod_form : const_one_form ∈ M(0, Γ) :=
{ hol := by { simp_rw const_one_form, apply mdifferentiable_one, },
  transf := by { intro γ, apply const_one_form_is_invar, },
  infinity := by { intro A, rw const_one_form_is_invar A, exact const_one_form_is_bound,} }

end const_mod_form

end modular_forms
