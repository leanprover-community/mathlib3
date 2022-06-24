/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
import algebra.module.submodule.basic
import analysis.complex.upper_half_plane.basic
import linear_algebra.general_linear_group
import linear_algebra.special_linear_group
import algebra.direct_sum.ring
import number_theory.modular
import geometry.manifold.mfderiv
import analysis.complex.upper_half_plane.functions_bounded_at_inf
import number_theory.modular_forms.slash_actions

/-!
# Modular forms

This file defines modular forms and proves some basic properties about them.

We begin by defining the `slash` operator on the space of functions `ℍ → ℂ` and from this
define the notion of weakly modular form.

Finally we construct the vector space of modular forms and prove that the product of two
modular forms is a modular form (of higher weight).
-/

universes u v

open complex upper_half_plane

open_locale topological_space manifold upper_half_plane

noncomputable theory

local notation `ℍ'` := (⟨upper_half_plane.upper_half_space ,
 upper_half_plane.upper_half_plane_is_open⟩: topological_space.opens ℂ)

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _

local notation `GL(` n `, ` R `)`⁺ := matrix.GL_pos (fin n) R

local notation `SL(` n `, ` R `)` := matrix.special_linear_group (fin n) R

variables (Γ : subgroup SL(2,ℤ)) (k : ℤ)

namespace modular_forms

local notation f `∣[`:73 k:0, A `]`  :72 := slash_action.map ℂ k A f

@[simp]
lemma slash_action_eq_slash (k : ℤ) (A : Γ) (f : ℍ → ℂ) : f ∣[k, A] = slash k A f := by {refl}

@[simp]
lemma slash_action_eq_slash' (k : ℤ) (A : SL(2, ℤ)) (f : ℍ → ℂ) : f ∣[k, A] = slash k A f :=
by {refl}

/--The space of functions that are modular-/
def weakly_modular_submodule (k : ℤ) (Γ : subgroup SL(2,ℤ)) : submodule ℂ (ℍ → ℂ) :=
  {carrier := { f : (ℍ → ℂ) | ∀ (γ : Γ), (f  ∣[k, γ]) = f },
  zero_mem' := by {apply slash_action.mul_zero },
  add_mem' := by {  intros f g hf hg γ,
    rw [slash_action.add_action k γ f g, hf γ, hg γ], },
  smul_mem' := by { intros c f hf γ,
    have : (c • f) ∣[k, γ] = c • (f ∣[k, γ]), by {apply slash_action.smul_action},
    rw (hf γ) at this,
    apply this,} }

lemma wmodular_mem (k : ℤ) (Γ : subgroup SL(2,ℤ)) (f : ℍ → ℂ) :
  f ∈ (weakly_modular_submodule k Γ) ↔ ∀ (γ : Γ), (f ∣[k, γ]) = f := iff.rfl

lemma slash_mul (k1 k2 : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) :
  (f * g) ∣[k1+k2, A] = (((↑ₘ A).det) : ℝ) • (f ∣[k1, A]) * (g ∣[k2, A]) :=
begin
  ext1,
  simp only [slash_action.map, slash, matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe,
   ←mul_assoc],
  have h1 : ((((↑ₘ A).det) : ℝ)^(k1 + k2 - 1) : ℂ) =
  (((↑ₘ A).det) : ℝ) * (((↑ₘ A).det) : ℝ)^(k1 - 1) * (((↑ₘ A).det) : ℝ)^(k2 - 1),
  by {simp only [mul_assoc, matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe, coe_coe],
  rw [←zpow_add₀, ←zpow_one_add₀],
  ring_exp,
  all_goals { norm_cast, apply (matrix.GL_pos.det_ne_zero A), }, },
  have h22 : (upper_half_plane.denom A x)^(-(k1+k2)) = (upper_half_plane.denom A x)^(-k1) *
    (upper_half_plane.denom A x)^(-k2),
  by { rw [int.neg_add, zpow_add₀], exact upper_half_plane.denom_ne_zero A x, },
  rw [h1, h22],
  simp only [upper_half_plane.denom, pi.mul_apply, coe_coe, zpow_neg, algebra.smul_mul_assoc,
    pi.smul_apply, real_smul],
  ring,
end

lemma slash_mul_SL2 (k1 k2 : ℤ) (A : SL(2,ℤ)) (f g : ℍ → ℂ) :
  (f * g) ∣[k1 + k2, A] = (f ∣[k1, A]) * (g ∣[k2, A]) :=
begin
  have : (((↑ₘ(A : GL(2,ℝ)⁺)).det) : ℝ) = 1,
  { simp only [coe_coe,matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
    matrix.special_linear_group.det_coe], },
  have hs := slash_mul k1 k2 A f g,
  simp_rw [this, one_smul] at hs,
  convert hs,
end

lemma slash_mul_subgroup (k1 k2 : ℤ) (Γ : subgroup SL(2,ℤ)) (A : Γ) (f g : ℍ → ℂ) :
  (f * g) ∣[k1+k2, A] = (f ∣[k1, A]) * (g ∣[k2, A]) :=
begin
  have : (((↑ₘ(A : GL(2,ℝ)⁺)).det) : ℝ) = 1,
  by { simp only [coe_coe,matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
    matrix.special_linear_group.det_coe], },
  have t1 := slash_mul k1 k2 A f g,
  rw this at t1,
  simp only [coe_coe, one_smul] at t1,
  convert t1,
end

/--A function `f : ℍ → ℂ` is modular, of weight `k ∈ ℤ` and level `Γ`, if for every matrix in
 `γ ∈ Γ` we have `f(γ • z)= (c*z+d)^k f(z)` where `γ= ![![a, b], ![c, d]]`,
 and it acts on `ℍ` via Moebius trainsformations. -/
lemma wmodular_mem' (k : ℤ) (Γ : subgroup SL(2,ℤ)) (f : ℍ → ℂ) :
  f ∈ (weakly_modular_submodule k Γ) ↔ ∀ γ : Γ, ∀ z : ℍ,
  f (γ • z) = ((↑ₘγ 1 0 : ℝ) * z +(↑ₘγ 1 1 : ℝ))^k * f z :=
begin
  simp only [wmodular_mem],
  split,
  { intros h1 γ z,
  have h3 : (f ∣[k, γ]) z = f z , by {simp_rw (h1 γ)},
  rw [←h3, mul_comm],
  simp only [slash_action_eq_slash, slash],
  have h55 := zpow_neg_mul_zpow_self k (upper_half_plane.denom_ne_zero (γ : GL(2, ℝ)⁺) z),
  simp only [upper_half_plane.denom, upper_half_plane.subgroup_to_sl_moeb, upper_half_plane.sl_moeb,
    coe_coe, matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
    matrix.special_linear_group.coe_matrix_coe, int.coe_cast_ring_hom, matrix.map_apply,
    of_real_int_cast] at *,
  rw [mul_assoc, h55, ←int.coe_cast_ring_hom, ←matrix.special_linear_group.coe_matrix_coe,
    matrix.special_linear_group.det_coe ((γ : SL(2, ℤ)) : SL(2, ℝ))],
  simp only [of_real_one, one_zpow, mul_one], },
  { intros hf γ,
  simp_rw [slash_action_eq_slash, slash],
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

/-- A function `f : ℍ → ℂ` is a modular form weight `k ∈ ℤ` and of level `Γ` if it is holomorphic,
 weakly modular and bounded at infinity -/
structure is_modular_form_of_weight_and_level (k : ℤ) (Γ : subgroup SL(2,ℤ)) (f : ℍ → ℂ) : Prop :=
  (hol : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (↑f : ℍ' → ℂ))
  (transf : f ∈ weakly_modular_submodule k Γ)
  (infinity : ∀ (A : SL(2,ℤ)), is_bound_at_inf (f ∣[k, A]))

/-- A function `f : ℍ → ℂ` is a cusp form of weight `k ∈ ℤ` and of level `Γ` if it is holomorphic,
 weakly modular, and zero at infinity -/
structure is_cusp_form_of_weight_and_level (k : ℤ) (Γ : subgroup SL(2,ℤ)) (f : ℍ → ℂ) : Prop :=
  (hol : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (↑f : ℍ' → ℂ))
  (transf : f ∈ weakly_modular_submodule k Γ)
  (infinity : ∀ (A : SL(2,ℤ)), is_zero_at_inf (f ∣[k, A]))

/-- The zero modular form is a cusp form-/
lemma zero_cusp_form : is_cusp_form_of_weight_and_level k Γ 0 :=
{ hol := by {apply mdifferentiable_zero,},
  transf := (weakly_modular_submodule k Γ).zero_mem',
  infinity := by { intro A,
    convert zero_form_is_zero_at_inf,
    apply slash_action.mul_zero, } }

lemma is_modular_form_of_weight_and_level_of_is_cusp_form_of_weight_and_level {f : ℍ → ℂ}
  (h : is_cusp_form_of_weight_and_level k Γ f) : is_modular_form_of_weight_and_level k Γ f :=
{ hol := h.1,
  transf := h.2,
  infinity := λ (A : SL(2,ℤ)), is_zero_at_inf_is_bound _ (h.3 A), }

 /-- The zero modular form is a modular form-/
lemma zero_mod_form : is_modular_form_of_weight_and_level k Γ 0 :=
begin
  apply_rules [is_modular_form_of_weight_and_level_of_is_cusp_form_of_weight_and_level,
    zero_cusp_form],
end

/-- This is the space of modular forms of weight `k` and level `Γ`-/
def space_of_mod_forms_of_weight_and_level (k : ℤ) (Γ : subgroup SL(2,ℤ)) : submodule ℂ (ℍ → ℂ) :=
{ carrier := { f : ℍ → ℂ | is_modular_form_of_weight_and_level k Γ f},
  zero_mem':= by { simp only [set.mem_set_of_eq], apply zero_mod_form, },
  add_mem' := by { intros a b ha hb,
    split,
    exact mdifferentiable_add ha.hol hb.hol,
    exact (weakly_modular_submodule k Γ).add_mem' ha.transf hb.transf,
    intro A,
    rw slash_action.add_action,
    exact (bounded_at_infty_submodule.add_mem' (ha.infinity A) (hb.infinity A)) },
  smul_mem' := by { intros c f hf,
    split,
    exact mdifferentiable_smul _ hf.hol,
    exact (weakly_modular_submodule k Γ).smul_mem' _ hf.transf,
    intro A,
    rw slash_action.smul_action,
    apply (bounded_at_infty_submodule.smul_mem' c (hf.infinity A)), }, }

localized "notation `M`:= space_of_mod_forms_of_weight_and_level " in modular_forms

/-- This is the space of cuspforms of weigth `k` and level `Γ` -/
def space_of_cusp_forms_of_weight_and_level (k : ℤ) (Γ : subgroup SL(2,ℤ)) : submodule ℂ (ℍ → ℂ) :=
{ carrier := is_cusp_form_of_weight_and_level k Γ,
  zero_mem' := by apply zero_cusp_form,
  add_mem' := by { intros a b ha hb,
    split,
    exact mdifferentiable_add ha.hol hb.hol,
    exact (weakly_modular_submodule k Γ).add_mem' ha.transf hb.transf,
    intro A,
    rw slash_action.add_action,
    apply (zero_at_infty_submodule.add_mem' (ha.infinity A) (hb.infinity A)) },
  smul_mem' := by { intros c f hf, split,
    exact mdifferentiable_smul _ hf.hol,
    exact (weakly_modular_submodule k Γ).smul_mem' _ hf.transf,
    intro A,
    rw slash_action.smul_action,
    apply zero_at_infty_submodule.smul_mem' c (hf.infinity A), }, }

localized "notation `S`:= space_of_cusp_forms_of_weight_and_level" in modular_forms

/--The product of two modular forms is a modular form whose weight is the sum of the weights-/
lemma mul_modform (k_1 k_2 : ℤ) (Γ : subgroup SL(2,ℤ)) (f g : ℍ → ℂ)
  (hf : f ∈ M k_1 Γ) (hg : g ∈ M k_2 Γ) : f * g ∈ (M (k_1 + k_2) Γ) :=
begin
  refine ⟨mdifferentiable_mul hf.1 hg.1, mul_modular _ _ _ _ _ hf.2 hg.2, _⟩,
  intro A,
  rw [slash_mul_SL2 k_1 k_2 A f g],
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
lemma const_one_form_is_invar (A : SL(2,ℤ)) : const_one_form ∣[(0 : ℤ), A] = const_one_form :=
begin
  rw [slash_action_eq_slash', slash, const_one_form],
  dsimp only,
  have : (((↑ₘ(A : GL(2,ℝ)⁺)).det) : ℝ) = 1,
  { simp only [coe_coe,
      matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
      matrix.special_linear_group.det_coe], },
  rw [zero_sub, this],
  simp only [pi.one_apply, of_real_one, one_zpow, mul_one, neg_zero', zpow_zero],
  refl,
end

/-- The constant function 1 is modular of weight 0 -/
lemma const_mod_form : const_one_form ∈ M 0 Γ :=
{ hol := by { simp_rw const_one_form, apply mdifferentiable_one, },
  transf := by { intro γ, apply const_one_form_is_invar, },
  infinity := by { intro A, rw const_one_form_is_invar A, exact const_one_form_is_bound,} }

end const_mod_form

end modular_forms
