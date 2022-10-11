/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/

import geometry.manifold.mfderiv
import analysis.complex.upper_half_plane.functions_bounded_at_infty
import number_theory.modular_forms.slash_actions

/-!
# Modular forms

This file defines modular forms and proves some basic properties about them.

We begin by defining the notion of weakly modular form from which we then we construct the vector
space of modular forms, cusp forms and prove that the product of two modular forms is a modular
form (of higher weight).
-/

open complex upper_half_plane

open_locale topological_space manifold upper_half_plane

noncomputable theory

local notation `ℍ'`:= (⟨upper_half_space , upper_half_plane_is_open⟩: topological_space.opens ℂ)

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _

local notation `GL(` n `, ` R `)`⁺ := matrix.GL_pos (fin n) R

local notation `SL(` n `, ` R `)` := matrix.special_linear_group (fin n) R

variables {Γ : subgroup SL(2, ℤ)} {k : ℤ}

namespace modular_forms

local notation f `∣[`:73 k:0, A `]`  :72 := slash_action.map ℂ k A f

lemma slash_action_eq_slash (k : ℤ) (A : Γ) (f : ℍ → ℂ) : f ∣[k, A] = slash k A f := rfl

lemma slash_action_eq_slash' (k : ℤ) (A : SL(2, ℤ)) (f : ℍ → ℂ) : f ∣[k, A] = slash k A f := rfl

/-- The space of functions that are weakly modular. -/
def weakly_modular_form (k : ℤ) (Γ : subgroup SL(2, ℤ)) : submodule ℂ (ℍ → ℂ) :=
{ carrier := { f : ℍ → ℂ | ∀ γ : Γ, (f  ∣[k, γ]) = f },
  zero_mem' := slash_action.mul_zero _,
  add_mem' := λ f g hf hg γ, by rw [slash_action.add_action, hf, hg],
  smul_mem' := λ c f hf γ, by rw [slash_action.smul_action, hf] }

lemma weakly_modular_mem (k : ℤ) (Γ : subgroup SL(2, ℤ)) (f : ℍ → ℂ) :
  f ∈ weakly_modular_form k Γ ↔ ∀ γ : Γ, f ∣[k, γ] = f := iff.rfl

lemma slash_mul (k1 k2 : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) :
  (f * g) ∣[k1 + k2, A] = (((↑ₘ A).det) : ℝ) • (f ∣[k1, A]) * (g ∣[k2, A]) :=
begin
  ext1,
  simp only [slash_action.map, slash, matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe,
    pi.mul_apply, pi.smul_apply, algebra.smul_mul_assoc, real_smul],
  set d : ℂ := ↑((↑ₘ A).det : ℝ),
  have h1 : d ^ (k1 + k2 - 1) = d * d ^ (k1 - 1) * d ^ (k2 - 1),
  { have : d ≠ 0,
    { dsimp [d],
      norm_cast,
      exact matrix.GL_pos.det_ne_zero A },
    rw [← zpow_one_add₀ this, ← zpow_add₀ this],
    ring_exp },
  have h22 : denom A x ^ (- (k1 + k2)) = denom A x ^ (- k1) * denom A x ^ (- k2),
  { rw [int.neg_add, zpow_add₀],
    exact upper_half_plane.denom_ne_zero A x, },
  rw [h1, h22],
  ring,
end

lemma slash_mul_SL2 (k1 k2 : ℤ) (A : SL(2, ℤ)) (f g : ℍ → ℂ) :
  (f * g) ∣[k1 + k2, A] = (f ∣[k1, A]) * (g ∣[k2, A]) :=
calc (f * g) ∣[k1 + k2, (A : GL(2, ℝ)⁺)] = _ • (f ∣[k1, A]) * (g ∣[k2, A]) : slash_mul _ _ _ _ _
... = (1:ℝ) • (f ∣[k1, A]) * (g ∣[k2, A]) : by simp [-matrix.special_linear_group.coe_matrix_coe]
... = (f ∣[k1, A]) * (g ∣[k2, A]) : by simp

lemma slash_mul_subgroup (k1 k2 : ℤ) (Γ : subgroup SL(2, ℤ)) (A : Γ) (f g : ℍ → ℂ) :
  (f * g) ∣[k1 + k2, A] = (f ∣[k1, A]) * (g ∣[k2, A]) :=
begin
  have : (((↑ₘ(A : GL(2,ℝ)⁺)).det) : ℝ) = 1,
  by { simp only [coe_coe,matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
    matrix.special_linear_group.det_coe], },
  have t1 := slash_mul k1 k2 A f g,
  rw this at t1,
  simp only [coe_coe, one_smul] at t1,
  convert t1,
end

/-- A function `f : ℍ → ℂ` is weakly modular, of weight `k ∈ ℤ` and level `Γ`, if for every matrix .
 `γ ∈ Γ` we have `f(γ • z)= (c*z+d)^k f(z)` where `γ= ![![a, b], ![c, d]]`, and it acts on `ℍ`
  via Möbius transformations. -/
lemma weakly_modular_mem' (k : ℤ) (Γ : subgroup SL(2, ℤ)) (f : ℍ → ℂ) :
  f ∈ weakly_modular_form k Γ ↔ ∀ γ : Γ, ∀ z : ℍ,
  f (γ • z) = ((↑ₘγ 1 0 : ℝ) * z +(↑ₘγ 1 1 : ℝ))^k * f z :=
begin
  simp only [weakly_modular_mem, function.funext_iff, slash_action_eq_slash, slash],
  refine forall₂_congr _,
  intros γ z,
  convert inv_mul_eq_iff_eq_mul₀ _ using 2,
  { rw mul_comm,
    simp [-matrix.special_linear_group.coe_matrix_coe] },
  { exact zpow_ne_zero _ (denom_ne_zero _ _) },
end

lemma mul_modular (k_1 k_2 : ℤ) (Γ : subgroup SL(2, ℤ)) (f g : ℍ → ℂ)
  (hf : f ∈ weakly_modular_form k_1 Γ) (hg : g ∈ weakly_modular_form k_2 Γ) :
  f * g ∈ weakly_modular_form (k_1 + k_2) Γ :=
begin
  simp only [weakly_modular_mem', pi.mul_apply, coe_coe] at *,
  intros γ z,
  rw [(hf γ z), (hg γ z)],
  have pown := zpow_add₀ (upper_half_plane.denom_ne_zero (γ : GL(2, ℝ)⁺) z) k_1 k_2,
  simp only [upper_half_plane.denom, coe_fn_coe_base, ne.def,
    matrix.general_linear_group.coe_fn_eq_coe, coe_coe] at pown,
  rw pown,
  ring,
end

/-- A function `f : ℍ → ℂ` is a modular form weight `k ∈ ℤ` and of level `Γ` if it is holomorphic,
 weakly modular and bounded at infinity. -/
structure is_modular_form (k : ℤ) (Γ : subgroup SL(2, ℤ)) (f : ℍ → ℂ) : Prop :=
(hol : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (↑f : ℍ' → ℂ))
(transf : f ∈ weakly_modular_form k Γ)
(infinity : ∀ (A : SL(2, ℤ)), is_bounded_at_im_infty (f ∣[k, A]))

/-- A function `f : ℍ → ℂ` is a cusp form of weight `k ∈ ℤ` and of level `Γ` if it is holomorphic,
 weakly modular, and zero at infinity. -/
structure is_cusp_form (k : ℤ) (Γ : subgroup SL(2, ℤ)) (f : ℍ → ℂ) : Prop :=
(hol : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (↑f : ℍ' → ℂ))
(transf : f ∈ weakly_modular_form k Γ)
(infinity : ∀ (A : SL(2, ℤ)), is_zero_at_im_infty (f ∣[k, A]))

lemma is_modular_form_of_is_cusp_form {f : ℍ → ℂ}
  (h : is_cusp_form k Γ f) : is_modular_form k Γ f :=
{ hol := h.hol,
  transf := h.transf,
  infinity := λ (A : SL(2, ℤ)), filter.zero_at_filter_is_bounded_at_filter (h.infinity A)}

/-- This is the space of cuspforms of weigth `k` and level `Γ` -/
def space_of_cusp_forms_of_weight_and_level (k : ℤ) (Γ : subgroup SL(2, ℤ)) :
  submodule ℂ (ℍ → ℂ) :=
{ carrier := is_cusp_form k Γ,
  zero_mem' := { hol := (λ _, mdifferentiable_at_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)),
    transf := (weakly_modular_form k Γ).zero_mem',
    infinity :=  λ  A, begin
    rw slash_action.mul_zero,
    apply (zero_at_im_infty_submodule ℂ).zero_mem
    end},
  add_mem' := λ a b ha hb,
    { hol := mdifferentiable.add _ ha.hol hb.hol,
      transf := (weakly_modular_form k Γ).add_mem' ha.transf hb.transf,
      infinity := λ A, begin
      rw slash_action.add_action,
      apply ((zero_at_im_infty_submodule ℂ).add_mem' (ha.infinity A) (hb.infinity A))
    end},
  smul_mem' :=λ c f hf,
    { hol :=  mdifferentiable.const_smul _ _ hf.hol,
      transf := (weakly_modular_form k Γ).smul_mem' _ hf.transf,
      infinity := λ A, begin
      rw slash_action.smul_action,
      apply (zero_at_im_infty_submodule ℂ).smul_mem' c (hf.infinity A),
    end}}

localized "notation `S`:= space_of_cusp_forms_of_weight_and_level" in modular_forms

/-- This is the space of modular forms of weight `k` and level `Γ`-/
def space_of_mod_forms_of_weight_and_level (k : ℤ) (Γ : subgroup SL(2, ℤ)) : submodule ℂ (ℍ → ℂ) :=
{ carrier := { f : ℍ → ℂ | is_modular_form k Γ f },
  zero_mem':= is_modular_form_of_is_cusp_form (S k Γ).zero_mem',
  add_mem' := λ  a b ha hb,
    { hol := mdifferentiable.add _ ha.hol hb.hol,
      transf :=  (weakly_modular_form k Γ).add_mem' ha.transf hb.transf,
      infinity := λ  A, begin
      rw slash_action.add_action,
      exact (bounded_at_im_infty_subalgebra ℂ).add_mem' (ha.infinity A) (hb.infinity A)
      end},
  smul_mem' := λ c f hf,
    { hol := mdifferentiable.const_smul _ _ hf.hol,
      transf := (weakly_modular_form k Γ).smul_mem' _ hf.transf,
      infinity := λ A, begin
      rw slash_action.smul_action,
      apply (bounded_at_im_infty_subalgebra ℂ).smul_mem (hf.infinity A)
    end } }

localized "notation `M`:= space_of_mod_forms_of_weight_and_level " in modular_forms

/--The product of two modular forms is a modular form whose weight is the sum of the weights-/
lemma mul_modform (k_1 k_2 : ℤ) (Γ : subgroup SL(2, ℤ)) (f g : ℍ → ℂ)
  (hf : f ∈ M k_1 Γ) (hg : g ∈ M k_2 Γ) : f * g ∈ (M (k_1 + k_2) Γ) :=
{ hol := mdifferentiable.mul _ hf.hol hg.hol,
  transf := mul_modular _ _ _ _ _ hf.transf hg.transf,
  infinity := λ A, begin
  rw [slash_mul_SL2 k_1 k_2 A f g],
  exact (hf.infinity A).mul (hg.infinity A),
  end}

/-! Constant functions are modular forms of weight 0. -/
section const_mod_form

/-- The constant function is bounded at infinity. -/
lemma const_one_form_is_bound : is_bounded_at_im_infty (1 : ℍ → ℂ):=
@asymptotics.is_O_const_const _ _ ℂ _ _ 1 _ one_ne_zero _

/-- The constant function 1 is invariant under any subgroup of `SL(2, ℤ)`. -/
lemma const_one_form_is_invar (A : SL(2, ℤ)) : (1 : ℍ → ℂ) ∣[(0 : ℤ), A] = (1 : ℍ → ℂ) :=
begin
  rw [slash_action_eq_slash'],
  have : (((↑ₘ(A : GL(2,ℝ)⁺)).det) : ℝ) = 1,
  { simp only [coe_coe,
      matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
      matrix.special_linear_group.det_coe], },
  funext,
  rw [slash, zero_sub, this],
  simp,
end

/-- The constant function 1 is modular of weight 0. -/
lemma const_mod_form : (1 : ℍ → ℂ) ∈ M 0 Γ :=
{ hol :=  (λ (x : ℍ'), mdifferentiable_at_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)),
  transf := (λ (γ : ↥Γ), const_one_form_is_invar ((subgroup.subtype Γ) γ)),
  infinity := λ  A, by {rw const_one_form_is_invar A, exact const_one_form_is_bound }}

end const_mod_form

end modular_forms
