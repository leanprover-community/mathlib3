/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/

import geometry.manifold.mfderiv
import analysis.complex.upper_half_plane.functions_bounded_at_infty
import analysis.complex.upper_half_plane.topology
import number_theory.modular_forms.slash_invariant_forms

/-!
# Modular forms

This file defines modular forms and proves some basic properties about them.

We begin by defining modular forms and cusp forms as extension of `slash_invariant_forms` then we
define the space of modular forms, cusp forms and prove that the product of two modular forms is a
modular form.
-/

open complex upper_half_plane

open_locale topological_space manifold upper_half_plane

noncomputable theory

instance upper_half_plane.charted_space : charted_space ℂ ℍ :=
upper_half_plane.open_embedding_coe.singleton_charted_space

instance upper_half_plane.smooth_manifold_with_corners : smooth_manifold_with_corners 𝓘(ℂ) ℍ :=
open_embedding.singleton_smooth_manifold_with_corners 𝓘(ℂ) (upper_half_plane.open_embedding_coe)

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _

local notation `GL(` n `, ` R `)`⁺ := matrix.GL_pos (fin n) R

local notation `SL(` n `, ` R `)` := matrix.special_linear_group (fin n) R

set_option old_structure_cmd true

section modular_forms

open modular_forms

variables (F : Type*) (Γ : subgroup SL(2, ℤ)) (k : ℤ)

local notation f `∣[`:73 k:0, A `]` :72 := slash_action.map ℂ k A f

structure modular_form extends slash_invariant_form Γ k :=
(hol' : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (to_fun : ℍ → ℂ))
(bdd_at_infty' : ∀ (A : SL(2, ℤ)), is_bounded_at_im_infty (to_fun ∣[k, A]))

structure cusp_form extends slash_invariant_form Γ k :=
(hol' : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (to_fun : ℍ → ℂ))
(zero_at_infty' : ∀ (A : SL(2, ℤ)), is_zero_at_im_infty (to_fun ∣[k, A]))

class modular_form_class extends slash_invariant_form_class F Γ k :=
(hol : ∀ f : F, mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (f : ℍ → ℂ))
(bdd_at_infty : ∀ (f : F) (A : SL(2, ℤ)), is_bounded_at_im_infty (f ∣[k, A]))

class cusp_form_class extends slash_invariant_form_class F Γ k :=
(hol : ∀ f : F, mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (f : ℍ → ℂ))
(zero_at_infty : ∀ (f : F) (A : SL(2, ℤ)), is_zero_at_im_infty (f ∣[k, A]))

instance modular_form_class.modular_form : modular_form_class (modular_form Γ k) Γ k :=
{ coe := modular_form.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  slash_action_eq := modular_form.slash_action_eq',
  hol := modular_form.hol',
  bdd_at_infty := modular_form.bdd_at_infty' }

instance cusp_form_class.cusp_form : cusp_form_class (cusp_form Γ k) Γ k :=
{ coe := cusp_form.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  slash_action_eq := cusp_form.slash_action_eq',
  hol := cusp_form.hol',
  zero_at_infty := cusp_form.zero_at_infty' }

variables {F Γ k}

instance : has_coe_to_fun (modular_form Γ k) (λ _, ℍ → ℂ) := fun_like.has_coe_to_fun
instance : has_coe_to_fun (cusp_form Γ k) (λ _, ℍ → ℂ) := fun_like.has_coe_to_fun

@[simp] lemma mf_to_fun_eq_coe {f : modular_form Γ k} : f.to_fun = (f : ℍ → ℂ) := rfl
@[simp] lemma cf_to_fun_eq_coe {f : cusp_form Γ k} : f.to_fun = (f : ℍ → ℂ) := rfl

@[ext] theorem mf_ext {f g : modular_form Γ k} (h : ∀ x, f x = g x) : f = g :=
fun_like.ext f g h

@[ext] theorem cf_ext {f g : cusp_form Γ k} (h : ∀ x, f x = g x) : f = g :=
fun_like.ext f g h

protected def mf_copy (f : modular_form Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) :
  modular_form Γ k :=
{ to_fun := f',
  slash_action_eq' := h.symm ▸ f.slash_action_eq',
  hol' := h.symm ▸ f.hol',
  bdd_at_infty' := λ A, h.symm ▸ f.bdd_at_infty' A }

protected def cf_copy (f : cusp_form Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) :
  cusp_form Γ k :=
{ to_fun := f',
  slash_action_eq' := h.symm ▸ f.slash_action_eq',
  hol' := h.symm ▸ f.hol',
  zero_at_infty' := λ A, h.symm ▸ f.zero_at_infty' A }

end modular_forms

namespace modular_forms

open slash_invariant_forms

set_option old_structure_cmd true

variables {F : Type*} {Γ : subgroup SL(2, ℤ)} {k : ℤ}

instance has_add : has_add (modular_form Γ k) :=
{ add := λ f g, {to_fun := f + g,
  slash_action_eq' := (f.to_slash_invariant_form + g.to_slash_invariant_form).2,
  hol' := mdifferentiable.add _ f.hol' g.hol',
  bdd_at_infty' := λ A, begin
      rw slash_action.add_action,
      exact (bounded_at_im_infty_subalgebra ℂ).add_mem' (f.bdd_at_infty' A) (g.bdd_at_infty' A),
      end}}

instance has_zero : has_zero (modular_form Γ k) :=
{ zero := ⟨0, slash_action.mul_zero _, (λ _, mdifferentiable_at_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)),
  by {intro a,
    convert (bounded_at_im_infty_subalgebra ℂ).zero_mem',
    apply slash_action.mul_zero _ }⟩}

instance has_nsmul : has_smul ℕ (modular_form Γ k) :=
⟨ λ c f, {to_fun := (c : ℂ) • f,
    slash_action_eq' := by {intro γ, convert slash_action.smul_action k γ f (c : ℂ),
    exact ((f.slash_action_eq') γ).symm},
    hol' := mdifferentiable.const_smul _ _ f.hol',
    bdd_at_infty' := λ A, begin
      rw slash_action.smul_action,
      apply (bounded_at_im_infty_subalgebra ℂ).smul_mem (f.bdd_at_infty' A)
    end }⟩

instance has_zsmul : has_smul ℤ (modular_form Γ k) :=
⟨ λ c f, {to_fun := (c : ℂ) • f,
    slash_action_eq' := by {intro γ, convert slash_action.smul_action k γ f (c : ℂ),
    exact ((f.slash_action_eq') γ).symm},
    hol' := mdifferentiable.const_smul _ _ f.hol',
    bdd_at_infty' := λ A, begin
      rw slash_action.smul_action,
      apply (bounded_at_im_infty_subalgebra ℂ).smul_mem (f.bdd_at_infty' A)
    end }⟩

instance has_csmul : has_smul ℂ (modular_form Γ k) :=
⟨ λ c f, {to_fun := c • f,
    slash_action_eq' := by {intro γ, convert slash_action.smul_action k γ f c,
    exact ((f.slash_action_eq') γ).symm},
    hol' := mdifferentiable.const_smul _ _ f.hol',
    bdd_at_infty' := λ A, begin
      rw slash_action.smul_action,
      apply (bounded_at_im_infty_subalgebra ℂ).smul_mem (f.bdd_at_infty' A)
    end }⟩

instance has_neg : has_neg (modular_form Γ k) :=
⟨λ f, {to_fun := -f,
    slash_action_eq':= (-(f.to_slash_invariant_form)).2,
    hol' := mdifferentiable.neg _ f.hol',
    bdd_at_infty':= λ A, begin
      convert (bounded_at_im_infty_subalgebra ℂ).smul_mem (f.bdd_at_infty' A) (-1),
      simp only [_root_.neg_smul, one_smul],
      apply  modular_forms.neg_slash,
      end }⟩

instance has_sub  : has_sub (modular_form Γ k) :=
⟨λ f g, {to_fun := f - g,
  slash_action_eq' :=
    (slash_invariant_forms.has_sub.1 f.to_slash_invariant_form g.to_slash_invariant_form).2,
    hol' := mdifferentiable.sub _ f.hol' g.hol',
    bdd_at_infty' := λ A, begin
      convert (bounded_at_im_infty_subalgebra ℂ).sub_mem (f.bdd_at_infty' A) (g.bdd_at_infty' A),
      have :  (f : ℍ → ℂ) - g = f + (-g), by {funext, simp, ring,},
      have h2 := slash_action.smul_action k A g.1 (-1 : ℂ),
      simp only [_root_.neg_smul, one_smul, mf_to_fun_eq_coe] at h2,
      rw [this, slash_action.add_action k A, h2],
      refl,
    end  }⟩

instance : add_comm_group (modular_form Γ k) :=
fun_like.coe_injective.add_comm_group _ rfl (λ _ _, by {refl}) (λ _, by{refl}) (λ _ _, by {refl})
(λ _ _, by {simp, refl,}) (λ _ _, by {simp, refl})

lemma coe_zero : ((0 : (modular_form Γ k) ) : ℍ → ℂ) = (0 : ℍ → ℂ) := rfl

def coe_hom : (modular_form Γ k) →+ (ℍ → ℂ) :=
{ to_fun := λ f, f, map_zero' := coe_zero, map_add' := λ _ _, rfl }

lemma coe_hom_injective : function.injective (@coe_hom Γ k) :=
by { exact fun_like.coe_injective }

instance modular_forms.module : module ℂ (modular_form Γ k) :=
coe_hom_injective.module ℂ (coe_hom) (λ _ _, rfl)

def modular_forms.mul (k_1 k_2 : ℤ) (Γ : subgroup SL(2, ℤ)) (f : (modular_form Γ k_1))
  (g : (modular_form Γ k_2)) : (modular_form Γ (k_1 + k_2)) :=
{ to_fun := f * g,
  slash_action_eq' := by {intro A, rw slash_mul_subgroup, congr,
  apply f.slash_action_eq' A, apply g.slash_action_eq' A,},
  hol' := mdifferentiable.mul _ f.hol' g.hol',
  bdd_at_infty' := λ A, begin
  rw [slash_mul_SL2 k_1 k_2 A f g],
  exact (f.bdd_at_infty' A).mul (g.bdd_at_infty' A),
  end}

  /-- The constant function is bounded at infinity. -/
lemma const_one_form_is_bound : is_bounded_at_im_infty (1 : ℍ → ℂ):=
@asymptotics.is_O_const_const _ _ ℂ _ _ 1 _ one_ne_zero _

instance : has_one (modular_form Γ 0) :=
{one := {
  to_fun := (1 : slash_invariant_form Γ 0),
  slash_action_eq' := (1 : slash_invariant_form Γ 0).2,
  hol' := (λ (x : ℍ), mdifferentiable_at_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)),
  bdd_at_infty' := by {intro A,
  convert const_one_form_is_bound,
  apply const_one_form_is_invar A}}}

end modular_forms

namespace cusp_forms

set_option old_structure_cmd true

variables {F : Type*} {Γ : subgroup SL(2, ℤ)} {k : ℤ}

instance has_add : has_add (cusp_form Γ k) :=
{ add := λ f g, {to_fun := f + g,
  slash_action_eq' := (f.to_slash_invariant_form + g.to_slash_invariant_form).2,
  hol' :=  mdifferentiable.add _ f.hol' g.hol',
  zero_at_infty' := λ A, begin
      rw slash_action.add_action,
      exact (zero_at_im_infty_submodule ℂ).add_mem' (f.zero_at_infty' A) (g.zero_at_infty' A),
      end}}

instance has_zero : has_zero (cusp_form Γ k) :=
{ zero := ⟨0, slash_action.mul_zero _, (λ _, mdifferentiable_at_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)),
  by {intro a,
    convert (zero_at_im_infty_submodule ℂ).zero_mem',
    apply slash_action.mul_zero _ }⟩}

instance has_nsmul : has_smul ℕ (cusp_form Γ k) :=
⟨ λ c f, {to_fun := (c : ℂ) • f,
    slash_action_eq' := by {intro γ, convert slash_action.smul_action k γ f (c : ℂ),
    exact ((f.slash_action_eq') γ).symm},
    hol' := mdifferentiable.const_smul _ _ f.hol',
    zero_at_infty' := λ A, begin
      rw slash_action.smul_action,
      apply (zero_at_im_infty_submodule ℂ).smul_mem c (f.zero_at_infty' A)
    end }⟩

instance has_zsmul : has_smul ℤ (cusp_form Γ k) :=
⟨ λ c f, {to_fun := (c : ℂ) • f,
    slash_action_eq' := by {intro γ, convert slash_action.smul_action k γ f (c : ℂ),
    exact ((f.slash_action_eq') γ).symm},
    hol' := mdifferentiable.const_smul _ _ f.hol',
    zero_at_infty' := λ A, begin
      rw slash_action.smul_action,
      apply (zero_at_im_infty_submodule ℂ).smul_mem c (f.zero_at_infty' A)
    end }⟩

instance has_csmul : has_smul ℂ (cusp_form Γ k) :=
⟨ λ c f, {to_fun := c • f,
    slash_action_eq' := by {intro γ, convert slash_action.smul_action k γ f c,
    exact ((f.slash_action_eq') γ).symm},
    hol' := mdifferentiable.const_smul _ _ f.hol',
    zero_at_infty' := λ A, begin
      rw slash_action.smul_action,
      apply (zero_at_im_infty_submodule ℂ).smul_mem c (f.zero_at_infty' A)
    end }⟩

instance has_neg : has_neg (cusp_form Γ k) :=
⟨λ f, {to_fun := -f,
    slash_action_eq':= (-(f.to_slash_invariant_form)).2,
    hol' := mdifferentiable.neg _ f.hol',
    zero_at_infty':= λ A, begin
      convert (zero_at_im_infty_submodule ℂ).smul_mem (-1) (f.zero_at_infty' A),
      simp only [_root_.neg_smul, one_smul],
      apply  modular_forms.neg_slash,
      end }⟩

instance has_sub : has_sub (cusp_form Γ k) :=
⟨λ f g, {to_fun := f - g,
  slash_action_eq' :=
    (slash_invariant_forms.has_sub.1 f.to_slash_invariant_form g.to_slash_invariant_form).2,
    hol' := mdifferentiable.sub _ f.hol' g.hol',
    zero_at_infty' := λ A, begin
      convert (zero_at_im_infty_submodule ℂ).sub_mem (f.zero_at_infty' A) (g.zero_at_infty' A),
      have : (f : ℍ → ℂ) - g = f + (-g), by {funext, simp, ring,},
      have h2 := slash_action.smul_action k A g.1 (-1 : ℂ),
      simp only [_root_.neg_smul, one_smul, cf_to_fun_eq_coe] at h2,
      rw [this, slash_action.add_action k A, h2],
      refl,
    end }⟩

instance : add_comm_group (cusp_form Γ k) :=
fun_like.coe_injective.add_comm_group _ rfl (λ _ _, by {refl}) (λ _, by{refl}) (λ _ _, by {refl})
(λ _ _, by {simp, refl,}) (λ _ _, by {simp, refl})

lemma coe_zero : ((0 : (cusp_form Γ k) ) : ℍ → ℂ) = (0 : ℍ → ℂ) := rfl

def coe_hom : (cusp_form Γ k) →+ (ℍ → ℂ) :=
{ to_fun := λ f, f, map_zero' := cusp_forms.coe_zero, map_add' := λ _ _, rfl }

lemma coe_hom_injective : function.injective (@coe_hom Γ k) :=
by { exact fun_like.coe_injective }

instance : module ℂ (cusp_form Γ k) :=
coe_hom_injective.module ℂ (coe_hom) (λ _ _, rfl)

instance [cusp_form_class F Γ k] : modular_form_class F Γ k :=
{ coe := fun_like.coe,
  coe_injective' := fun_like.coe_injective',
  slash_action_eq := cusp_form_class.slash_action_eq,
  hol := cusp_form_class.hol,
  bdd_at_infty := λ _ _, filter.zero_at_filter_is_bounded_at_filter
    (cusp_form_class.zero_at_infty _ _)}

end cusp_forms
