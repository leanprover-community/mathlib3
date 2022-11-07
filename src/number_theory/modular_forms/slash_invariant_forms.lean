/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
import analysis.complex.upper_half_plane.basic
import number_theory.modular_forms.slash_actions


/-!
# Slash invariant forms

This file defines funtions that are invariant under a `slash_action` which forms the basis for
defining `modular_form` and `cusp_form`. We prove several instances for such spaces, in particular
that they form a module.
-/

open complex upper_half_plane

open_locale upper_half_plane

noncomputable theory

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _

local notation `GL(` n `, ` R `)`⁺ := matrix.GL_pos (fin n) R

local notation `SL(` n `, ` R `)` := matrix.special_linear_group (fin n) R

section slash_invariant_forms

set_option old_structure_cmd true

open modular_forms

variables (F : Type*) (Γ : subgroup SL(2, ℤ)) (k : ℤ)

localized "notation f `∣[`:73 k:0, A `]` :72 := slash_action.map ℂ k A f" in slash_invariant_forms

structure slash_invariant_form :=
(to_fun : ℍ → ℂ)
(slash_action_eq' : ∀ γ : Γ, to_fun ∣[k, γ] = to_fun)

class slash_invariant_form_class extends fun_like F ℍ (λ _, ℂ) :=
(slash_action_eq : ∀ (f : F) (γ : Γ), f ∣[k, γ] = f)

instance slash_invariant_form_class.slash_invariant_form :
   slash_invariant_form_class (slash_invariant_form Γ k) Γ k :=
{ coe := (slash_invariant_form.to_fun),
  coe_injective' := λ f g h, by cases f; cases g; congr',
  slash_action_eq := slash_invariant_form.slash_action_eq' }

variables {F Γ k}

instance : has_coe_to_fun (slash_invariant_form Γ k) (λ _, ℍ → ℂ) := fun_like.has_coe_to_fun

@[simp] lemma sif_to_fun_eq_coe {f : slash_invariant_form Γ k} : f.to_fun = (f : ℍ → ℂ) := rfl

@[ext] theorem sif_ext {f g : slash_invariant_form Γ k} (h : ∀ x, f x = g x) : f = g :=
fun_like.ext f g h

protected def sif_copy (f : slash_invariant_form Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) :
  slash_invariant_form Γ k :=
{ to_fun := f',
  slash_action_eq' := h.symm ▸ f.slash_action_eq',}

end slash_invariant_forms

namespace slash_invariant_forms

open slash_invariant_forms

variables {F : Type*} {Γ : subgroup SL(2, ℤ)} {k : ℤ}

instance slash_invariant_form_class.coe_to_fun [slash_invariant_form_class F Γ k] :
  has_coe_to_fun F (λ _, ℍ → ℂ) := fun_like.has_coe_to_fun

@[simp] lemma slash_action_eqn [slash_invariant_form_class F Γ k] (f : F) (γ : Γ) :
   slash_action.map ℂ k γ ⇑f = ⇑f := slash_invariant_form_class.slash_action_eq f γ

lemma slash_action_eqn' (k : ℤ) (Γ : subgroup SL(2, ℤ)) [slash_invariant_form_class F Γ k] (f : F) :
∀ γ : Γ, ∀ z : ℍ, f (γ • z) = ((↑ₘγ 1 0 : ℝ) * z +(↑ₘγ 1 1 : ℝ))^k * f z :=
begin
  intros γ z,
  rw ←modular_forms.slash_action_eq'_iff,
  simp,
end

instance [slash_invariant_form_class F Γ k] : has_coe_t F (slash_invariant_form Γ k) :=
⟨λ f, { to_fun := f, slash_action_eq' := slash_action_eqn f }⟩

@[simp] lemma slash_invariant_form_class.coe_coe [slash_invariant_form_class F Γ k] (f : F) :
  ((f : (slash_invariant_form Γ k)) : ℍ → ℂ) = f := rfl

instance has_add : has_add (slash_invariant_form Γ k) :=
⟨λ f g , ⟨ f + g, by {intro γ, convert slash_action.add_action k γ f g,
   exact ((f.slash_action_eq') γ).symm, exact ((g.slash_action_eq') γ).symm} ⟩⟩

instance has_zero : has_zero (slash_invariant_form Γ k) :=
{zero := ⟨ 0 , slash_action.mul_zero _⟩}

instance has_nsmul : has_smul ℕ (slash_invariant_form Γ k) :=
⟨ λ c f, {to_fun := (c : ℂ) • f,
    slash_action_eq' := by {intro γ, convert slash_action.smul_action k γ f (c : ℂ),
    exact ((f.slash_action_eq') γ).symm}}⟩

instance has_zsmul : has_smul ℤ (slash_invariant_form Γ k) :=
⟨ λ c f, {to_fun := (c : ℂ) • f,
    slash_action_eq' := by {intro γ, convert slash_action.smul_action k γ f (c : ℂ),
    exact ((f.slash_action_eq') γ).symm}}⟩

instance has_csmul : has_smul ℂ (slash_invariant_form Γ k) :=
⟨ λ c f, {to_fun := c • f,
    slash_action_eq' := by {intro γ, convert slash_action.smul_action k γ f c,
    exact ((f.slash_action_eq') γ).symm}}⟩

instance has_neg : has_neg (slash_invariant_form Γ k) :=
⟨λ f, ⟨ -f,
  begin intro g,
  have := ((f.slash_action_eq') g),
  rw modular_forms.subgroup_slash at *,
  rw modular_forms.neg_slash,
  simp only [neg_inj],
  convert this
  end⟩ ⟩

instance has_sub : has_sub (slash_invariant_form Γ k) :=
⟨λ f g, ⟨f - g, by { intro γ,
  have : (f : ℍ → ℂ) - g = f + (-g), by {funext, simp, ring,},
  rw [this, slash_action.add_action k γ],
  simp [(f.slash_action_eq') γ],
  rw modular_forms.neg_slash,
  simp only [neg_inj],
  convert ((g.slash_action_eq') γ),} ⟩⟩

instance : add_comm_group (slash_invariant_form Γ k) :=
fun_like.coe_injective.add_comm_group _ rfl (λ _ _, by {refl}) (λ _, by{refl}) (λ _ _, by {refl})
(λ _ _, by {simp, refl,}) (λ _ _, by {simp, refl})

lemma coe_zero : ((0 : (slash_invariant_form Γ k) ) : ℍ → ℂ) = (0 : ℍ → ℂ) := rfl

def coe_hom : (slash_invariant_form Γ k) →+ (ℍ → ℂ) :=
{ to_fun := λ f, f, map_zero' := slash_invariant_forms.coe_zero, map_add' := λ _ _, rfl }

lemma coe_hom_injective : function.injective (@coe_hom Γ k) :=
fun_like.coe_injective

instance : module ℂ (slash_invariant_form Γ k) :=
coe_hom_injective.module ℂ (coe_hom) (λ _ _, rfl)

instance : has_one (slash_invariant_form Γ 0) :=
{one := {to_fun := 1, slash_action_eq' := by {intro A,
  convert modular_forms.const_one_form_is_invar A}}}

end slash_invariant_forms
