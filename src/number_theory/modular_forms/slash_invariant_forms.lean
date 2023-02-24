/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import number_theory.modular_forms.slash_actions

/-!
# Slash invariant forms

This file defines functions that are invariant under a `slash_action` which forms the basis for
defining `modular_form` and `cusp_form`. We prove several instances for such spaces, in particular
that they form a module.
-/

open complex upper_half_plane

open_locale upper_half_plane

noncomputable theory

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _

-- like `↑ₘ`, but allows the user to specify the ring `R`. Useful to help Lean elaborate.
local notation `↑ₘ[` R `]` := @coe _ (matrix (fin 2) (fin 2) R) _

local notation `GL(` n `, ` R `)`⁺ := matrix.GL_pos (fin n) R

local notation `SL(` n `, ` R `)` := matrix.special_linear_group (fin n) R

section slash_invariant_forms

set_option old_structure_cmd true

open modular_form

variables (F : Type*) (Γ : out_param $ subgroup SL(2, ℤ)) (k : out_param ℤ)

localized "notation f `∣[`:73 k:0, A `]` :72 := slash_action.map ℂ k A f" in slash_invariant_forms

/--Functions `ℍ → ℂ` that are invariant under the `slash_action`. -/
structure slash_invariant_form :=
(to_fun : ℍ → ℂ)
(slash_action_eq' : ∀ γ : Γ, to_fun ∣[k, γ] = to_fun)

/--`slash_invariant_form_class F Γ k` asserts `F` is a type of bundled functions that are invariant
under the `slash_action`. -/
class slash_invariant_form_class extends fun_like F ℍ (λ _, ℂ) :=
(slash_action_eq : ∀ (f : F) (γ : Γ), (f : ℍ → ℂ) ∣[k, γ] = f)

attribute [nolint dangerous_instance] slash_invariant_form_class.to_fun_like

@[priority 100]
instance slash_invariant_form_class.slash_invariant_form :
   slash_invariant_form_class (slash_invariant_form Γ k) Γ k :=
{ coe := slash_invariant_form.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  slash_action_eq := slash_invariant_form.slash_action_eq' }

variables {F Γ k}

instance : has_coe_to_fun (slash_invariant_form Γ k) (λ _, ℍ → ℂ) := fun_like.has_coe_to_fun

@[simp] lemma slash_invariant_form_to_fun_eq_coe {f : slash_invariant_form Γ k} :
  f.to_fun = (f : ℍ → ℂ) := rfl

@[ext] theorem slash_invariant_form_ext {f g : slash_invariant_form Γ k} (h : ∀ x, f x = g x) :
  f = g := fun_like.ext f g h

/-- Copy of a `slash_invariant_form` with a new `to_fun` equal to the old one.
Useful to fix definitional equalities. -/
protected def slash_invariant_form.copy (f : slash_invariant_form Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) :
  slash_invariant_form Γ k :=
{ to_fun := f',
  slash_action_eq' := h.symm ▸ f.slash_action_eq',}

end slash_invariant_forms

namespace slash_invariant_form

open slash_invariant_form

variables {F : Type*} {Γ : out_param $ subgroup SL(2, ℤ)} {k : out_param ℤ}

@[priority 100, nolint dangerous_instance]
instance slash_invariant_form_class.coe_to_fun [slash_invariant_form_class F Γ k] :
  has_coe_to_fun F (λ _, ℍ → ℂ) := fun_like.has_coe_to_fun

@[simp] lemma slash_action_eqn [slash_invariant_form_class F Γ k] (f : F) (γ : Γ) :
   slash_action.map ℂ k γ ⇑f = ⇑f := slash_invariant_form_class.slash_action_eq f γ

lemma slash_action_eqn' (k : ℤ) (Γ : subgroup SL(2, ℤ)) [slash_invariant_form_class F Γ k] (f : F)
  (γ : Γ) (z : ℍ) : f (γ • z) = ((↑ₘ[ℤ]γ 1 0 : ℂ) * z +(↑ₘ[ℤ]γ 1 1 : ℂ))^k * f z :=
begin
  rw ←modular_form.slash_action_eq'_iff,
  simp,
end

instance [slash_invariant_form_class F Γ k] : has_coe_t F (slash_invariant_form Γ k) :=
⟨λ f, { to_fun := f, slash_action_eq' := slash_action_eqn f }⟩

@[simp] lemma slash_invariant_form_class.coe_coe [slash_invariant_form_class F Γ k] (f : F) :
  ((f : slash_invariant_form Γ k) : ℍ → ℂ) = f := rfl

instance has_add : has_add (slash_invariant_form Γ k) :=
⟨ λ f g,
  { to_fun := f + g,
    slash_action_eq' := λ γ, by convert slash_action.add_action k γ (f : ℍ → ℂ) g; simp } ⟩

@[simp] lemma coe_add (f g : slash_invariant_form Γ k) : ⇑(f + g) = f + g := rfl
@[simp] lemma add_apply (f g : slash_invariant_form Γ k) (z : ℍ) : (f + g) z = f z + g z := rfl

instance has_zero : has_zero (slash_invariant_form Γ k) :=
⟨ { to_fun := 0,
    slash_action_eq' := slash_action.zero_slash _} ⟩

@[simp] lemma coe_zero : ⇑(0 : slash_invariant_form Γ k) = (0 : ℍ → ℂ) := rfl

section
variables {α : Type*} [has_smul α ℂ] [is_scalar_tower α ℂ ℂ]

instance has_smul : has_smul α (slash_invariant_form Γ k) :=
⟨ λ c f,
  { to_fun := c • f,
    slash_action_eq' := λ γ, by rw [←smul_one_smul ℂ c ⇑f, slash_action.smul_action k γ ⇑f,
                                    slash_action_eqn] }⟩

@[simp] lemma coe_smul (f : slash_invariant_form Γ k) (n : α) : ⇑(n • f) = n • f := rfl
@[simp] lemma smul_apply (f : slash_invariant_form Γ k) (n : α) (z : ℍ) :
  (n • f) z = n • (f z) := rfl

end

instance has_neg : has_neg (slash_invariant_form Γ k) :=
⟨ λ f,
  { to_fun := -f,
    slash_action_eq' := λ γ, by simpa [modular_form.subgroup_slash,
      modular_form.neg_slash] using f.slash_action_eq' γ } ⟩

@[simp] lemma coe_neg (f : slash_invariant_form Γ k) : ⇑(-f) = -f := rfl
@[simp] lemma neg_apply (f : slash_invariant_form Γ k) (z : ℍ) : (-f) z = - (f z) := rfl

instance has_sub : has_sub (slash_invariant_form Γ k) := ⟨ λ f g, f + -g ⟩

@[simp] lemma coe_sub (f g : slash_invariant_form Γ k) : ⇑(f - g) = f - g := rfl
@[simp] lemma sub_apply (f g : slash_invariant_form Γ k) (z : ℍ) : (f - g) z = f z - g z := rfl

instance : add_comm_group (slash_invariant_form Γ k) :=
fun_like.coe_injective.add_comm_group _ rfl coe_add coe_neg coe_sub coe_smul coe_smul

/--Additive coercion from `slash_invariant_form` to `ℍ → ℂ`.-/
def coe_hom : slash_invariant_form Γ k →+ (ℍ → ℂ) :=
{ to_fun := λ f, f,
  map_zero' := rfl,
  map_add' := λ _ _, rfl }

lemma coe_hom_injective : function.injective (@coe_hom Γ k) :=
fun_like.coe_injective

instance : module ℂ (slash_invariant_form Γ k) :=
coe_hom_injective.module ℂ coe_hom (λ _ _, rfl)

instance : has_one (slash_invariant_form Γ 0) :=
⟨ { to_fun := 1,
    slash_action_eq' := λ A, modular_form.is_invariant_one A } ⟩

@[simp] lemma one_coe_eq_one : ((1 : slash_invariant_form Γ 0) : ℍ → ℂ) = 1 := rfl

instance : inhabited (slash_invariant_form Γ k) := ⟨0⟩

end slash_invariant_form
