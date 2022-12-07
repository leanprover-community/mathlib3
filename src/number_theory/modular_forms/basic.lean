/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import geometry.manifold.mfderiv
import analysis.complex.upper_half_plane.functions_bounded_at_infty
import analysis.complex.upper_half_plane.topology
import number_theory.modular_forms.slash_invariant_forms
import ring_theory.graded_algebra.basic
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
upper_half_plane.open_embedding_coe.singleton_smooth_manifold_with_corners 𝓘(ℂ)

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _

local notation `GL(` n `, ` R `)`⁺ := matrix.GL_pos (fin n) R

local notation `SL(` n `, ` R `)` := matrix.special_linear_group (fin n) R

section modular_form

open modular_form

variables (F : Type*) (Γ : subgroup SL(2, ℤ)) (k : ℤ)

local notation f `∣[`:73 k:0, A `]` :72 := slash_action.map ℂ k A f

set_option old_structure_cmd true

/--These are `slash_invariant_form`'s that are holomophic and bounded at infinity. -/
structure modular_form extends slash_invariant_form Γ k :=
(hol' : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (to_fun : ℍ → ℂ))
(bdd_at_infty' : ∀ (A : SL(2, ℤ)), is_bounded_at_im_infty (to_fun ∣[k, A]))

/-- The `slash_invariant_form` associated to a `modular_form`. -/
add_decl_doc modular_form.to_slash_invariant_form

/--These are `slash_invariant_form`s that are holomophic and zero at infinity. -/
structure cusp_form extends slash_invariant_form Γ k :=
(hol' : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (to_fun : ℍ → ℂ))
(zero_at_infty' : ∀ (A : SL(2, ℤ)), is_zero_at_im_infty (to_fun ∣[k, A]))

/-- The `slash_invariant_form` associated to a `cusp_form`. -/
add_decl_doc cusp_form.to_slash_invariant_form

/--`modular_form_class F Γ k` says that `F` is a type of bundled functions that extend
`slash_invariant_forms_class` by requiring that the functions be holomorphic and bounded
at infinity. -/
class modular_form_class extends slash_invariant_form_class F Γ k :=
(hol : ∀ f : F, mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (f : ℍ → ℂ))
(bdd_at_infty : ∀ (f : F) (A : SL(2, ℤ)), is_bounded_at_im_infty (f ∣[k, A]))

/--`cusp_form_class F Γ k` says that `F` is a type of bundled functions that extend
`slash_invariant_forms_class` by requiring that the functions be holomorphic and zero
at infinity. -/
class cusp_form_class extends slash_invariant_form_class F Γ k :=
(hol : ∀ f : F, mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (f : ℍ → ℂ))
(zero_at_infty : ∀ (f : F) (A : SL(2, ℤ)), is_zero_at_im_infty (f ∣[k, A]))

@[priority 100]
instance modular_form_class.modular_form : modular_form_class (modular_form Γ k) Γ k :=
{ coe := modular_form.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  slash_action_eq := modular_form.slash_action_eq',
  hol := modular_form.hol',
  bdd_at_infty := modular_form.bdd_at_infty' }

@[priority 100]
instance cusp_form_class.cusp_form : cusp_form_class (cusp_form Γ k) Γ k :=
{ coe := cusp_form.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  slash_action_eq := cusp_form.slash_action_eq',
  hol := cusp_form.hol',
  zero_at_infty := cusp_form.zero_at_infty' }

variables {F Γ k}

@[simp] lemma modular_form_to_fun_eq_coe {f : modular_form Γ k} : f.to_fun = (f : ℍ → ℂ) := rfl
@[simp] lemma cusp_form_to_fun_eq_coe {f : cusp_form Γ k} : f.to_fun = (f : ℍ → ℂ) := rfl

@[ext] theorem modular_form.ext {f g : modular_form Γ k} (h : ∀ x, f x = g x) : f = g :=
fun_like.ext f g h

@[ext] theorem cusp_form.ext {f g : cusp_form Γ k} (h : ∀ x, f x = g x) : f = g :=
fun_like.ext f g h

/-- Copy of a `modular_form` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def modular_form.copy (f : modular_form Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) :
  modular_form Γ k :=
{ to_fun := f',
  slash_action_eq' := h.symm ▸ f.slash_action_eq',
  hol' := h.symm ▸ f.hol',
  bdd_at_infty' := λ A, h.symm ▸ f.bdd_at_infty' A }

/-- Copy of a `cusp_form` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def cusp_form.copy (f : cusp_form Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) :
  cusp_form Γ k :=
{ to_fun := f',
  slash_action_eq' := h.symm ▸ f.slash_action_eq',
  hol' := h.symm ▸ f.hol',
  zero_at_infty' := λ A, h.symm ▸ f.zero_at_infty' A }

end modular_form

namespace modular_form

open slash_invariant_form

variables {F : Type*} {Γ : subgroup SL(2, ℤ)} {k : ℤ}

instance has_add : has_add (modular_form Γ k) :=
{ add := λ f g,
  { hol' := f.hol'.add g.hol',
    bdd_at_infty' := λ A, by simpa using (f.bdd_at_infty' A).add (g.bdd_at_infty' A),
    .. (f : slash_invariant_form Γ k) + g } }

@[simp] lemma coe_add (f g : modular_form Γ k) : ⇑(f + g) = f + g := rfl

@[simp] lemma add_apply (f g : modular_form Γ k) (z : ℍ) : (f + g) z = f z + g z := rfl

instance has_zero : has_zero (modular_form Γ k) :=
⟨{ to_fun := 0,
  slash_action_eq' := slash_action.mul_zero _,
  hol' := (λ _, mdifferentiable_at_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)),
  bdd_at_infty' := λ A, by simpa [slash_action.mul_zero _ ]
    using (bounded_at_im_infty_subalgebra ℂ).zero_mem' }⟩

section
variables {α : Type*} [has_smul α ℂ] [is_scalar_tower α ℂ ℂ]

instance has_smul : has_smul α (modular_form Γ k) :=
⟨ λ c f,
  { to_fun := c • f,
    hol' := by simpa using f.hol'.const_smul (c • (1 : ℂ)),
    bdd_at_infty' := λ A, by simpa using (f.bdd_at_infty' A).const_smul_left (c • (1 : ℂ)),
     .. c • (f : slash_invariant_form Γ k)}⟩

@[simp] lemma coe_smul (f : (modular_form Γ k)) (n : α) : ⇑(n • f) = n • f := rfl
@[simp] lemma smul_apply (f : (modular_form Γ k)) (n : α) (z : ℍ) :
   (n • f) z = n • (f z) := rfl
end

instance has_neg : has_neg (modular_form Γ k) :=
⟨λ f,
  { to_fun := -f,
    hol' := f.hol'.neg,
    bdd_at_infty':= λ A, by simpa [-asymptotics.is_O_neg_left] using ((f.bdd_at_infty' A).neg_left),
    .. -(f : slash_invariant_form Γ k) }⟩

@[simp] lemma coe_neg (f : modular_form Γ k) : ⇑(-f) = -f := rfl

@[simp] lemma neg_apply (f : modular_form Γ k) (z : ℍ) : (-f) z = - (f z) := rfl

instance has_sub : has_sub (modular_form Γ k) :=
⟨ λ f g, f + -g ⟩

@[simp] lemma coe_sub (f g : (modular_form Γ k)) : ⇑(f - g) = f - g := rfl

@[simp] lemma sub_apply (f g : modular_form Γ k) (z : ℍ) : (f - g) z = f z - g z := rfl

instance : add_comm_group (modular_form Γ k) :=
fun_like.coe_injective.add_comm_group _ rfl coe_add coe_neg coe_sub coe_smul coe_smul

@[simp]lemma coe_zero : ⇑(0 : modular_form Γ k) = (0 : ℍ → ℂ) := rfl

/--Additive coercion from `modular_form` to `ℍ → ℂ`. -/
def coe_hom : (modular_form Γ k) →+ (ℍ → ℂ) :=
{ to_fun := λ f, f,
  map_zero' := coe_zero,
  map_add' := λ _ _, rfl }

lemma coe_hom_injective : function.injective (@coe_hom Γ k) :=
fun_like.coe_injective

instance : module ℂ (modular_form Γ k) :=
coe_hom_injective.module ℂ (coe_hom) (λ _ _, rfl)

instance : inhabited (modular_form Γ k) := ⟨0⟩

/--The modular form of weight `k_1 + k_2` given by the product of two modular forms of weights
`k_1` and `k_2`. -/
def mul {k_1 k_2 : ℤ} {Γ : subgroup SL(2, ℤ)} (f : (modular_form Γ k_1))
  (g : (modular_form Γ k_2)) : (modular_form Γ (k_1 + k_2)) :=
{ to_fun := f * g,
  slash_action_eq' := λ A, by simp_rw [mul_slash_subgroup, modular_form_class.slash_action_eq],
  hol' := f.hol'.mul g.hol',
  bdd_at_infty' := λ A, begin
    rw [mul_slash_SL2],
    exact (f.bdd_at_infty' A).mul (g.bdd_at_infty' A),
  end}

  /-- The constant function is bounded at infinity. -/
lemma is_bounded_at_im_infty_one : is_bounded_at_im_infty (1 : ℍ → ℂ):=
@asymptotics.is_O_const_const _ _ ℂ _ _ 1 _ one_ne_zero _

instance : has_one (modular_form Γ 0) :=
{ one :=
    { hol' := λ x, mdifferentiable_at_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ),
    bdd_at_infty' := λ A, (congr_arg is_bounded_at_im_infty (is_invariant_one A)).mpr
      is_bounded_at_im_infty_one,
    .. (1 : slash_invariant_form Γ 0) } }

@[simp] lemma one_coe_eq_one : ((1 : modular_form Γ 0) : ℍ → ℂ) = 1 := rfl

@[simp] lemma mul_coe {k_1 k_2 : ℤ} {Γ : subgroup SL(2, ℤ)} (f : (modular_form Γ k_1))
  (g : (modular_form Γ k_2)) : ((f.mul g) : ℍ → ℂ) = f * g := rfl

end modular_form

namespace cusp_form

variables {F : Type*} {Γ : subgroup SL(2, ℤ)} {k : ℤ}

instance has_add : has_add (cusp_form Γ k) :=
{ add := λ f g,
  { to_fun := f + g,
    hol' := f.hol'.add g.hol',
    zero_at_infty' := λ A, by simpa using (zero_at_im_infty_submodule ℂ).add_mem'
      (f.zero_at_infty' A) (g.zero_at_infty' A),
    .. (f : slash_invariant_form Γ k) + g }}

@[simp] lemma coe_add (f g : cusp_form Γ k) : ⇑(f + g) = f + g := rfl

@[simp] lemma add_apply (f g : cusp_form Γ k) (z : ℍ) : (f + g) z = f z + g z := rfl

instance has_zero : has_zero (cusp_form Γ k) :=
⟨ { to_fun := 0,
    slash_action_eq' := slash_action.mul_zero _,
    hol' := (λ _, mdifferentiable_at_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)),
    zero_at_infty' := λ A, by simpa [slash_action.mul_zero _ ]
      using filter.zero_is_zero_at_filter _, }⟩

section
variables {α : Type*} [has_smul α ℂ] [is_scalar_tower α ℂ ℂ]

instance has_smul : has_smul α (cusp_form Γ k) :=
⟨ λ c f,
  { to_fun := c • f,
    hol' := by simpa using f.hol'.const_smul (c • (1 : ℂ)),
    zero_at_infty' := λ A, by simpa using
      ((zero_at_im_infty_submodule ℂ).smul_mem (c • (1 : ℂ)) (f.zero_at_infty' A)),
     .. c • (f : slash_invariant_form Γ k) }⟩

@[simp] lemma coe_smul (f : (cusp_form Γ k)) (n : α) : ⇑(n • f) = n • f := rfl
@[simp] lemma smul_apply (f : (cusp_form Γ k)) (n : α) {z : ℍ} :
   (n • f) z = n • (f z) := rfl

end

instance has_neg : has_neg (cusp_form Γ k) :=
⟨λ f,
  { to_fun := -f,
    hol' := f.hol'.neg,
    zero_at_infty':= λ A, by simpa [-neg_mem_iff] using
      (zero_at_im_infty_submodule ℂ).smul_mem (-1) (f.zero_at_infty' A),
     .. -(f : slash_invariant_form Γ k)}⟩

@[simp] lemma coe_neg (f : cusp_form Γ k) : ⇑(-f) = -f := rfl
@[simp] lemma neg_apply (f : cusp_form Γ k) (z : ℍ) : (-f) z = -(f z) := rfl

instance has_sub : has_sub (cusp_form Γ k) :=
⟨ λ f g, f + -g ⟩

@[simp] lemma coe_sub (f g : cusp_form Γ k) : ⇑(f - g) = f - g := rfl
@[simp] lemma sub_apply (f g : cusp_form Γ k) (z : ℍ) : (f - g) z = f z - g z := rfl

instance : add_comm_group (cusp_form Γ k) :=
fun_like.coe_injective.add_comm_group _ rfl coe_add coe_neg coe_sub coe_smul coe_smul

lemma coe_zero : ⇑(0 : cusp_form Γ k) = (0 : ℍ → ℂ) := rfl

/--Additive coercion from `cusp_form` to `ℍ → ℂ`. -/
def coe_hom : (cusp_form Γ k) →+ (ℍ → ℂ) :=
{ to_fun := λ f, f,
  map_zero' := cusp_form.coe_zero,
  map_add' := λ _ _, rfl }

lemma coe_hom_injective : function.injective (@coe_hom Γ k) :=
fun_like.coe_injective

instance : module ℂ (cusp_form Γ k) :=
coe_hom_injective.module ℂ (coe_hom) (λ _ _, rfl)

instance : inhabited (cusp_form Γ k) := ⟨0⟩

@[priority 99]
instance [cusp_form_class F Γ k] : modular_form_class F Γ k :=
{ coe := fun_like.coe,
  coe_injective' := fun_like.coe_injective',
  slash_action_eq := cusp_form_class.slash_action_eq,
  hol := cusp_form_class.hol,
  bdd_at_infty := λ _ _, (cusp_form_class.zero_at_infty _ _).bounded_at_filter}

end cusp_form
