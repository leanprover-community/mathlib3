/-
Copyright (c) 2022 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import representation_theory.rep_hom

/-!
# Homomorphisms between representations

This file defines equivalence between representations `rep_equiv`. We could define it as linear
equivalence between modules that preserve the group action, or in the case of this file, as
`rep_hom` that is also an `add_equiv`. Lemmas and definitions closely follow
`algebra.module.equiv`.

## Notations

Since multiple different representations may be defined on the same vector space, the `rep_equiv`s
are written to be from `ρ : representation k G V` to `ρ₂ : representation k G V₂`
(denoted `ρ ≃ᵣ ρ₂`), rather than from `V` to `V₂`.

## Tags

representation, isomorphism
-/

open function
open_locale big_operators

section
set_option old_structure_cmd true

/-- A linear equivalence is an invertible linear map. -/
@[nolint has_inhabited_instance]
structure rep_equiv {k G V V₂ : Type*} [comm_semiring k] [monoid G]
  [add_comm_monoid V] [module k V] [add_comm_monoid V₂] [module k V₂]
  (ρ : representation k G V) (ρ₂ : representation k G V₂)
  extends rep_hom ρ ρ₂, V ≃+ V₂
end

attribute [nolint doc_blame] rep_equiv.to_rep_hom
attribute [nolint doc_blame] rep_equiv.to_add_equiv

infixr ` ≃ᵣ `:25 := rep_equiv

namespace rep_equiv

section add_comm_monoid

variables
  {k G V V₂ : Type*} [comm_semiring k] [monoid G]
  [add_comm_monoid V] [module k V] [add_comm_monoid V₂] [module k V₂]
  {ρ : representation k G V} {ρ₂ : representation k G V₂}

instance : has_coe (ρ ≃ᵣ ρ₂) (ρ →ᵣ ρ₂) := ⟨to_rep_hom⟩
instance : has_coe_to_fun (ρ ≃ᵣ ρ₂) (λ _, V → V₂) := ⟨to_fun⟩

@[simp] lemma coe_mk {to_fun inv_fun map_add map_smul map_smulG left_inv right_inv} :
  ⇑(⟨to_fun, map_add, map_smul, map_smulG, inv_fun, left_inv, right_inv⟩ : ρ ≃ᵣ ρ₂) = to_fun :=
rfl

@[nolint doc_blame]
def to_equiv : (ρ ≃ᵣ ρ₂) → V ≃ V₂ := λ f, f.to_add_equiv.to_equiv

lemma to_equiv_injective : function.injective (to_equiv : (ρ ≃ᵣ ρ₂) → V ≃ V₂) :=
λ ⟨_, _, _, _, _, _, _⟩ ⟨_, _, _, _, _, _, _⟩ h, rep_equiv.mk.inj_eq.mpr (equiv.mk.inj h)

@[simp] lemma to_equiv_inj {e₁ e₂ : ρ ≃ᵣ ρ₂} : e₁.to_equiv = e₂.to_equiv ↔ e₁ = e₂ :=
to_equiv_injective.eq_iff

lemma to_rep_hom_injective :
  injective (coe : (ρ ≃ᵣ ρ₂) → (ρ →ᵣ ρ₂)) :=
λ e₁ e₂ H, to_equiv_injective $ equiv.ext $ rep_hom.congr_fun H

@[simp, norm_cast] lemma to_rep_hom_inj {e₁ e₂ : ρ ≃ᵣ ρ₂} :
  (e₁ : ρ →ᵣ ρ₂) = e₂ ↔ e₁ = e₂ :=
to_rep_hom_injective.eq_iff

instance : rep_hom_class (ρ ≃ᵣ ρ₂) ρ ρ₂ :=
{ coe := rep_equiv.to_fun,
  coe_injective' := λ f g h, to_rep_hom_injective (fun_like.coe_injective h),
  map_add := map_add',
  map_smulₛₗ := map_smul',
  map_smulG := map_smulG' }

lemma coe_injective :
  @injective (ρ ≃ᵣ ρ₂) (V → V₂) coe_fn :=
fun_like.coe_injective

variables (e e' : ρ ≃ᵣ ρ₂)

lemma to_rep_hom_eq_coe : e.to_rep_hom = (e : ρ →ᵣ ρ₂) := rfl

@[simp, norm_cast] theorem coe_coe : ⇑(e : ρ →ᵣ ρ₂) = e := rfl

@[simp] lemma coe_to_equiv : ⇑e.to_equiv = e := rfl

@[simp] lemma coe_to_rep_hom : ⇑e.to_rep_hom = e := rfl

@[simp] lemma to_fun_eq_coe : e.to_fun = e := rfl

section

variables {e e'}

@[ext] lemma ext (h : ∀ x, e x = e' x) : e = e' := fun_like.ext _ _ h

lemma ext_iff : e = e' ↔ ∀ x, e x = e' x := fun_like.ext_iff

protected lemma congr_arg {x x'} : x = x' → e x = e x' := fun_like.congr_arg e

protected lemma congr_fun (h : e = e') (x : V) : e x = e' x := fun_like.congr_fun h x

end

variables (ρ)

/-- The identity map is a representation equivalence. -/
@[refl]
def refl : ρ ≃ᵣ ρ := { .. rep_hom.id, .. equiv.refl V }

variables {ρ}

@[simp] lemma refl_apply (x : V) : refl ρ x = x := rfl

/-- Representation equivalences are symmetric. -/
@[symm]
def symm (e : ρ ≃ᵣ ρ₂) : ρ₂ ≃ᵣ ρ :=
{ .. e.to_rep_hom.inverse e.inv_fun e.left_inv e.right_inv,
  .. e.to_equiv.symm }

/-- See Note [custom simps projection] -/
def simps.symm_apply (e : ρ ≃ᵣ ρ₂) : V₂ → V := e.symm

initialize_simps_projections rep_equiv (to_fun → apply, inv_fun → symm_apply)

@[simp] lemma inv_fun_eq_symm : e.inv_fun = e.symm := rfl

@[simp] lemma coe_to_equiv_symm : ⇑e.to_equiv.symm = e.symm := rfl

variables
  {V₃ : Type*} [add_comm_monoid V₃] [module k V₃] {ρ₃ : representation k G V₃}
  (e₁₂ : ρ ≃ᵣ ρ₂) (e₂₃ : ρ₂ ≃ᵣ ρ₃)

/-- Representation equivalences are transitive. -/
@[trans]
def trans : ρ ≃ᵣ ρ₃ :=
{ .. e₂₃.to_rep_hom.comp e₁₂.to_rep_hom,
  .. e₁₂.to_equiv.trans e₂₃.to_equiv }

infixr ` ≪≫ᵣ `:80 := rep_equiv.trans

variables {e₁₂ e₂₃}

@[simp] lemma coe_to_add_equiv : ⇑(e.to_add_equiv) = e := rfl

-- to_add_monoid_hom_commutes

@[simp] theorem trans_apply (c : V) :
  (e₁₂.trans e₂₃ : ρ ≃ᵣ ρ₃) c = e₂₃ (e₁₂ c) := rfl

@[simp] theorem apply_symm_apply (c : V₂) : e (e.symm c) = c := e.right_inv c
@[simp] theorem symm_apply_apply (b : V) : e.symm (e b) = b := e.left_inv b

@[simp] lemma trans_symm : (e₁₂.trans e₂₃ : ρ ≃ᵣ ρ₃).symm = e₂₃.symm.trans e₁₂.symm :=
rfl

lemma symm_trans_apply
  (c : V₃) : (e₁₂.trans e₂₃ : ρ ≃ᵣ ρ₃).symm c = e₁₂.symm (e₂₃.symm c) := rfl

@[simp] lemma trans_refl : e.trans (refl ρ₂) = e := to_equiv_injective e.to_equiv.trans_refl
@[simp] lemma refl_trans : (refl ρ).trans e = e := to_equiv_injective e.to_equiv.refl_trans

lemma symm_apply_eq {x y} : e.symm x = y ↔ x = e y := e.to_equiv.symm_apply_eq

lemma eq_symm_apply {x y} : y = e.symm x ↔ e y = x := e.to_equiv.eq_symm_apply

lemma eq_comp_symm {α : Type*} (f : V₂ → α) (g : V → α) :
  f = g ∘ e₁₂.symm ↔ f ∘ e₁₂ = g := e₁₂.to_equiv.eq_comp_symm f g

lemma comp_symm_eq {α : Type*} (f : V₂ → α) (g : V → α) :
  g ∘ e₁₂.symm = f ↔ g = f ∘ e₁₂ := e₁₂.to_equiv.comp_symm_eq f g

lemma eq_symm_comp {α : Type*} (f : α → V) (g : α → V₂) :
  f = e₁₂.symm ∘ g ↔ e₁₂ ∘ f = g := e₁₂.to_equiv.eq_symm_comp f g

lemma symm_comp_eq {α : Type*} (f : α → V) (g : α → V₂) :
  e₁₂.symm ∘ g = f ↔ g = e₁₂ ∘ f := e₁₂.to_equiv.symm_comp_eq f g

lemma eq_comp_to_rep_hom_symm (f : ρ₂ →ᵣ ρ₃) (g : ρ →ᵣ ρ₃) :
  f = g.comp e₁₂.symm.to_rep_hom ↔ f.comp e₁₂.to_rep_hom = g :=
begin
  split; intro H; ext,
  { simp [H, e₁₂.to_equiv.eq_comp_symm f g] },
  { simp [←H, ←e₁₂.to_equiv.eq_comp_symm f g] }
end

lemma comp_to_rep_hom_symm_eq (f : ρ₂ →ᵣ ρ₃) (g : ρ →ᵣ ρ₃) :
  g.comp e₁₂.symm.to_rep_hom = f ↔ g = f.comp e₁₂.to_rep_hom :=
begin
  split; intro H; ext,
  { simp [←H, ←e₁₂.to_equiv.comp_symm_eq f g] },
  { simp [H, e₁₂.to_equiv.comp_symm_eq f g] }
end

lemma eq_to_rep_hom_symm_comp (f : ρ₃ →ᵣ ρ) (g : ρ₃ →ᵣ ρ₂) :
  f = e₁₂.symm.to_rep_hom.comp g ↔ e₁₂.to_rep_hom.comp f = g :=
begin
  split; intro H; ext,
  { simp [H, e₁₂.to_equiv.eq_symm_comp f g] },
  { simp [←H, ←e₁₂.to_equiv.eq_symm_comp f g] }
end

lemma to_rep_hom_symm_comp_eq (f : ρ₃ →ᵣ ρ) (g : ρ₃ →ᵣ ρ₂) :
  e₁₂.symm.to_rep_hom.comp g = f ↔ g = e₁₂.to_rep_hom.comp f :=
begin
  split; intro H; ext,
  { simp [←H, ←e₁₂.to_equiv.symm_comp_eq f g] },
  { simp [H, e₁₂.to_equiv.symm_comp_eq f g] }
end

@[simp] lemma refl_symm : (refl ρ).symm = rep_equiv.refl ρ := rfl

@[simp] lemma self_trans_symm (f : ρ ≃ᵣ ρ₂) :
  f.trans f.symm = rep_equiv.refl ρ :=
by { ext x, simp }

@[simp] lemma symm_trans_self (f : ρ ≃ᵣ ρ₂) :
  f.symm.trans f = rep_equiv.refl ρ₂ :=
by { ext x, simp }

@[simp, norm_cast] lemma refl_to_rep_hom :
  (rep_equiv.refl ρ : ρ →ᵣ ρ) = rep_hom.id :=
rfl

@[simp, norm_cast]
lemma comp_coe (f : ρ ≃ᵣ ρ₂) (f' : ρ₂ ≃ᵣ ρ₃) :
  (f' : ρ₂ →ᵣ ρ₃).comp (f : ρ →ᵣ ρ₂) = (f.trans f' : ρ ≃ᵣ ρ₃) := rfl

@[simp] lemma mk_coe (h₁ h₂ h₃ f h₄ h₅) :
  (rep_equiv.mk e h₁ h₂ h₃ f h₄ h₅ : ρ ≃ᵣ ρ₂) = e := ext $ λ _, rfl

protected theorem map_add (a b : V) : e (a + b) = e a + e b := map_add e a b
protected theorem map_zero : e 0 = 0 := map_zero e
@[simp] protected theorem map_smulₛₗ (c : k) (x : V) : e (c • x) = c • e x := e.map_smul' c x
@[simp] protected theorem map_smulG (g : G) (x : V) : e (ρ g x) = ρ₂ g (e x) := e.map_smulG' g x

@[simp] lemma map_sum {ι : Type*} {s : finset ι} (u : ι → V) : e (∑ i in s, u i) = ∑ i in s, e (u i) :=
e.to_rep_hom.map_sum

@[simp] theorem map_eq_zero_iff {x : V} : e x = 0 ↔ x = 0 :=
e.to_add_equiv.map_eq_zero_iff
theorem map_ne_zero_iff {x : V} : e x ≠ 0 ↔ x ≠ 0 :=
e.to_add_equiv.map_ne_zero_iff

@[simp] theorem symm_symm (e : ρ ≃ᵣ ρ₂): e.symm.symm = e :=
by { cases e, refl }

lemma symm_bijective : function.bijective (symm : (ρ ≃ᵣ ρ₂) → (ρ₂ ≃ᵣ ρ)) :=
equiv.bijective ⟨(symm : (ρ ≃ᵣ ρ₂) →
  (ρ₂ ≃ᵣ ρ)), (symm : (ρ₂ ≃ᵣ ρ) → (ρ ≃ᵣ ρ₂)), symm_symm, symm_symm⟩

@[simp] lemma mk_coe' (f h₁ h₂ h₃ h₄ h₅) : (rep_equiv.mk f h₁ h₂ h₃ ⇑e h₄ h₅ :
  ρ₂ ≃ᵣ ρ) = e.symm :=
symm_bijective.injective $ ext $ λ x, rfl

@[simp] theorem symm_mk (f h₁ h₂ h₃ h₄ h₅) :
  (⟨e, h₁, h₂, h₃, f, h₄, h₅⟩ : ρ ≃ᵣ ρ₂).symm =
  { to_fun := f, inv_fun := e,
    ..(⟨e, h₁, h₂, h₃, f, h₄, h₅⟩ : ρ ≃ᵣ ρ₂).symm } := rfl

@[simp] lemma coe_symm_mk
  {to_fun inv_fun map_add map_smul map_smulG left_inv right_inv} :
  ⇑((⟨to_fun, map_add, map_smul, map_smulG, inv_fun, left_inv, right_inv⟩ : ρ ≃ᵣ ρ₂).symm) = inv_fun :=
rfl

protected lemma bijective : function.bijective e := e.to_equiv.bijective
protected lemma injective : function.injective e := e.to_equiv.injective
protected lemma surjective : function.surjective e := e.to_equiv.surjective

protected lemma image_eq_preimage (s : set V) : e '' s = e.symm ⁻¹' s :=
e.to_equiv.image_eq_preimage s

protected lemma image_symm_eq_preimage (s : set V₂) : e.symm '' s = e ⁻¹' s :=
e.to_equiv.symm.image_eq_preimage s

section pointwise
open_locale pointwise

@[simp] lemma image_smul_set (e : ρ ≃ᵣ ρ₂) (c : k) (s : set V) :
  e '' (c • s) = c • e '' s :=
rep_hom.image_smul_set e.to_rep_hom c s

@[simp] lemma preimage_smul_set (e : ρ ≃ᵣ ρ₂) (c : k) (s : set V₂) :
  e ⁻¹' (c • s) = c • e ⁻¹' s :=
by rw [← rep_equiv.image_symm_eq_preimage, ← rep_equiv.image_symm_eq_preimage,
  image_smul_set]

end pointwise

-- restrict_scalars

section automorphisms

instance automorphism_group : group (ρ ≃ᵣ ρ) :=
{ mul := λ f g, g.trans f,
  one := rep_equiv.refl ρ,
  inv := λ f, f.symm,
  mul_assoc := λ f g h, rfl,
  mul_one := λ f, ext $ λ x, rfl,
  one_mul := λ f, ext $ λ x, rfl,
  mul_left_inv := λ f, ext $ f.left_inv }

/-- Restriction from representation automorphisms of `ρ` to representation endomorphisms of `ρ`,
promoted to a monoid hom. -/
@[simps]
def automorphism_group.to_linear_map_monoid_hom : (ρ ≃ᵣ ρ) →* (ρ →ᵣ ρ) :=
{ to_fun := coe,
  map_one' := rfl,
  map_mul' := λ _ _, rfl }

-- apply_distrib_mul_action

end automorphisms

end add_comm_monoid

end rep_equiv

namespace representation

-- comp_hom.to_linear_equiv

end representation

namespace distrib_mul_action

--

end distrib_mul_action

namespace add_equiv

--

end add_equiv
