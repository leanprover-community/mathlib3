/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton,
Anatole Dedecker
-/
import topology.homeomorph
import topology.uniform_space.uniform_embedding
import topology.uniform_space.pi

/-!
# Uniform isomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines uniform isomorphisms between two uniform spaces. They are bijections with both
directions uniformly continuous. We denote uniform isomorphisms with the notation `≃ᵤ`.

# Main definitions

* `uniform_equiv α β`: The type of uniform isomorphisms from `α` to `β`.
  This type can be denoted using the following notation: `α ≃ᵤ β`.

-/

open set filter
open_locale

universes u v
variables {α : Type u} {β : Type*} {γ : Type*} {δ : Type*}

/-- Uniform isomorphism between `α` and `β` -/
@[nolint has_nonempty_instance] -- not all spaces are homeomorphic to each other
structure uniform_equiv (α : Type*) (β : Type*) [uniform_space α] [uniform_space β]
  extends α ≃ β :=
(uniform_continuous_to_fun  : uniform_continuous to_fun)
(uniform_continuous_inv_fun : uniform_continuous inv_fun)

infix ` ≃ᵤ `:25 := uniform_equiv

namespace uniform_equiv
variables [uniform_space α] [uniform_space β] [uniform_space γ] [uniform_space δ]

instance : has_coe_to_fun (α ≃ᵤ β) (λ _, α → β) := ⟨λe, e.to_equiv⟩

@[simp] lemma uniform_equiv_mk_coe (a : equiv α β) (b c) :
  ((uniform_equiv.mk a b c) : α → β) = a :=
rfl

/-- Inverse of a uniform isomorphism. -/
protected def symm (h : α ≃ᵤ β) : β ≃ᵤ α :=
{ uniform_continuous_to_fun  := h.uniform_continuous_inv_fun,
  uniform_continuous_inv_fun := h.uniform_continuous_to_fun,
  to_equiv := h.to_equiv.symm }

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (h : α ≃ᵤ β) : α → β := h
/-- See Note [custom simps projection] -/
def simps.symm_apply (h : α ≃ᵤ β) : β → α := h.symm

initialize_simps_projections uniform_equiv
  (to_equiv_to_fun → apply, to_equiv_inv_fun → symm_apply, -to_equiv)

@[simp] lemma coe_to_equiv (h : α ≃ᵤ β) : ⇑h.to_equiv = h := rfl
@[simp] lemma coe_symm_to_equiv (h : α ≃ᵤ β) : ⇑h.to_equiv.symm = h.symm := rfl

lemma to_equiv_injective : function.injective (to_equiv : α ≃ᵤ β → α ≃ β)
| ⟨e, h₁, h₂⟩ ⟨e', h₁', h₂'⟩ rfl := rfl

@[ext] lemma ext {h h' : α ≃ᵤ β} (H : ∀ x, h x = h' x) : h = h' :=
to_equiv_injective $ equiv.ext H

/-- Identity map as a uniform isomorphism. -/
@[simps apply {fully_applied := ff}]
protected def refl (α : Type*) [uniform_space α] : α ≃ᵤ α :=
{ uniform_continuous_to_fun := uniform_continuous_id,
  uniform_continuous_inv_fun := uniform_continuous_id,
  to_equiv := equiv.refl α }

/-- Composition of two uniform isomorphisms. -/
protected def trans (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) : α ≃ᵤ γ :=
{ uniform_continuous_to_fun  := h₂.uniform_continuous_to_fun.comp h₁.uniform_continuous_to_fun,
  uniform_continuous_inv_fun := h₁.uniform_continuous_inv_fun.comp h₂.uniform_continuous_inv_fun,
  to_equiv := equiv.trans h₁.to_equiv h₂.to_equiv }

@[simp] lemma trans_apply (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) (a : α) : h₁.trans h₂ a = h₂ (h₁ a) := rfl

@[simp] lemma uniform_equiv_mk_coe_symm (a : equiv α β) (b c) :
  ((uniform_equiv.mk a b c).symm : β → α) = a.symm :=
rfl

@[simp] lemma refl_symm : (uniform_equiv.refl α).symm = uniform_equiv.refl α := rfl

protected lemma uniform_continuous (h : α ≃ᵤ β) : uniform_continuous h :=
h.uniform_continuous_to_fun

@[continuity]
protected lemma continuous (h : α ≃ᵤ β) : continuous h :=
h.uniform_continuous.continuous

protected lemma uniform_continuous_symm (h : α ≃ᵤ β) : uniform_continuous (h.symm) :=
h.uniform_continuous_inv_fun

@[continuity] -- otherwise `by continuity` can't prove continuity of `h.to_equiv.symm`
protected lemma continuous_symm (h : α ≃ᵤ β) : continuous (h.symm) :=
h.uniform_continuous_symm.continuous

/-- A uniform isomorphism as a homeomorphism. -/
@[simps]
protected def to_homeomorph (e : α ≃ᵤ β) : α ≃ₜ β :=
{ continuous_to_fun := e.continuous,
  continuous_inv_fun := e.continuous_symm,
  .. e.to_equiv }

@[simp] lemma apply_symm_apply (h : α ≃ᵤ β) (x : β) : h (h.symm x) = x :=
h.to_equiv.apply_symm_apply x

@[simp] lemma symm_apply_apply (h : α ≃ᵤ β) (x : α) : h.symm (h x) = x :=
h.to_equiv.symm_apply_apply x

protected lemma bijective (h : α ≃ᵤ β) : function.bijective h := h.to_equiv.bijective
protected lemma injective (h : α ≃ᵤ β) : function.injective h := h.to_equiv.injective
protected lemma surjective (h : α ≃ᵤ β) : function.surjective h := h.to_equiv.surjective

/-- Change the uniform equiv `f` to make the inverse function definitionally equal to `g`. -/
def change_inv (f : α ≃ᵤ β) (g : β → α) (hg : function.right_inverse g f) : α ≃ᵤ β :=
have g = f.symm, from funext (λ x, calc g x = f.symm (f (g x)) : (f.left_inv (g x)).symm
                                        ... = f.symm x : by rw hg x),
{ to_fun := f,
  inv_fun := g,
  left_inv := by convert f.left_inv,
  right_inv := by convert f.right_inv,
  uniform_continuous_to_fun := f.uniform_continuous,
  uniform_continuous_inv_fun := by convert f.symm.uniform_continuous }

@[simp] lemma symm_comp_self (h : α ≃ᵤ β) : ⇑h.symm ∘ ⇑h = id :=
funext h.symm_apply_apply

@[simp] lemma self_comp_symm (h : α ≃ᵤ β) : ⇑h ∘ ⇑h.symm = id :=
funext h.apply_symm_apply

@[simp] lemma range_coe (h : α ≃ᵤ β) : range h = univ :=
h.surjective.range_eq

lemma image_symm (h : α ≃ᵤ β) : image h.symm = preimage h :=
funext h.symm.to_equiv.image_eq_preimage

lemma preimage_symm (h : α ≃ᵤ β) : preimage h.symm = image h :=
(funext h.to_equiv.image_eq_preimage).symm

@[simp] lemma image_preimage (h : α ≃ᵤ β) (s : set β) : h '' (h ⁻¹' s) = s :=
h.to_equiv.image_preimage s

@[simp] lemma preimage_image (h : α ≃ᵤ β) (s : set α) : h ⁻¹' (h '' s) = s :=
h.to_equiv.preimage_image s

protected lemma uniform_inducing (h : α ≃ᵤ β) : uniform_inducing h :=
uniform_inducing_of_compose h.uniform_continuous h.symm.uniform_continuous $
  by simp only [symm_comp_self, uniform_inducing_id]

lemma comap_eq (h : α ≃ᵤ β) : uniform_space.comap h ‹_› = ‹_› :=
by ext : 1; exact h.uniform_inducing.comap_uniformity

protected lemma uniform_embedding (h : α ≃ᵤ β) : uniform_embedding h :=
⟨h.uniform_inducing, h.injective⟩

/-- Uniform equiv given a uniform embedding. -/
noncomputable def of_uniform_embedding (f : α → β) (hf : uniform_embedding f) :
  α ≃ᵤ (set.range f) :=
{ uniform_continuous_to_fun := hf.to_uniform_inducing.uniform_continuous.subtype_mk _,
  uniform_continuous_inv_fun :=
    by simp [hf.to_uniform_inducing.uniform_continuous_iff, uniform_continuous_subtype_coe],
  to_equiv := equiv.of_injective f hf.inj }

/-- If two sets are equal, then they are uniformly equivalent. -/
def set_congr {s t : set α} (h : s = t) : s ≃ᵤ t :=
{ uniform_continuous_to_fun := uniform_continuous_subtype_val.subtype_mk _,
  uniform_continuous_inv_fun := uniform_continuous_subtype_val.subtype_mk _,
  to_equiv := equiv.set_congr h }

/-- Product of two uniform isomorphisms. -/
def prod_congr (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) : α × γ ≃ᵤ β × δ :=
{ uniform_continuous_to_fun  := (h₁.uniform_continuous.comp uniform_continuous_fst).prod_mk
    (h₂.uniform_continuous.comp uniform_continuous_snd),
  uniform_continuous_inv_fun := (h₁.symm.uniform_continuous.comp uniform_continuous_fst).prod_mk
    (h₂.symm.uniform_continuous.comp uniform_continuous_snd),
  to_equiv := h₁.to_equiv.prod_congr h₂.to_equiv }

@[simp] lemma prod_congr_symm (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) :
  (h₁.prod_congr h₂).symm = h₁.symm.prod_congr h₂.symm := rfl

@[simp] lemma coe_prod_congr (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) :
  ⇑(h₁.prod_congr h₂) = prod.map h₁ h₂ := rfl

section
variables (α β γ)

/-- `α × β` is uniformly isomorphic to `β × α`. -/
def prod_comm : α × β ≃ᵤ β × α :=
{ uniform_continuous_to_fun  := uniform_continuous_snd.prod_mk uniform_continuous_fst,
  uniform_continuous_inv_fun := uniform_continuous_snd.prod_mk uniform_continuous_fst,
  to_equiv := equiv.prod_comm α β }

@[simp] lemma prod_comm_symm : (prod_comm α β).symm = prod_comm β α := rfl
@[simp] lemma coe_prod_comm : ⇑(prod_comm α β) = prod.swap := rfl

/-- `(α × β) × γ` is uniformly isomorphic to `α × (β × γ)`. -/
def prod_assoc : (α × β) × γ ≃ᵤ α × (β × γ) :=
{ uniform_continuous_to_fun  := (uniform_continuous_fst.comp uniform_continuous_fst).prod_mk
    ((uniform_continuous_snd.comp uniform_continuous_fst).prod_mk uniform_continuous_snd),
  uniform_continuous_inv_fun := (uniform_continuous_fst.prod_mk
    (uniform_continuous_fst.comp uniform_continuous_snd)).prod_mk
    (uniform_continuous_snd.comp uniform_continuous_snd),
  to_equiv := equiv.prod_assoc α β γ }

/-- `α × {*}` is uniformly isomorphic to `α`. -/
@[simps apply {fully_applied := ff}]
def prod_punit : α × punit ≃ᵤ α :=
{ to_equiv := equiv.prod_punit α,
  uniform_continuous_to_fun := uniform_continuous_fst,
  uniform_continuous_inv_fun := uniform_continuous_id.prod_mk uniform_continuous_const }

/-- `{*} × α` is uniformly isomorphic to `α`. -/
def punit_prod : punit × α ≃ᵤ α :=
(prod_comm _ _).trans (prod_punit _)

@[simp] lemma coe_punit_prod : ⇑(punit_prod α) = prod.snd := rfl

/-- Uniform equivalence between `ulift α` and `α`. -/
def ulift : ulift.{v u} α ≃ᵤ α :=
{ uniform_continuous_to_fun := uniform_continuous_comap,
  uniform_continuous_inv_fun := begin
    have hf : uniform_inducing (@equiv.ulift.{v u} α).to_fun, from ⟨rfl⟩,
    simp_rw [hf.uniform_continuous_iff],
    exact uniform_continuous_id,
  end,
  .. equiv.ulift }

end

/-- If `ι` has a unique element, then `ι → α` is homeomorphic to `α`. -/
@[simps { fully_applied := ff }]
def fun_unique (ι α : Type*) [unique ι] [uniform_space α] : (ι → α) ≃ᵤ α :=
{ to_equiv := equiv.fun_unique ι α,
  uniform_continuous_to_fun := Pi.uniform_continuous_proj _ _,
  uniform_continuous_inv_fun := uniform_continuous_pi.mpr (λ _, uniform_continuous_id) }

/-- Uniform isomorphism between dependent functions `Π i : fin 2, α i` and `α 0 × α 1`. -/
@[simps { fully_applied := ff }]
def pi_fin_two (α : fin 2 → Type u) [Π i, uniform_space (α i)] : (Π i, α i) ≃ᵤ α 0 × α 1 :=
{ to_equiv := pi_fin_two_equiv α,
  uniform_continuous_to_fun :=
    (Pi.uniform_continuous_proj _ 0).prod_mk (Pi.uniform_continuous_proj _ 1),
  uniform_continuous_inv_fun := uniform_continuous_pi.mpr $
    fin.forall_fin_two.2 ⟨uniform_continuous_fst, uniform_continuous_snd⟩ }

/-- Uniform isomorphism between `α² = fin 2 → α` and `α × α`. -/
@[simps { fully_applied := ff }] def fin_two_arrow : (fin 2 → α) ≃ᵤ α × α :=
{ to_equiv := fin_two_arrow_equiv α, .. pi_fin_two (λ _, α) }

/--
A subset of a uniform space is uniformly isomorphic to its image under a uniform isomorphism.
-/
def image (e : α ≃ᵤ β) (s : set α) : s ≃ᵤ e '' s :=
{ uniform_continuous_to_fun :=
    (e.uniform_continuous.comp uniform_continuous_subtype_val).subtype_mk _,
  uniform_continuous_inv_fun :=
    (e.symm.uniform_continuous.comp uniform_continuous_subtype_val).subtype_mk _,
  to_equiv := e.to_equiv.image s }

end uniform_equiv

/-- A uniform inducing equiv between uniform spaces is a uniform isomorphism. -/
@[simps] def equiv.to_uniform_equiv_of_uniform_inducing [uniform_space α] [uniform_space β]
  (f : α ≃ β) (hf : uniform_inducing f) :
  α ≃ᵤ β :=
{ uniform_continuous_to_fun := hf.uniform_continuous,
  uniform_continuous_inv_fun := hf.uniform_continuous_iff.2 $ by simpa using uniform_continuous_id,
  .. f }
