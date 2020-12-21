/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
import topology.dense_embedding

open set filter
open_locale topological_space

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

/-- Homeomorphism between `α` and `β`, also called topological isomorphism -/
@[nolint has_inhabited_instance] -- not all spaces are homeomorphic to each other
structure homeomorph (α : Type*) (β : Type*) [topological_space α] [topological_space β]
  extends α ≃ β :=
(continuous_to_fun  : continuous to_fun . tactic.interactive.continuity')
(continuous_inv_fun : continuous inv_fun . tactic.interactive.continuity')

infix ` ≃ₜ `:25 := homeomorph

namespace homeomorph
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

instance : has_coe_to_fun (α ≃ₜ β) := ⟨λ_, α → β, λe, e.to_equiv⟩

@[simp] lemma homeomorph_mk_coe (a : equiv α β) (b c) :
  ((homeomorph.mk a b c) : α → β) = a :=
rfl

lemma coe_eq_to_equiv (h : α ≃ₜ β) (a : α) : h a = h.to_equiv a := rfl

/-- Identity map as a homeomorphism. -/
protected def refl (α : Type*) [topological_space α] : α ≃ₜ α :=
{ continuous_to_fun := continuous_id, continuous_inv_fun := continuous_id, .. equiv.refl α }

/-- Composition of two homeomorphisms. -/
protected def trans (h₁ : α ≃ₜ β) (h₂ : β ≃ₜ γ) : α ≃ₜ γ :=
{ continuous_to_fun  := h₂.continuous_to_fun.comp h₁.continuous_to_fun,
  continuous_inv_fun := h₁.continuous_inv_fun.comp h₂.continuous_inv_fun,
  .. equiv.trans h₁.to_equiv h₂.to_equiv }

/-- Inverse of a homeomorphism. -/
protected def symm (h : α ≃ₜ β) : β ≃ₜ α :=
{ continuous_to_fun  := h.continuous_inv_fun,
  continuous_inv_fun := h.continuous_to_fun,
  .. h.to_equiv.symm }

@[simp] lemma homeomorph_mk_coe_symm (a : equiv α β) (b c) :
  ((homeomorph.mk a b c).symm : β → α) = a.symm :=
rfl

@[continuity]
protected lemma continuous (h : α ≃ₜ β) : continuous h := h.continuous_to_fun

@[simp] lemma apply_symm_apply (h : α ≃ₜ β) (x : β) : h (h.symm x) = x :=
h.to_equiv.apply_symm_apply x

@[simp] lemma symm_apply_apply (h : α ≃ₜ β) (x : α) : h.symm (h x) = x :=
h.to_equiv.symm_apply_apply x

protected lemma bijective (h : α ≃ₜ β) : function.bijective h := h.to_equiv.bijective
protected lemma injective (h : α ≃ₜ β) : function.injective h := h.to_equiv.injective
protected lemma surjective (h : α ≃ₜ β) : function.surjective h := h.to_equiv.surjective

/-- Change the homeomorphism `f` to make the inverse function definitionally equal to `g`. -/
def change_inv (f : α ≃ₜ β) (g : β → α) (hg : function.right_inverse g f) : α ≃ₜ β :=
have g = f.symm, from funext (λ x, calc g x = f.symm (f (g x)) : (f.left_inv (g x)).symm
                                        ... = f.symm x : by rw hg x),
{ to_fun := f,
  inv_fun := g,
  left_inv := by convert f.left_inv,
  right_inv := by convert f.right_inv,
  continuous_to_fun := f.continuous,
  continuous_inv_fun := by convert f.symm.continuous }

@[simp] lemma symm_comp_self (h : α ≃ₜ β) : ⇑h.symm ∘ ⇑h = id :=
funext h.symm_apply_apply

@[simp] lemma self_comp_symm (h : α ≃ₜ β) : ⇑h ∘ ⇑h.symm = id :=
funext h.apply_symm_apply

@[simp] lemma range_coe (h : α ≃ₜ β) : range h = univ :=
h.surjective.range_eq

lemma image_symm (h : α ≃ₜ β) : image h.symm = preimage h :=
funext h.symm.to_equiv.image_eq_preimage

lemma preimage_symm (h : α ≃ₜ β) : preimage h.symm = image h :=
(funext h.to_equiv.image_eq_preimage).symm

@[simp] lemma image_preimage (h : α ≃ₜ β) (s : set β) : h '' (h ⁻¹' s) = s :=
h.to_equiv.image_preimage s

@[simp] lemma preimage_image (h : α ≃ₜ β) (s : set α) : h ⁻¹' (h '' s) = s :=
h.to_equiv.preimage_image s

protected lemma inducing (h : α ≃ₜ β) : inducing h :=
inducing_of_inducing_compose h.continuous h.symm.continuous $
  by simp only [symm_comp_self, inducing_id]

lemma induced_eq (h : α ≃ₜ β) : topological_space.induced h ‹_› = ‹_› := h.inducing.1.symm

protected lemma quotient_map (h : α ≃ₜ β) : quotient_map h :=
quotient_map.of_quotient_map_compose h.symm.continuous h.continuous $
  by simp only [self_comp_symm, quotient_map.id]

lemma coinduced_eq (h : α ≃ₜ β) : topological_space.coinduced h ‹_› = ‹_› :=
h.quotient_map.2.symm

protected lemma embedding (h : α ≃ₜ β) : embedding h :=
⟨h.inducing, h.to_equiv.injective⟩

lemma compact_image {s : set α} (h : α ≃ₜ β) : is_compact (h '' s) ↔ is_compact s :=
h.embedding.compact_iff_compact_image.symm

lemma compact_preimage {s : set β} (h : α ≃ₜ β) : is_compact (h ⁻¹' s) ↔ is_compact s :=
by rw ← image_symm; exact h.symm.compact_image

protected lemma dense_embedding (h : α ≃ₜ β) : dense_embedding h :=
{ dense   := h.surjective.dense_range,
  inj     := h.injective,
  induced := h.induced_eq.symm }

@[simp] lemma is_open_preimage (h : α ≃ₜ β) {s : set β} : is_open (h ⁻¹' s) ↔ is_open s :=
h.quotient_map.is_open_preimage

@[simp] lemma is_open_image (h : α ≃ₜ β) {s : set α} : is_open (h '' s) ↔ is_open s :=
by rw [← preimage_symm, is_open_preimage]

@[simp] lemma is_closed_preimage (h : α ≃ₜ β) {s : set β} : is_closed (h ⁻¹' s) ↔ is_closed s :=
by simp only [is_closed, ← preimage_compl, is_open_preimage]

@[simp] lemma is_closed_image (h : α ≃ₜ β) {s : set α} : is_closed (h '' s) ↔ is_closed s :=
by rw [← preimage_symm, is_closed_preimage]

lemma preimage_closure (h : α ≃ₜ β) (s : set β) : h ⁻¹' (closure s) = closure (h ⁻¹' s) :=
by rw [h.embedding.closure_eq_preimage_closure_image, h.image_preimage]

lemma image_closure (h : α ≃ₜ β) (s : set α) : h '' (closure s) = closure (h '' s) :=
by rw [← preimage_symm, preimage_closure]

protected lemma is_open_map (h : α ≃ₜ β) : is_open_map h := λ s, h.is_open_image.2

protected lemma is_closed_map (h : α ≃ₜ β) : is_closed_map h := λ s, h.is_closed_image.2

protected lemma closed_embedding (h : α ≃ₜ β) : closed_embedding h :=
closed_embedding_of_embedding_closed h.embedding h.is_closed_map

@[simp] lemma map_nhds_eq (h : α ≃ₜ β) (x : α) : map h (𝓝 x) = 𝓝 (h x) :=
h.embedding.map_nhds_eq _ (by simp)

@[simp] lemma comap_nhds_eq (h : α ≃ₜ β) (y : β) : comap h (𝓝 y) = 𝓝 (h.symm y) :=
by rw [h.embedding.to_inducing.nhds_eq_comap, h.apply_symm_apply]

lemma nhds_eq_comap (h : α ≃ₜ β) (x : α) : 𝓝 x = comap h (𝓝 (h x)) :=
by rw [comap_nhds_eq, h.symm_apply_apply]

@[simp] lemma is_open_image (h : α ≃ₜ β) {s : set α} : is_open (h '' s) ↔ is_open s :=
by rw [← preimage_symm, is_open_preimage]

@[simp] lemma is_closed_preimage (h : α ≃ₜ β) {s : set β} : is_closed (h ⁻¹' s) ↔ is_closed s :=
by simp only [is_closed, ← preimage_compl, is_open_preimage]

@[simp] lemma is_closed_image (h : α ≃ₜ β) {s : set α} : is_closed (h '' s) ↔ is_closed s :=
by rw [← preimage_symm, is_closed_preimage]

lemma preimage_closure (h : α ≃ₜ β) (s : set β) : h ⁻¹' (closure s) = closure (h ⁻¹' s) :=
by rw [h.embedding.closure_eq_preimage_closure_image, h.image_preimage]

lemma image_closure (h : α ≃ₜ β) (s : set α) : h '' (closure s) = closure (h '' s) :=
by rw [← preimage_symm, preimage_closure]

@[simp] lemma map_nhds_eq (h : α ≃ₜ β) (x : α) : map h (𝓝 x) = 𝓝 (h x) :=
h.embedding.map_nhds_eq _ (by simp)

@[simp] lemma comap_nhds_eq (h : α ≃ₜ β) (y : β) : comap h (𝓝 y) = 𝓝 (h.symm y) :=
by rw [h.embedding.to_inducing.nhds_eq_comap, h.apply_symm_apply]

lemma nhds_eq_comap (h : α ≃ₜ β) (x : α) : 𝓝 x = comap h (𝓝 (h x)) :=
by rw [comap_nhds_eq, h.symm_apply_apply]

/-- If an bijective map `e : α ≃ β` is continuous and open, then it is a homeomorphism. -/
def homeomorph_of_continuous_open (e : α ≃ β) (h₁ : continuous e) (h₂ : is_open_map e) :
  α ≃ₜ β :=
{ continuous_to_fun := h₁,
  continuous_inv_fun := begin
    rw continuous_def,
    intros s hs,
    convert ← h₂ s hs using 1,
    apply e.image_eq_preimage
  end,
  .. e }

@[simp] lemma comp_continuous_on_iff (h : α ≃ₜ β) (f : γ → α) (s : set γ) :
  continuous_on (h ∘ f) s ↔ continuous_on f s :=
⟨λ H, by simpa only [(∘), h.symm_apply_apply] using h.symm.continuous.comp_continuous_on H,
  λ H, h.continuous.comp_continuous_on H⟩

@[simp] lemma comp_continuous_iff (h : α ≃ₜ β) {f : γ → α} :
  continuous (h ∘ f) ↔ continuous f :=
by simp [continuous_iff_continuous_on_univ, comp_continuous_on_iff]

@[simp] lemma comp_continuous_iff' (h : α ≃ₜ β) {f : β → γ} :
  continuous (f ∘ h) ↔ continuous f :=
⟨λ H, by simpa only [(∘), h.apply_symm_apply] using H.comp h.symm.continuous,
  λ H, H.comp h.continuous⟩

/-- If two sets are equal, then they are homeomorphic. -/
def set_congr {s t : set α} (h : s = t) : s ≃ₜ t :=
{ continuous_to_fun := continuous_subtype_mk _ continuous_subtype_val,
  continuous_inv_fun := continuous_subtype_mk _ continuous_subtype_val,
  .. equiv.set_congr h }

/-- Sum of two homeomorphisms. -/
def sum_congr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : α ⊕ γ ≃ₜ β ⊕ δ :=
{ continuous_to_fun  :=
  begin
    convert continuous_sum_rec (continuous_inl.comp h₁.continuous)
      (continuous_inr.comp h₂.continuous),
    ext x, cases x; refl,
  end,
  continuous_inv_fun :=
  begin
    convert continuous_sum_rec (continuous_inl.comp h₁.symm.continuous)
      (continuous_inr.comp h₂.symm.continuous),
    ext x, cases x; refl
  end,
  .. h₁.to_equiv.sum_congr h₂.to_equiv }

/-- Product of two homeomorphisms. -/
def prod_congr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : α × γ ≃ₜ β × δ :=
{ continuous_to_fun  := (h₁.continuous.comp continuous_fst).prod_mk
    (h₂.continuous.comp continuous_snd),
  continuous_inv_fun := (h₁.symm.continuous.comp continuous_fst).prod_mk
    (h₂.symm.continuous.comp continuous_snd),
  .. h₁.to_equiv.prod_congr h₂.to_equiv }

section
variables (α β γ)

/-- `α × β` is homeomorphic to `β × α`. -/
def prod_comm : α × β ≃ₜ β × α :=
{ continuous_to_fun  := continuous_snd.prod_mk continuous_fst,
  continuous_inv_fun := continuous_snd.prod_mk continuous_fst,
  .. equiv.prod_comm α β }

/-- `(α × β) × γ` is homeomorphic to `α × (β × γ)`. -/
def prod_assoc : (α × β) × γ ≃ₜ α × (β × γ) :=
{ continuous_to_fun  := (continuous_fst.comp continuous_fst).prod_mk
    ((continuous_snd.comp continuous_fst).prod_mk continuous_snd),
  continuous_inv_fun := (continuous_fst.prod_mk (continuous_fst.comp continuous_snd)).prod_mk
    (continuous_snd.comp continuous_snd),
  .. equiv.prod_assoc α β γ }

end

/-- `ulift α` is homeomorphic to `α`. -/
def {u v} ulift {α : Type u} [topological_space α] : ulift.{v u} α ≃ₜ α :=
{ continuous_to_fun := continuous_ulift_down,
  continuous_inv_fun := continuous_ulift_up,
  .. equiv.ulift }

section distrib

/-- `(α ⊕ β) × γ` is homeomorphic to `α × γ ⊕ β × γ`. -/
def sum_prod_distrib : (α ⊕ β) × γ ≃ₜ α × γ ⊕ β × γ :=
begin
  refine (homeomorph.homeomorph_of_continuous_open (equiv.sum_prod_distrib α β γ).symm _ _).symm,
  { convert continuous_sum_rec
      ((continuous_inl.comp continuous_fst).prod_mk continuous_snd)
      ((continuous_inr.comp continuous_fst).prod_mk continuous_snd),
    ext1 x, cases x; refl, },
  { exact (is_open_map_sum
    (open_embedding_inl.prod open_embedding_id).is_open_map
    (open_embedding_inr.prod open_embedding_id).is_open_map) }
end

/-- `α × (β ⊕ γ)` is homeomorphic to `α × β ⊕ α × γ`. -/
def prod_sum_distrib : α × (β ⊕ γ) ≃ₜ α × β ⊕ α × γ :=
(prod_comm _ _).trans $
sum_prod_distrib.trans $
sum_congr (prod_comm _ _) (prod_comm _ _)

variables {ι : Type*} {σ : ι → Type*} [Π i, topological_space (σ i)]

/-- `(Σ i, σ i) × β` is homeomorphic to `Σ i, (σ i × β)`. -/
def sigma_prod_distrib : ((Σ i, σ i) × β) ≃ₜ (Σ i, (σ i × β)) :=
homeomorph.symm $
homeomorph_of_continuous_open (equiv.sigma_prod_distrib σ β).symm
  (continuous_sigma $ λ i,
    (continuous_sigma_mk.comp continuous_fst).prod_mk continuous_snd)
  (is_open_map_sigma $ λ i,
    (open_embedding_sigma_mk.prod open_embedding_id).is_open_map)

end distrib

end homeomorph
