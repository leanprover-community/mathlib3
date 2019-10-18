/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
import topology.subset_properties topology.dense_embedding

open set

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

/-- α and β are homeomorph, also called topological isomoph -/
structure homeomorph (α : Type*) (β : Type*) [topological_space α] [topological_space β]
  extends α ≃ β :=
(continuous_to_fun  : continuous to_fun)
(continuous_inv_fun : continuous inv_fun)

infix ` ≃ₜ `:25 := homeomorph

namespace homeomorph
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

instance : has_coe_to_fun (α ≃ₜ β) := ⟨λ_, α → β, λe, e.to_equiv⟩

lemma coe_eq_to_equiv (h : α ≃ₜ β) (a : α) : h a = h.to_equiv a := rfl

protected def refl (α : Type*) [topological_space α] : α ≃ₜ α :=
{ continuous_to_fun := continuous_id, continuous_inv_fun := continuous_id, .. equiv.refl α }

protected def trans (h₁ : α ≃ₜ β) (h₂ : β ≃ₜ γ) : α ≃ₜ γ :=
{ continuous_to_fun  := h₂.continuous_to_fun.comp h₁.continuous_to_fun,
  continuous_inv_fun := h₁.continuous_inv_fun.comp h₂.continuous_inv_fun,
  .. equiv.trans h₁.to_equiv h₂.to_equiv }

protected def symm (h : α ≃ₜ β) : β ≃ₜ α :=
{ continuous_to_fun  := h.continuous_inv_fun,
  continuous_inv_fun := h.continuous_to_fun,
  .. h.to_equiv.symm }

protected lemma continuous (h : α ≃ₜ β) : continuous h := h.continuous_to_fun

lemma symm_comp_self (h : α ≃ₜ β) : ⇑h.symm ∘ ⇑h = id :=
funext $ assume a, h.to_equiv.left_inv a

lemma self_comp_symm (h : α ≃ₜ β) : ⇑h ∘ ⇑h.symm = id :=
funext $ assume a, h.to_equiv.right_inv a

lemma range_coe (h : α ≃ₜ β) : range h = univ :=
eq_univ_of_forall $ assume b, ⟨h.symm b, congr_fun h.self_comp_symm b⟩

lemma image_symm (h : α ≃ₜ β) : image h.symm = preimage h :=
funext h.symm.to_equiv.image_eq_preimage

lemma preimage_symm (h : α ≃ₜ β) : preimage h.symm = image h :=
(funext h.to_equiv.image_eq_preimage).symm

lemma induced_eq
  {α : Type*} {β : Type*} [tα : topological_space α] [tβ : topological_space β] (h : α ≃ₜ β) :
  tβ.induced h = tα :=
le_antisymm
  (calc topological_space.induced ⇑h tβ ≤ _ : induced_mono (coinduced_le_iff_le_induced.1 h.symm.continuous)
  ... ≤ tα : by rw [induced_compose, symm_comp_self, induced_id] ; exact le_refl _)
  (coinduced_le_iff_le_induced.1 h.continuous)

lemma coinduced_eq
  {α : Type*} {β : Type*} [tα : topological_space α] [tβ : topological_space β] (h : α ≃ₜ β) :
  tα.coinduced h = tβ :=
le_antisymm
  h.continuous
  begin
    have : (tβ.coinduced h.symm).coinduced h ≤ tα.coinduced h := coinduced_mono h.symm.continuous,
    rwa [coinduced_compose, self_comp_symm, coinduced_id] at this,
  end

lemma compact_image {s : set α} (h : α ≃ₜ β) : compact (h '' s) ↔ compact s :=
⟨λ hs, by have := compact_image hs h.symm.continuous;
  rwa [← image_comp, symm_comp_self, image_id] at this,
λ hs, compact_image hs h.continuous⟩

lemma compact_preimage {s : set β} (h : α ≃ₜ β) : compact (h ⁻¹' s) ↔ compact s :=
by rw ← image_symm; exact h.symm.compact_image

protected lemma embedding (h : α ≃ₜ β) : embedding h :=
⟨⟨h.induced_eq.symm⟩, h.to_equiv.injective⟩

protected lemma dense_embedding (h : α ≃ₜ β) : dense_embedding h :=
{ dense   := assume a, by rw [h.range_coe, closure_univ]; trivial,
  inj     := h.to_equiv.injective,
  induced := (induced_iff_nhds_eq _).2 (assume a, by rw [← nhds_induced, h.induced_eq]) }

protected lemma is_open_map (h : α ≃ₜ β) : is_open_map h :=
begin
  assume s,
  rw ← h.preimage_symm,
  exact h.symm.continuous s
end

protected lemma is_closed_map (h : α ≃ₜ β) : is_closed_map h :=
begin
  assume s,
  rw ← h.preimage_symm,
  exact continuous_iff_is_closed.1 (h.symm.continuous) _
end

def homeomorph_of_continuous_open (e : α ≃ β) (h₁ : continuous e) (h₂ : is_open_map e) :
  α ≃ₜ β :=
{ continuous_to_fun := h₁,
  continuous_inv_fun := begin
    intros s hs,
    convert ← h₂ s hs using 1,
    apply e.image_eq_preimage
  end,
  .. e }

protected lemma quotient_map (h : α ≃ₜ β) : quotient_map h :=
⟨h.to_equiv.surjective, h.coinduced_eq.symm⟩

def prod_congr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : α × γ ≃ₜ β × δ :=
{ continuous_to_fun  :=
    continuous.prod_mk (h₁.continuous.comp continuous_fst) (h₂.continuous.comp continuous_snd),
  continuous_inv_fun :=
    continuous.prod_mk (h₁.symm.continuous.comp continuous_fst) (h₂.symm.continuous.comp continuous_snd),
  .. h₁.to_equiv.prod_congr h₂.to_equiv }

section
variables (α β γ)

def prod_comm : α × β ≃ₜ β × α :=
{ continuous_to_fun  := continuous.prod_mk continuous_snd continuous_fst,
  continuous_inv_fun := continuous.prod_mk continuous_snd continuous_fst,
  .. equiv.prod_comm α β }

def prod_assoc : (α × β) × γ ≃ₜ α × (β × γ) :=
{ continuous_to_fun  :=
    continuous.prod_mk (continuous_fst.comp continuous_fst)
      (continuous.prod_mk (continuous_snd.comp continuous_fst) continuous_snd),
  continuous_inv_fun := continuous.prod_mk
      (continuous.prod_mk continuous_fst (continuous_fst.comp continuous_snd))
      (continuous_snd.comp continuous_snd),
  .. equiv.prod_assoc α β γ }

end

section distrib
variables {ι : Type*} {σ : ι → Type*} [Π i, topological_space (σ i)]

def sigma_prod_distrib : ((Σ i, σ i) × β) ≃ₜ (Σ i, (σ i × β)) :=
homeomorph.symm $
homeomorph_of_continuous_open (equiv.sigma_prod_distrib σ β).symm
  (continuous_sigma $ λ i,
    continuous.prod_mk (continuous_sigma_mk.comp continuous_fst) continuous_snd)
  (is_open_map_sigma $ λ i,
    (open_embedding.prod open_embedding_sigma_mk open_embedding_id).is_open_map)

end distrib

end homeomorph
