/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import data.set.finite
import algebra.big_operators.basic

/-!
# Preimage of a `finset` under an injective map.
-/

open set function

open_locale big_operators

universes u v w x
variables {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace finset

section preimage

/-- Preimage of `s : finset β` under a map `f` injective of `f ⁻¹' s` as a `finset`.  -/
noncomputable def preimage (s : finset β) (f : α → β)
  (hf : set.inj_on f (f ⁻¹' ↑s)) : finset α :=
(s.finite_to_set.preimage hf).to_finset

@[simp] lemma mem_preimage {f : α → β} {s : finset β} {hf : set.inj_on f (f ⁻¹' ↑s)} {x : α} :
  x ∈ preimage s f hf ↔ f x ∈ s :=
set.finite.mem_to_finset _

@[simp, norm_cast] lemma coe_preimage {f : α → β} (s : finset β)
  (hf : set.inj_on f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : set α) = f ⁻¹' ↑s :=
set.finite.coe_to_finset _

@[simp] lemma preimage_empty {f : α → β} : preimage ∅ f (by simp [inj_on]) = ∅ :=
finset.coe_injective (by simp)

@[simp] lemma preimage_univ {f : α → β} [fintype α] [fintype β] (hf) :
  preimage univ f hf = univ :=
finset.coe_injective (by simp)

@[simp] lemma preimage_inter [decidable_eq α] [decidable_eq β] {f : α → β} {s t : finset β}
  (hs : set.inj_on f (f ⁻¹' ↑s)) (ht : set.inj_on f (f ⁻¹' ↑t)) :
  preimage (s ∩ t) f (λ x₁ hx₁ x₂ hx₂, hs (mem_of_mem_inter_left hx₁) (mem_of_mem_inter_left hx₂))
    = preimage s f hs ∩ preimage t f ht :=
finset.coe_injective (by simp)

@[simp] lemma preimage_union [decidable_eq α] [decidable_eq β] {f : α → β} {s t : finset β} (hst) :
  preimage (s ∪ t) f hst
    = preimage s f (λ x₁ hx₁ x₂ hx₂, hst (mem_union_left _ hx₁) (mem_union_left _ hx₂))
    ∪ preimage t f (λ x₁ hx₁ x₂ hx₂, hst (mem_union_right _ hx₁) (mem_union_right _ hx₂)) :=
finset.coe_injective (by simp)

@[simp] lemma preimage_compl [decidable_eq α] [decidable_eq β] [fintype α] [fintype β]
  {f : α → β} (s : finset β) (hf : function.injective f) :
  preimage sᶜ f (hf.inj_on _) = (preimage s f (hf.inj_on _))ᶜ :=
finset.coe_injective (by simp)

lemma monotone_preimage {f : α → β} (h : injective f) :
  monotone (λ s, preimage s f (h.inj_on _)) :=
λ s t hst x hx, mem_preimage.2 (hst $ mem_preimage.1 hx)

lemma image_subset_iff_subset_preimage [decidable_eq β] {f : α → β} {s : finset α} {t : finset β}
  (hf : set.inj_on f (f ⁻¹' ↑t)) :
  s.image f ⊆ t ↔ s ⊆ t.preimage f hf :=
image_subset_iff.trans $ by simp only [subset_iff, mem_preimage]

lemma map_subset_iff_subset_preimage {f : α ↪ β} {s : finset α} {t : finset β} :
  s.map f ⊆ t ↔ s ⊆ t.preimage f (f.injective.inj_on _) :=
by classical; rw [map_eq_image, image_subset_iff_subset_preimage]

lemma image_preimage [decidable_eq β] (f : α → β) (s : finset β) [Π x, decidable (x ∈ set.range f)]
  (hf : set.inj_on f (f ⁻¹' ↑s)) :
  image f (preimage s f hf) = s.filter (λ x, x ∈ set.range f) :=
finset.coe_inj.1 $ by simp only [coe_image, coe_preimage, coe_filter,
  set.image_preimage_eq_inter_range, set.sep_mem_eq]

lemma image_preimage_of_bij [decidable_eq β] (f : α → β) (s : finset β)
  (hf : set.bij_on f (f ⁻¹' ↑s) ↑s) :
  image f (preimage s f hf.inj_on) = s :=
finset.coe_inj.1 $ by simpa using hf.image_eq

lemma sigma_preimage_mk {β : α → Type*} [decidable_eq α] (s : finset (Σ a, β a)) (t : finset α) :
  t.sigma (λ a, s.preimage (sigma.mk a) $ sigma_mk_injective.inj_on _) = s.filter (λ a, a.1 ∈ t) :=
by { ext x, simp [and_comm] }

lemma sigma_preimage_mk_of_subset {β : α → Type*} [decidable_eq α] (s : finset (Σ a, β a))
  {t : finset α} (ht : s.image sigma.fst ⊆ t) :
  t.sigma (λ a, s.preimage (sigma.mk a) $ sigma_mk_injective.inj_on _) = s :=
by rw [sigma_preimage_mk, filter_true_of_mem $ image_subset_iff.1 ht]

lemma sigma_image_fst_preimage_mk {β : α → Type*} [decidable_eq α] (s : finset (Σ a, β a)) :
  (s.image sigma.fst).sigma (λ a, s.preimage (sigma.mk a) $ sigma_mk_injective.inj_on _) = s :=
s.sigma_preimage_mk_of_subset (subset.refl _)

end preimage

@[to_additive]
lemma prod_preimage' [comm_monoid β] (f : α → γ) [decidable_pred $ λ x, x ∈ set.range f]
  (s : finset γ) (hf : set.inj_on f (f ⁻¹' ↑s)) (g : γ → β) :
  ∏ x in s.preimage f hf, g (f x) = ∏ x in s.filter (λ x, x ∈ set.range f), g x :=
by haveI := classical.dec_eq γ;
calc ∏ x in preimage s f hf, g (f x) = ∏ x in image f (preimage s f hf), g x :
  eq.symm $ prod_image $ by simpa only [mem_preimage, inj_on] using hf
  ... = ∏ x in s.filter (λ x, x ∈ set.range f), g x : by rw [image_preimage]

@[to_additive]
lemma prod_preimage [comm_monoid β] (f : α → γ) (s : finset γ)
  (hf : set.inj_on f (f ⁻¹' ↑s)) (g : γ → β) (hg : ∀ x ∈ s, x ∉ set.range f → g x = 1) :
  ∏ x in s.preimage f hf, g (f x) = ∏ x in s, g x :=
by { classical, rw [prod_preimage', prod_filter_of_ne], exact λ x hx, not.imp_symm (hg x hx) }

@[to_additive]
lemma prod_preimage_of_bij [comm_monoid β] (f : α → γ) (s : finset γ)
  (hf : set.bij_on f (f ⁻¹' ↑s) ↑s) (g : γ → β) :
  ∏ x in s.preimage f hf.inj_on, g (f x) = ∏ x in s, g x :=
prod_preimage _ _ hf.inj_on g $ λ x hxs hxf, (hxf $ hf.subset_range hxs).elim

end finset
