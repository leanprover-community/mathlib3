/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Yury Kudryashov
-/
import logic.rel.lemmas order.complete_lattice data.set.lattice

/-!
# Properties of relations that involve order

In this file we prove various properties of relations using `≤` either in the statement,
or in the proof.
-/
universes u v w x

attribute [derive lattice.complete_lattice] rel

namespace rel

variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {r : rel α β}

lemma lift_fun_mono : ((≥) ⟹ (≤) ⟹ (≤)).diag (@lift_fun α β γ δ) :=
assume rac₁ rac₂ hac rbd₁ rbd₂ hbd f g hfg x y hxy,
hbd _ _ $ hfg $ hac _ _ hxy

lemma lift_fun_mono_right (r : rel α γ) : monotone (@lift_fun α β γ δ r) :=
lift_fun_mono (le_refl r)

lemma lift_fun_mono_left (r : rel β δ) : ((≥) ⟹ (≤)).diag (λ r', @lift_fun α β γ δ r' r) :=
assume rac₁ rac₂ hac, lift_fun_mono hac (le_refl r)

lemma inf_rel_rel (rac : rel α γ) (rbd₁ rbd₂ : rel β δ) :
  (rac ⟹ rbd₁) ⊓ (rac ⟹ rbd₂) = (rac ⟹ (rbd₁ ⊓ rbd₂)) :=
le_antisymm
  (λ f g ⟨h₁, h₂⟩ x z hxz, ⟨h₁ hxz, h₂ hxz⟩)
  (monotone.map_inf rac.lift_fun_mono_right rbd₁ rbd₂)

lemma inf_le_ge [partial_order α] : ((≤) ⊓ (≥)) = rel.id α :=
ext $ λ x y, le_antisymm_iff.symm

lemma inf_rel_le_ge [partial_order β] : (r ⟹ ((≤) : rel β β)) ⊓ (r ⟹ (≥)) = (r ⟹ (rel.id β)) :=
by rw [inf_rel_rel r (≤) (≥), inf_le_ge]

lemma bi_total.rel_forall (hr : r.bi_total) :
  ((r ⟹ (↔)) ⟹ (↔)) (λp, ∀ i, p i) (λq, ∀j, q j) :=
assume p q Hrel,
⟨hr.2.rel_forall $ lift_fun_mono_right r @iff.mp _ _ Hrel,
  hr.1.rel_forall $ lift_fun_mono_right r @iff.mpr _ _ Hrel⟩

lemma bi_total.rel_exists (hr : r.bi_total) :
  ((r ⟹ (↔)) ⟹ (↔)) (λp, ∃ i, p i) (λq, ∃j, q j) :=
assume p q Hrel,
⟨hr.1.rel_exists $ lift_fun_mono_right r @iff.mp _ _ Hrel,
  hr.2.rel_exists $ lift_fun_mono_right r @iff.mpr _ _ Hrel⟩

lemma left_unique_of_rel_eq {eq' : rel β β} (h : (r ⟹ r ⟹ iff) eq eq') : left_unique r :=
assume x₁ x₂ y h₁ h₂, (h h₁ h₂).mpr $ (h h₁ h₁).mp rfl

lemma right_unique_of_rel_eq {eq' : rel α α} (h : (r ⟹ r ⟹ iff) eq' eq) : right_unique r :=
assume x y₁ y₂ h₁ h₂, (h h₁ h₂).mp $ (h h₁ h₁).mpr rfl

variable (r)

lemma image_mono : monotone r.image := assume s t h y ⟨x, xs, rxy⟩, ⟨x, h xs, rxy⟩

lemma image_subset : ((⊆) ⟹ (⊆)).diag r.image := r.image_mono

lemma image_inter (s t : set α) : r.image (s ∩ t) ⊆ r.image s ∩ r.image t :=
r.image_mono.map_inf s t

lemma image_union (s t : set α) : r.image (s ∪ t) = r.image s ∪ r.image t :=
le_antisymm
  (λ y ⟨x, xst, rxy⟩, xst.elim (λ xs, or.inl ⟨x, ⟨xs, rxy⟩⟩) (λ xt, or.inr ⟨x, ⟨xt, rxy⟩⟩))
  (r.image_mono.map_sup s t)

lemma preimage_mono : monotone r.preimage := r.conv.image_mono

lemma preimage_subset : ((⊆) ⟹ (⊆)).diag r.preimage :=
r.conv.image_subset

lemma preimage_inter (s t : set β) : r.preimage (s ∩ t) ⊆ r.preimage s ∩ r.preimage t :=
r.conv.image_inter s t

lemma preimage_union (s t : set β) : r.preimage (s ∪ t) = r.preimage s ∪ r.preimage t :=
image_union _ s t

variable {r}

lemma left_unique.image_inter (h : left_unique r) (s t : set α) :
  r.image (s ∩ t) = r.image s ∩ r.image t :=
le_antisymm (r.image_inter s t) $
assume y ⟨⟨x, xs, hxy⟩, ⟨x', x't, hx'y⟩⟩,
have x = x', from h hxy hx'y,
⟨x, ⟨xs, this.symm ▸ x't⟩, hxy⟩

lemma right_unique.preimage_inter (h : right_unique r) (s t : set β) :
  r.preimage (s ∩ t) = r.preimage s ∩ r.preimage t :=
h.conv.image_inter s t

variable (r)

lemma core_mono : monotone r.core := assume s t h x h' y rxy, h $ h' rxy

lemma core_subset {s t : set β} (h : s ⊆ t) : r.core s ⊆ r.core t :=
r.core_mono h

lemma core_inter (s t : set β) : r.core (s ∩ t) = r.core s ∩ r.core t :=
le_antisymm (r.core_mono.map_inf s t) $ assume x ⟨hs, ht⟩ y hxy, ⟨hs hxy, ht hxy⟩

lemma core_union (s t : set β) : r.core (s ∪ t) ⊇ r.core s ∪ r.core t :=
r.core_mono.map_sup s t

theorem core_preimage_gc : galois_connection (image r) (core r) :=
image_subset_iff _

end rel
