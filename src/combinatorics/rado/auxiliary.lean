/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/

import data.finset.card
import data.fintype.basic

/-!
# Some auxiliary lemmas on finsets etc.

These should probably go into `data.finset.basic`, `data.finset.image` or `data.fintype.basic`.
-/

namespace finset

variables {α : Type*} [decidable_eq α]

@[simp]
lemma card_insert_eq_card_iff {a : α} {s : finset α} : (insert a s).card = s.card ↔ a ∈ s :=
by simp only [card_insert_eq_ite, imp_false, ite_eq_left_iff, nat.succ_ne_self, not_not]

variables {β : Type*} [decidable_eq β]

lemma image_update {s : finset α} (f : α → β) {a : α} (h : a ∈ s) (b : β) :
  s.image (function.update f a b) = insert b ((s.erase a).image f) :=
begin
  ext c,
  simp only [mem_image, exists_prop, mem_insert, mem_erase, ne.def],
  refine ⟨λ H, _, λ H, _⟩,
  { obtain ⟨j, hj₁, hj₂⟩ := H,
    rcases eq_or_ne j a with rfl | hji,
    { refine or.inl (hj₂ ▸ function.update_same j b f), },
    { exact or.inr ⟨j, ⟨hji, hj₁⟩, hj₂ ▸ (function.update_noteq hji b f).symm⟩, } },
  { rcases H with rfl | ⟨j, ⟨hj₁, hj₂⟩, hj₃⟩,
    { exact ⟨a, h, function.update_same a c f⟩, },
    { exact ⟨j, hj₂, hj₃ ▸ function.update_noteq hj₁ b f⟩, } }
end

lemma image_restrict_eq_image_image_coe (s : finset α) (f : α → β) (t : finset s) :
  t.image (set.restrict ↑s f) = (t.image coe).image f :=
by {ext, simp only [mem_image, exists_prop, subtype.coe_mk, exists_and_distrib_right,
                    exists_eq_right, finset.exists_coe, set.restrict_apply]}

lemma bUnion_union (s t : finset α) (f : α → finset β) :
  (s ∪ t).bUnion f = s.bUnion f ∪ t.bUnion f :=
begin
  ext,
  simp only [or_and_distrib_right, exists_or_distrib, mem_bUnion, mem_union, exists_prop],
end

lemma eq_of_apply_eq_apply_of_card_le_card {f : α → β} {a b : α} (h₁ : f a = f b)
  (h₂ : ({a, b} : finset α).card ≤ (image f ({a, b} : finset α)).card) : a = b :=
begin
  replace h₂ := le_antisymm h₂ card_image_le,
  simp only [image_insert, image_singleton] at h₂,
  rw h₁ at h₂,
  simp only [pair_eq_singleton, card_singleton] at h₂,
  refine (eq_or_ne a b).elim id (λ hh, _),
  rw card_doubleton hh at h₂,
  cases h₂,
end

end finset
