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

/-!
Define versions of `eq_on`, `inj_on` and `restrict` for `finset`s.

This is mostly for convenience so that we can use dot notation for these on `finset`s.
-/

section finset_versions

variables {α : Type*} {β : Type*}

/-- The restriction of `f` to a `finset` `s` -/
def restrict (s : finset α) (f : α →  β) (a : ↥s) : β := f a

/-- The statement that two functions `f` and `g` agree on a `finset` `s` -/
def eq_on (f g : α → β) (s : finset α) : Prop := (s : set α).eq_on f g

/-- The statement that a function `f` is injective on a `finset` `s` -/
def inj_on (f : α → β) (s : finset α) : Prop := (s : set α).inj_on f

-- We don't need the next two, but include them for completeness

/-- The statement that a function `f` is surjective from a `finset` `s` to a `finset` `t` -/
def surj_on (f : α → β) (s : finset α) (t : finset β) : Prop := (s : set α).surj_on f t

/-- The statement that a function `f` is bijective from a `finset` `s` to a `finset` `t` -/
def bij_on (f : α → β) (s : finset α) (t : finset β) : Prop := (s : set α).bij_on f t

end finset_versions

/-!
Auxiliary `finset` lemmas.
-/

section α

variables {α : Type*} [decidable_eq α]

lemma insert_sdiff_singleton_self {a : α} {s : finset α} (h : a ∈ s) : s = insert a (s \ {a}) :=
begin
  ext b,
  simp only [mem_insert, mem_sdiff, mem_singleton],
  by_cases H : b = a; simp [h, H],
end

lemma insert_sdiff_singleton_self' {a : α} {s : finset α} (h : a ∉ s) : s = insert a s \ {a} :=
begin
  rw insert_sdiff_of_mem _ (mem_singleton_self _),
  exact (sdiff_singleton_not_mem_eq_self _ h).symm,
end

lemma card_insert_eq_card_iff (a : α) (s : finset α) : (insert a s).card = s.card ↔ a ∈ s :=
begin
  rw card_insert_eq_ite,
  simp only [imp_false, ite_eq_left_iff, nat.succ_ne_self, not_not],
end

lemma card_insert_eq_card_add_one {a : α} {s : finset α} (h : a ∉ s) :
  (insert a s).card = s.card + 1 :=
by simp only [card_insert_eq_ite, h, if_false]

end α

section β

variables {α β : Type*} [decidable_eq β]

lemma image_eq_image_restrict_univ (s : finset α) (f : α → β) :
  s.image f = univ.image (s.restrict f) :=
by {ext, simp only [mem_image, univ_eq_attach, mem_attach, exists_true_left, subtype.coe_mk,
                    restrict, finset.exists_coe]}

lemma image_eq_range_coe (s : finset α) (f : α → β) :
  (s.image f : set β) = set.range (f ∘ (coe : s → α)) :=
begin
  ext,
  simp only [finset.coe_image, set.mem_image, finset.mem_coe, set.mem_range,
             function.comp_app, finset.exists_coe, subtype.coe_mk, exists_prop],
end

end β

section αβ

variables {α β : Type*} [decidable_eq α] [decidable_eq β]

lemma image_update {s : finset α} (f : α → β) {a : α} (h : a ∈ s) (b : β) :
  s.image (function.update f a b) = (s \ {a}).image f ∪ {b} :=
begin
  ext c,
  simp only [mem_image, exists_prop, mem_union, mem_sdiff, mem_singleton],
  refine ⟨λ H, _, λ H, _⟩,
  { obtain ⟨j, hj₁, hj₂⟩ := H,
    rcases eq_or_ne j a with rfl | hji,
    { exact or.inr (hj₂ ▸ function.update_same j b f), },
    { exact or.inl ⟨j, ⟨hj₁, hji⟩, hj₂ ▸ (function.update_noteq hji b f).symm⟩, } },
  { rcases H with ⟨j, ⟨hj₁, hj₂⟩, hj₃⟩ | rfl,
    { exact ⟨j, hj₁, hj₃ ▸ function.update_noteq hj₂ b f⟩, },
    { exact ⟨a, h, function.update_same a c f⟩, } }
end

lemma image_restrict_eq_image_image_coe (s : finset α) (f : α → β) (t : finset s) :
  t.image (s.restrict f) = (t.image coe).image f :=
by {ext, simp only [mem_image, exists_prop, subtype.coe_mk, exists_and_distrib_right,
                    exists_eq_right, restrict, finset.exists_coe]}

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

end αβ

end finset
