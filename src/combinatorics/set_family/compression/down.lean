/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.card

/-!
# Down-compressions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines down-compression.

Down-compressing `𝒜 : finset (finset α)` along `a : α` means removing `a` from the elements of `𝒜`,
when the resulting set is not already in `𝒜`.

## Main declarations

* `finset.non_member_subfamily`: `𝒜.non_member_subfamily a` is the subfamily of sets not containing
  `a`.
* `finset.member_subfamily`: `𝒜.member_subfamily a` is the image of the subfamily of sets containing
  `a` under removing `a`.
* `down.compression`: Down-compression.

## Notation

`𝓓 a 𝒜` is notation for `down.compress a 𝒜` in locale `set_family`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

compression, down-compression
-/

variables {α : Type*} [decidable_eq α] {𝒜 ℬ : finset (finset α)} {s : finset α} {a : α}

namespace finset

/-- Elements of `𝒜` that do not contain `a`. -/
def non_member_subfamily (a : α) (𝒜 : finset (finset α)) : finset (finset α) :=
𝒜.filter $ λ s, a ∉ s

/-- Image of the elements of `𝒜` which contain `a` under removing `a`. Finsets that do not contain
`a` such that `insert a s ∈ 𝒜`. -/
def member_subfamily (a : α) (𝒜 : finset (finset α)) : finset (finset α) :=
(𝒜.filter $ λ s, a ∈ s).image $ λ s, erase s a

@[simp] lemma mem_non_member_subfamily : s ∈ 𝒜.non_member_subfamily a ↔ s ∈ 𝒜 ∧ a ∉ s := mem_filter
@[simp] lemma mem_member_subfamily : s ∈ 𝒜.member_subfamily a ↔ insert a s ∈ 𝒜 ∧ a ∉ s :=
begin
  simp_rw [member_subfamily, mem_image, mem_filter],
  refine ⟨_, λ h, ⟨insert a s, ⟨h.1, mem_insert_self _ _⟩, erase_insert h.2⟩⟩,
  rintro ⟨s, hs, rfl⟩,
  rw insert_erase hs.2,
  exact ⟨hs.1, not_mem_erase _ _⟩,
end

lemma non_member_subfamily_inter (a : α) (𝒜 ℬ : finset (finset α)) :
  (𝒜 ∩ ℬ).non_member_subfamily a = 𝒜.non_member_subfamily a ∩ ℬ.non_member_subfamily a :=
filter_inter_distrib _ _ _

lemma member_subfamily_inter (a : α) (𝒜 ℬ : finset (finset α)) :
  (𝒜 ∩ ℬ).member_subfamily a = 𝒜.member_subfamily a ∩ ℬ.member_subfamily a :=
begin
  unfold member_subfamily,
  rw [filter_inter_distrib, image_inter_of_inj_on _ _ ((erase_inj_on' _).mono _)],
  rw [←coe_union, ←filter_union, coe_filter],
  exact set.inter_subset_right _ _,
end

lemma non_member_subfamily_union (a : α) (𝒜 ℬ : finset (finset α)) :
  (𝒜 ∪ ℬ).non_member_subfamily a = 𝒜.non_member_subfamily a ∪ ℬ.non_member_subfamily a :=
filter_union _ _ _

lemma member_subfamily_union (a : α) (𝒜 ℬ : finset (finset α)) :
  (𝒜 ∪ ℬ).member_subfamily a = 𝒜.member_subfamily a ∪ ℬ.member_subfamily a :=
by simp_rw [member_subfamily, filter_union, image_union]

lemma card_member_subfamily_add_card_non_member_subfamily (a : α) (𝒜 : finset (finset α)) :
  (𝒜.member_subfamily a).card + (𝒜.non_member_subfamily a).card = 𝒜.card :=
begin
  rw [member_subfamily, non_member_subfamily, card_image_of_inj_on,
    filter_card_add_filter_neg_card_eq_card],
  exact (erase_inj_on' _).mono (λ s hs, (mem_filter.1 hs).2),
end

lemma member_subfamily_union_non_member_subfamily (a : α) (𝒜 : finset (finset α)) :
  𝒜.member_subfamily a ∪ 𝒜.non_member_subfamily a = 𝒜.image (λ s, s.erase a) :=
begin
  ext s,
  simp only [mem_union, mem_member_subfamily, mem_non_member_subfamily, mem_image, exists_prop],
  split,
  { rintro (h | h),
    { exact ⟨_, h.1, erase_insert h.2⟩ },
    { exact ⟨_, h.1, erase_eq_of_not_mem h.2⟩ } },
  { rintro ⟨s, hs, rfl⟩,
    by_cases ha : a ∈ s,
    { exact or.inl ⟨by rwa insert_erase ha, not_mem_erase _ _⟩ },
    { exact or.inr ⟨by rwa erase_eq_of_not_mem ha, not_mem_erase _ _⟩ } }
end

@[simp] lemma member_subfamily_member_subfamily : (𝒜.member_subfamily a).member_subfamily a = ∅ :=
by { ext, simp }

@[simp] lemma member_subfamily_non_member_subfamily :
  (𝒜.non_member_subfamily a).member_subfamily a = ∅ :=
by { ext, simp }

@[simp] lemma non_member_subfamily_member_subfamily :
  (𝒜.member_subfamily a).non_member_subfamily a = 𝒜.member_subfamily a :=
by { ext, simp }

@[simp] lemma non_member_subfamily_non_member_subfamily :
  (𝒜.non_member_subfamily a).non_member_subfamily a = 𝒜.non_member_subfamily a :=
by { ext, simp }

end finset

open finset

-- The namespace is here to distinguish from other compressions.
namespace down

/-- `a`-down-compressing `𝒜` means removing `a` from the elements of `𝒜` that contain it, when the
resulting finset is not already in `𝒜`. -/
def compression (a : α) (𝒜 : finset (finset α)) : finset (finset α) :=
(𝒜.filter $ λ s, erase s a ∈ 𝒜).disj_union ((𝒜.image $ λ s, erase s a).filter $ λ s, s ∉ 𝒜) $
  disjoint_left.2 $ λ s h₁ h₂, (mem_filter.1 h₂).2 (mem_filter.1 h₁).1

localized "notation (name := down.compression) `𝓓 ` := down.compression" in finset_family

/-- `a` is in the down-compressed family iff it's in the original and its compression is in the
original, or it's not in the original but it's the compression of something in the original. -/
lemma mem_compression : s ∈ 𝓓 a 𝒜 ↔ s ∈ 𝒜 ∧ s.erase a ∈ 𝒜 ∨ s ∉ 𝒜 ∧ insert a s ∈ 𝒜 :=
begin
  simp_rw [compression, mem_disj_union, mem_filter, mem_image, and_comm (s ∉ 𝒜)],
  refine or_congr_right' (and_congr_left $ λ hs,
    ⟨_, λ h, ⟨_, h, erase_insert $ insert_ne_self.1 $ ne_of_mem_of_not_mem h hs⟩⟩),
  rintro ⟨t, ht, rfl⟩,
  rwa insert_erase (erase_ne_self.1 (ne_of_mem_of_not_mem ht hs).symm),
end

lemma erase_mem_compression (hs : s ∈ 𝒜) : s.erase a ∈ 𝓓 a 𝒜 :=
begin
  simp_rw [mem_compression, erase_idem, and_self],
  refine (em _).imp_right (λ h, ⟨h, _⟩),
  rwa insert_erase (erase_ne_self.1 (ne_of_mem_of_not_mem hs h).symm),
end

-- This is a special case of `erase_mem_compression` once we have `compression_idem`.
lemma erase_mem_compression_of_mem_compression : s ∈ 𝓓 a 𝒜 → s.erase a ∈ 𝓓 a 𝒜 :=
begin
  simp_rw [mem_compression, erase_idem],
  refine or.imp (λ h, ⟨h.2, h.2⟩) (λ h, _),
  rwa [erase_eq_of_not_mem (insert_ne_self.1 $ ne_of_mem_of_not_mem h.2 h.1)],
end

lemma mem_compression_of_insert_mem_compression (h : insert a s ∈ 𝓓 a 𝒜) : s ∈ 𝓓 a 𝒜 :=
begin
  by_cases ha : a ∈ s,
  { rwa insert_eq_of_mem ha at h },
  { rw ←erase_insert ha,
    exact erase_mem_compression_of_mem_compression h }
end

/-- Down-compressing a family is idempotent. -/
@[simp] lemma compression_idem (a : α) (𝒜 : finset (finset α)) : 𝓓 a (𝓓 a 𝒜) = 𝓓 a 𝒜 :=
begin
  ext s,
  refine mem_compression.trans ⟨_, λ h, or.inl ⟨h, erase_mem_compression_of_mem_compression h⟩⟩,
  rintro (h | h),
  { exact h.1 },
  { cases h.1 (mem_compression_of_insert_mem_compression h.2) }
end

/-- Down-compressing a family doesn't change its size. -/
@[simp] lemma card_compression (a : α) (𝒜 : finset (finset α)) : (𝓓 a 𝒜).card = 𝒜.card :=
begin
  rw [compression, card_disj_union, image_filter, card_image_of_inj_on ((erase_inj_on' _).mono $
    λ s hs, _), ←card_disjoint_union, filter_union_filter_neg_eq],
  { exact disjoint_filter_filter_neg _ _ _ },
  rw [mem_coe, mem_filter] at hs,
  exact not_imp_comm.1 erase_eq_of_not_mem (ne_of_mem_of_not_mem hs.1 hs.2).symm,
end

end down
