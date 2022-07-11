/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.fintype.basic

/-!
# Down-compressions

This file defines down-compression. It is an operation on a set family that reduces its shadow.

Down-compressing `a : α` along `u v : α` means replacing `a` by `(a ⊔ u) \ v` if `a` and `u` are
disjoint and `v ≤ a`. In some sense, it's moving `a` from `v` to `u`.

Down-compressions are immensely useful to prove the Kruskal-Katona theorem. The idea is that
compressing a set family might decrease the size of its shadow, so iterated compressions hopefully
minimise the shadow.

## Main declarations

* `finset.non_member_section`: `𝒜.non_member_section a` is the subfamily of sets not containing `a`.
* `finset.member_section`: `𝒜.member_section a` is the image of the subfamily of sets containing
  `a` under removing `a`.
* `down.compress`: `compress u v a` is `a` compressed along `u` and `v`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

compression, down-compression
-/

variables {α : Type*} [decidable_eq α] {𝒜 ℬ : finset (finset α)} {s : finset α} {a : α}

namespace finset

/-- ELements of `𝒜` that do not contain `a`. -/
def non_member_section (a : α) (𝒜 : finset (finset α)) : finset (finset α) :=
𝒜.filter $ λ s, a ∉ s

/-- Image of the elements of `𝒜` which contain `a` under removing `a`. Finsets that do not contain
`a` such that `insert a s ∈ 𝒜`. -/
def member_section (a : α) (𝒜 : finset (finset α)) : finset (finset α) :=
(𝒜.filter $ λ s, a ∈ s).image $ λ s, erase s a

@[simp] lemma mem_non_member_section : s ∈ 𝒜.non_member_section a ↔ s ∈ 𝒜 ∧ a ∉ s := mem_filter
@[simp] lemma mem_member_section : s ∈ 𝒜.member_section a ↔ insert a s ∈ 𝒜 ∧ a ∉ s :=
begin
  simp_rw [member_section, mem_image, mem_filter],
  refine ⟨_, λ h, ⟨insert a s, ⟨h.1, mem_insert_self _ _⟩, erase_insert h.2⟩⟩,
  rintro ⟨s, hs, rfl⟩,
  rw insert_erase hs.2,
  exact ⟨hs.1, not_mem_erase _ _⟩,
end

lemma non_member_section_inter (a : α) (𝒜 ℬ : finset (finset α)) :
  (𝒜 ∩ ℬ).non_member_section a = 𝒜.non_member_section a ∩ ℬ.non_member_section a :=
filter_inter_distrib _ _ _

lemma member_section_inter (a : α) (𝒜 ℬ : finset (finset α)) :
  (𝒜 ∩ ℬ).member_section a = 𝒜.member_section a ∩ ℬ.member_section a :=
begin
  unfold member_section,
  rw [filter_inter_distrib, image_inter_of_inj_on _ _ ((erase_inj_on' _).mono _)],
  rw [←coe_union, ←filter_union, coe_filter],
  exact set.inter_subset_right _ _,
end

lemma non_member_section_union (a : α) (𝒜 ℬ : finset (finset α)) :
  (𝒜 ∪ ℬ).non_member_section a = 𝒜.non_member_section a ∪ ℬ.non_member_section a :=
filter_union _ _ _

lemma member_section_union (a : α) (𝒜 ℬ : finset (finset α)) :
  (𝒜 ∪ ℬ).member_section a = 𝒜.member_section a ∪ ℬ.member_section a :=
by simp_rw [member_section, filter_union, image_union]

lemma card_member_section_add_card_non_member_section (a : α) (𝒜 : finset (finset α)) :
  (𝒜.member_section a).card + (𝒜.non_member_section a).card = 𝒜.card :=
begin
  rw [member_section, non_member_section, card_image_of_inj_on,
    filter_card_add_filter_neg_card_eq_card],
  exact (erase_inj_on' _).mono (λ s hs, (mem_filter.1 hs).2),
end

@[simp] lemma member_section_member_section : (𝒜.member_section a).member_section a = ∅ :=
by { ext, simp }

@[simp] lemma member_section_non_member_section : (𝒜.non_member_section a).member_section a = ∅ :=
by { ext, simp }

@[simp] lemma non_member_section_member_section :
  (𝒜.member_section a).non_member_section a = 𝒜.member_section a :=
by { ext, simp }

@[simp] lemma non_member_section_non_member_section :
  (𝒜.non_member_section a).non_member_section a = 𝒜.non_member_section a :=
by { ext, simp }

end finset

open finset

-- The namespace is here to distinguish from other compressions.
namespace down

/-- `a`-down-compressing `𝒜` means removing `a` from the elements of `𝒜` that contain it. -/
def compress (a : α) (𝒜 : finset (finset α)) : finset (finset α) :=
𝒜.member_section a ∪ 𝒜.non_member_section a

localized "notation `𝓓 ` := down.compress" in finset_family

/-- `a` is in the down-compressed family iff it's in the original and its compression is in the
original, or it's not in the original but it's the compression of something in the original. -/
lemma mem_compress : s ∈ 𝓓 a 𝒜 ↔ (insert a s ∈ 𝒜 ∨ s ∈ 𝒜) ∧ a ∉ s :=
by simp_rw [compress, mem_union, mem_member_section, mem_non_member_section, ←or_and_distrib_right]

lemma compress_union (a : α) (𝒜 ℬ : finset (finset α)) : 𝓓 a (𝒜 ∪ ℬ) = 𝓓 a 𝒜 ∪ 𝓓 a ℬ :=
by simp_rw [compress, member_section_union, non_member_section_union, union_union_union_comm]

/-- Down-compressing a family is idempotent. -/
@[simp] lemma compress_idem (a : α) (𝒜 : finset (finset α)) : 𝓓 a (𝓓 a 𝒜) = 𝓓 a 𝒜 :=
(compress_union _ _ _).trans $ by simp [compress]

/-- Down-compressing a family reduces its size. -/
lemma card_compress_le (a : α) (𝒜 : finset (finset α)) : (𝓓 a 𝒜).card ≤ 𝒜.card :=
(card_union_le _ _).trans_eq $ card_member_section_add_card_non_member_section _ _

end down
