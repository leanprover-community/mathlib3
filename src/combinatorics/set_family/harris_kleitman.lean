/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.big_operators.basic
import order.upper_lower

/-!
# Harris-Kleitman inequality

This file proves the Harris-Kleitman inequality. This relates `𝒜.card * ℬ.card` and
`2 ^ card α * (𝒜 ∩ ℬ).card` where `𝒜` and `ℬ` are upward- or downcard-closed finite families of
finsets. This can be interpreted as saying that any two lower sets (resp. any two upper sets)
correlate in the uniform measure.

## Main declarations

* `finset.non_member_subfamily`: `𝒜.non_member_subfamily a` is the subfamily of sets not containing
  `a`.
* `finset.member_subfamily`: `𝒜.member_subfamily a` is the image of the subfamily of sets
  containing `a` under removing `a`.
* `is_lower_set.le_card_inter_finset`: One form of the Harris-Kleitman inequality.

## References

* [D. J. Kleitman, *Families of non-disjoint subsets*][kleitman1966]
-/

open_locale big_operators

variables {α : Type*} [decidable_eq α] {𝒜 ℬ : finset (finset α)} {s : finset α} {a : α}

namespace finset

/-- ELements of `𝒜` that do not contain `a`. -/
def non_member_subfamily (𝒜 : finset (finset α)) (a : α) : finset (finset α) :=
𝒜.filter $ λ s, a ∉ s

/-- Image of the elements of `𝒜` which contain `a` under removing `a`. Finsets that do not contain
`a` such that `insert a s ∈ 𝒜`. -/
def member_subfamily (𝒜 : finset (finset α)) (a : α) : finset (finset α) :=
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

lemma non_member_subfamily_inter (𝒜 ℬ : finset (finset α)) (a : α) :
  (𝒜 ∩ ℬ).non_member_subfamily a = 𝒜.non_member_subfamily a ∩ ℬ.non_member_subfamily a :=
filter_inter_distrib _ _ _

lemma member_subfamily_inter (𝒜 ℬ : finset (finset α)) (a : α) :
  (𝒜 ∩ ℬ).member_subfamily a = 𝒜.member_subfamily a ∩ ℬ.member_subfamily a :=
begin
  unfold member_subfamily,
  rw [filter_inter_distrib, image_inter_of_inj_on _ _ ((erase_inj_on' _).mono _)],
  rw [←coe_union, ←filter_union, coe_filter],
  exact set.inter_subset_right _ _,
end

lemma card_member_subfamily_add_card_non_member_subfamily (𝒜 : finset (finset α)) (a : α) :
  (𝒜.member_subfamily a).card + (𝒜.non_member_subfamily a).card = 𝒜.card :=
begin
  rw [member_subfamily, non_member_subfamily, card_image_of_inj_on,
    filter_card_add_filter_neg_card_eq_card],
  exact (erase_inj_on' _).mono (λ s hs, (mem_filter.1 hs).2),
end

end finset

open finset

lemma is_lower_set.non_member_subfamily (h : is_lower_set (𝒜 : set (finset α))) :
  is_lower_set (𝒜.non_member_subfamily a : set (finset α)) :=
λ s t hts, by { simp_rw [mem_coe, mem_non_member_subfamily], exact and.imp (h hts) (mt $ @hts _) }

lemma is_lower_set.member_subfamily (h : is_lower_set (𝒜 : set (finset α))) :
  is_lower_set (𝒜.member_subfamily a : set (finset α)) :=
begin
  rintro s t hts,
  simp_rw [mem_coe, mem_member_subfamily],
  exact and.imp (h $ insert_subset_insert _ hts) (mt $ @hts _),
end

lemma is_lower_set.member_subfamily_subset_non_member_subfamily
  (h : is_lower_set (𝒜 : set (finset α))) :
  𝒜.member_subfamily a ⊆ 𝒜.non_member_subfamily a :=
λ s, by { rw [mem_member_subfamily, mem_non_member_subfamily],
  exact and.imp_left (h $ subset_insert _ _) }

/-- **Harris-Kleitman inequality**: Any two lower sets of finsets correlate. -/
lemma is_lower_set.le_card_inter_finset'
  (h𝒜 : is_lower_set (𝒜 : set (finset α))) (hℬ : is_lower_set (ℬ : set (finset α)))
  (h𝒜s : ∀ t ∈ 𝒜, t ⊆ s) (hℬs : ∀ t ∈ ℬ, t ⊆ s) :
  𝒜.card * ℬ.card ≤ 2 ^ s.card * (𝒜 ∩ ℬ).card :=
begin
  induction s using finset.induction with a s hs ih generalizing 𝒜 ℬ,
  { simp_rw [subset_empty, ←subset_singleton_iff', subset_singleton_iff] at h𝒜s hℬs,
    obtain rfl | rfl := h𝒜s,
    { simv only [card_empty, empty_inter, mul_zero, zero_mul] },
    obtain rfl | rfl := hℬs,
    { simv only [card_empty, inter_empty, mul_zero, zero_mul] },
    { simv only [card_empty, pow_zero, inter_singleton_of_mem, mem_singleton, card_singleton] } },
  rw [card_insert_of_not_mem hs, ←card_member_subfamily_add_card_non_member_subfamily 𝒜 a,
    ←card_member_subfamily_add_card_non_member_subfamily ℬ a, add_mul, mul_add, mul_add,
    add_comm (_ * _), add_add_add_comm],
  refine (add_le_add_right (mul_add_mul_le_mul_add_mul
    (card_le_of_subset h𝒜.member_subfamily_subset_non_member_subfamily) $
    card_le_of_subset hℬ.member_subfamily_subset_non_member_subfamily) _).trans _,
  rw [←two_mul, pow_succ, mul_assoc],
  have h₀ : ∀ 𝒞 : finset (finset α), (∀ t ∈ 𝒞, t ⊆ insert a s) → ∀ t ∈ 𝒞.non_member_subfamily a,
    t ⊆ s,
  { rintro 𝒞 h𝒞 t ht,
    rw mem_non_member_subfamily at ht,
    exact (subset_insert_iff_of_not_mem ht.2).1 (h𝒞 _ ht.1) },
  have h₁ : ∀ 𝒞 : finset (finset α), (∀ t ∈ 𝒞, t ⊆ insert a s) → ∀ t ∈ 𝒞.member_subfamily a, t ⊆ s,
  { rintro 𝒞 h𝒞 t ht,
    rw mem_member_subfamily at ht,
    exact (subset_insert_iff_of_not_mem ht.2).1 ((subset_insert _ _).trans $ h𝒞 _ ht.1) },
  refine mul_le_mul_left' _ _,
  refine (add_le_add (ih (h𝒜.member_subfamily) (hℬ.member_subfamily) (h₁ _ h𝒜s) $ h₁ _ hℬs) $
    ih (h𝒜.non_member_subfamily) (hℬ.non_member_subfamily) (h₀ _ h𝒜s) $ h₀ _ hℬs).trans_eq _,
  rw [←mul_add, ←member_subfamily_inter, ←non_member_subfamily_inter,
    card_member_subfamily_add_card_non_member_subfamily],
end

variables [fintype α]

/-- **Harris-Kleitman inequality**: Any two lower sets of finsets correlate. -/
lemma is_lower_set.le_card_inter_finset
  (h𝒜 : is_lower_set (𝒜 : set (finset α))) (hℬ : is_lower_set (ℬ : set (finset α))) :
  𝒜.card * ℬ.card ≤ 2 ^ fintype.card α * (𝒜 ∩ ℬ).card :=
h𝒜.le_card_inter_finset' hℬ (λ _ _, subset_univ _) $ λ _ _, subset_univ _

/-- **Harris-Kleitman inequality**: Upper sets and lower sets of finsets anticorrelate. -/
lemma is_upper_set.card_inter_le_finset
  (h𝒜 : is_upper_set (𝒜 : set (finset α))) (hℬ : is_lower_set (ℬ : set (finset α))) :
  2 ^ fintype.card α * (𝒜 ∩ ℬ).card ≤ 𝒜.card * ℬ.card :=
begin
  rw [←is_lower_set_compl, ←coe_compl] at h𝒜,
  have := h𝒜.le_card_inter_finset hℬ,
  rwa [card_compl, fintype.card_finset, tsub_mul, tsub_le_iff_tsub_le, ←mul_tsub, ←card_sdiff
    (inter_subset_right _ _), sdiff_inter_self_right, sdiff_compl, _root_.inf_comm] at this,
end

/-- **Harris-Kleitman inequality**: Lower sets and upper sets of finsets anticorrelate. -/
lemma is_lower_set.card_inter_le_finset
  (h𝒜 : is_lower_set (𝒜 : set (finset α))) (hℬ : is_upper_set (ℬ : set (finset α))) :
  2 ^ fintype.card α * (𝒜 ∩ ℬ).card ≤ 𝒜.card * ℬ.card :=
by { rw [inter_comm, mul_comm 𝒜.card], exact hℬ.card_inter_le_finset h𝒜 }

/-- **Harris-Kleitman inequality**: Any two upper sets of finsets correlate. -/
lemma is_upper_set.le_card_inter_finset
  (h𝒜 : is_upper_set (𝒜 : set (finset α))) (hℬ : is_upper_set (ℬ : set (finset α))) :
  𝒜.card * ℬ.card ≤ 2 ^ fintype.card α * (𝒜 ∩ ℬ).card :=
begin
  rw [←is_lower_set_compl, ←coe_compl] at h𝒜,
  have := h𝒜.card_inter_le_finset hℬ,
  rwa [card_compl, fintype.card_finset, tsub_mul, le_tsub_iff_le_tsub, ←mul_tsub, ←card_sdiff
    (inter_subset_right _ _), sdiff_inter_self_right, sdiff_compl, _root_.inf_comm] at this,
  { exact mul_le_mul_left' (card_le_of_subset $ inter_subset_right _ _) _ },
  { rw ←fintype.card_finset,
    exact mul_le_mul_right' (card_le_univ _) _ }
end
