/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.pointwise

/-!
# Ruzsa's covering lemma

This file proves the Ruzsa covering lemma. This says that, for `s`, `t` finsets, we can cover `s`
with at most `(s + t).card/t.card` copies of `t - t`.

## TODO

Merge this file with other prerequisites to Freiman's theorem once we have them.
-/

open nat
open_locale pointwise

variables {α β : Type*}

namespace finset

section
variables [decidable_eq α] [left_cancel_semigroup α] {s t : finset α}

@[to_additive]
lemma card_mul (h : (s : set α).pairwise_disjoint (• t)) : (s * t).card = s.card * t.card :=
begin
  rw [←image_mul_prod, product_eq_bUnion, bUnion_image],
  simp_rw show ∀ a, (t.image $ λ b, (a, b)).image (λ x : α × α, x.fst * x.snd) = a • t, from
    λ a, image_image,
  rw [card_bUnion h, sum_const_nat (λ _ _, _)],
  exact card_image_of_injective _ (mul_right_injective _),
end

end

section mul_action
variables [group α] [decidable_eq β] [mul_action α β] {s : finset β} (a : α) {b : β}

@[simp, to_additive] lemma smul_mem_smul_iff : a • b ∈ a • s ↔ b ∈ s := by simp [mem_smul_finset]

@[to_additive] lemma inv_smul_mem_iff : a⁻¹ • b ∈ s ↔ b ∈ a • s :=
by rw [←smul_mem_smul_iff a, smul_inv_smul]

@[to_additive] lemma mem_inv_smul_finset_iff : b ∈ a⁻¹ • s ↔ a • b ∈ s :=
by rw [←smul_mem_smul_iff a, smul_inv_smul]

end mul_action

end finset

namespace finset
variables [decidable_eq α] [linear_ordered_semiring β]

/-- **Ruzsa's covering lemma**. -/
lemma exists_subset_add_sub [add_comm_group α] {s t : finset α} {r : β} (ht : t.nonempty)
  (h : ↑((s + t).card) ≤ t.card • r) :
  ∃ u : finset α, ↑(u.card) ≤ r ∧ s ⊆ u + t - t :=
begin
  haveI : Π u, decidable ((u : set α).pairwise_disjoint (+ᵥ t)) := λ u, classical.dec _,
  set C := s.powerset.filter (λ u, (u : set α).pairwise_disjoint (+ᵥ t)),
  obtain ⟨u, hu, hCmax⟩ := C.exists_maximal
    (filter_nonempty_iff.2 ⟨∅, empty_mem_powerset _, set.pairwise_disjoint_empty⟩),
  rw [mem_filter, mem_powerset] at hu,
  refine ⟨u, _, λ a ha, _⟩,
  { -- TODO: `smul_le_smul_iff_of_pos` ought to be useful here
    refine le_of_mul_le_mul_left _ (cast_pos.2 ht.card_pos),
    rw [←cast_mul, mul_comm, ←card_add hu.2, ←_root_.nsmul_eq_mul],
    exact (cast_le.2 $ card_le_of_subset $ add_subset_add_right hu.1).trans h },
  rw add_sub_assoc,
  by_cases hau : a ∈ u,
  { exact subset_add_left _ ht.zero_mem_sub hau },
  by_cases H : ∀ b ∈ u, disjoint (a +ᵥ t) (b +ᵥ t),
  { refine (hCmax _ _ $ ssubset_insert hau).elim,
    rw [mem_filter, mem_powerset, insert_subset, coe_insert],
    exact ⟨⟨ha, hu.1⟩, hu.2.insert $ λ b hb _, H _ hb⟩ },
  push_neg at H,
  simp_rw [not_disjoint_iff, ←neg_vadd_mem_iff] at H,
  obtain ⟨b, hb, c, hc₁, hc₂⟩ := H,
  exact mem_add.2 ⟨_, _, hb, mem_sub.2 ⟨_, _, hc₂, hc₁, by simp [sub_eq_add_neg a b]⟩, by simp⟩,
end

/-- **Ruzsa's covering lemma**. -/
@[to_additive] lemma exists_subset_mul_div [comm_group α] {s t : finset α} {r : β} (ht : t.nonempty)
  (h : ↑((s * t).card) ≤ t.card • r) :
  ∃ u : finset α, ↑(u.card) ≤ r ∧ s ⊆ u * t / t :=
begin
  haveI : Π u, decidable ((u : set α).pairwise_disjoint (• t)) := λ u, classical.dec _,
  set C := s.powerset.filter (λ u, (u : set α).pairwise_disjoint (• t)),
  obtain ⟨u, hu, hCmax⟩ := C.exists_maximal
    (filter_nonempty_iff.2 ⟨∅, empty_mem_powerset _, set.pairwise_disjoint_empty⟩),
  rw [mem_filter, mem_powerset] at hu,
  refine ⟨u, _, λ a ha, _⟩,
  { -- TODO: `smul_le_smul_iff_of_pos` ought to be useful here
    refine le_of_mul_le_mul_left _ (cast_pos.2 ht.card_pos),
    rw [←cast_mul, mul_comm, ←card_mul hu.2, ←_root_.nsmul_eq_mul],
    exact (cast_le.2 $ card_le_of_subset $ mul_subset_mul_right hu.1).trans h },
  rw mul_div_assoc,
  by_cases hau : a ∈ u,
  { exact subset_mul_left _ ht.one_mem_div hau },
  by_cases H : ∀ b ∈ u, disjoint (a • t) (b • t),
  { refine (hCmax _ _ $ ssubset_insert hau).elim,
    rw [mem_filter, mem_powerset, insert_subset, coe_insert],
    exact ⟨⟨ha, hu.1⟩, hu.2.insert $ λ b hb _, H _ hb⟩ },
  push_neg at H,
  simp_rw [not_disjoint_iff, ←inv_smul_mem_iff] at H,
  obtain ⟨b, hb, c, hc₁, hc₂⟩ := H,
  exact mem_mul.2 ⟨_, _, hb, mem_div.2 ⟨_, _, hc₂, hc₁, by simp [div_eq_mul_inv a b]⟩, by simp⟩,
end

end finset
