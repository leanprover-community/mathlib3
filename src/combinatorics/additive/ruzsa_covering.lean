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

section monoid
variables {α β : Type*} [monoid α] [mul_action α β] {a : α}

open function

namespace units

@[to_additive] protected lemma smul_left_injective (a : αˣ) : injective ((•) a : β → β) :=
λ b c h, by simpa only [inv_smul_smul] using congr_arg (has_scalar.smul a⁻¹) h

@[simp, to_additive] protected lemma smul_left_inj (a : αˣ) {b c : β} : a • b = a • c ↔ b = c :=
a.smul_left_injective.eq_iff

end units

@[to_additive] protected lemma is_unit.smul_left_injective (h : is_unit a) :
  injective ((•) a : β → β) :=
h.unit.smul_left_injective

@[to_additive] protected lemma is_unit.smul_left_inj (h : is_unit a) {b c : β} :
  a • b = a • c ↔ b = c :=
h.unit.smul_left_inj

end monoid

section group
variables {α β : Type*} [group α] [mul_action α β] {a : α} {b c : β}

open function

@[to_additive] lemma smul_left_injective'' (a : α) : injective ((•) a : β → β) :=
(group.is_unit _).smul_left_injective

@[simp, to_additive] lemma smul_left_inj : a • b = a • c ↔ b = c := (group.is_unit _).smul_left_inj

end group

namespace finset
variables {α β : Type*}

open_locale pointwise

section mul_action
variables [group α] [decidable_eq β] [mul_action α β] {s : finset β} (a : α) {b : β}

@[simp, to_additive] lemma smul_mem_smul_iff : a • b ∈ a • s ↔ b ∈ s :=
(smul_left_injective'' _).mem_finset_image

@[to_additive] lemma inv_smul_mem_iff : a⁻¹ • b ∈ s ↔ b ∈ a • s :=
by rw [←smul_mem_smul_iff a, smul_inv_smul]

@[to_additive] lemma mem_inv_smul_finset_iff : b ∈ a⁻¹ • s ↔ a • b ∈ s :=
by rw [←smul_mem_smul_iff a, smul_inv_smul]

end mul_action

end finset

open_locale pointwise

variables {α : Type*}

namespace finset
variables [decidable_eq α] [comm_group α] (s : finset α) {t : finset α}

/-- **Ruzsa's covering lemma**. -/
@[to_additive "**Ruzsa's covering lemma**"]
lemma exists_subset_mul_div (ht : t.nonempty) :
  ∃ u : finset α, u.card * t.card ≤ (s * t).card ∧ s ⊆ u * t / t :=
begin
  haveI : Π u, decidable ((u : set α).pairwise_disjoint (• t)) := λ u, classical.dec _,
  set C := s.powerset.filter (λ u, (u : set α).pairwise_disjoint (• t)),
  obtain ⟨u, hu, hCmax⟩ := C.exists_maximal
    (filter_nonempty_iff.2 ⟨∅, empty_mem_powerset _, set.pairwise_disjoint_empty⟩),
  rw [mem_filter, mem_powerset] at hu,
  refine ⟨u, (card_mul_iff.2 $ pairwise_disjoint_smul_iff.1 hu.2).ge.trans
    (card_le_of_subset $ mul_subset_mul_right hu.1), λ a ha, _⟩,
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
