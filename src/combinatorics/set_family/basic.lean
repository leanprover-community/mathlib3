/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/
import combinatorics.set_family.shadow
import data.fintype.basic
import data.finset.slice

/-!
# Basic definitions for finite sets which are useful for combinatorics

We define a proposition asserting that a set is a set of r-sets.
-/

open finset nat
open_locale finset_family

variables {α : Type*}

namespace finset

variables [decidable_eq α] {𝒜 : finset (finset α)} {A B : finset α} {r k : ℕ}

/-- Iterated shadow of the empty set is empty. -/
lemma iter_shadow_empty (k : ℕ) : shadow^[k] (∅ : finset (finset α)) = ∅ :=
begin
  induction k with k ih,
  { refl },
  { rwa [iterate, shadow_empty] }
end

/-- `B ∈ ∂𝒜` iff `B` is exactly one element less than something from `𝒜` -/
lemma sub_iff_shadow_one : B ∈ ∂𝒜 ↔ ∃ A ∈ 𝒜, B ⊆ A ∧ (A \ B).card = 1 :=
begin
  rw mem_shadow_iff_insert_mem,
  split,
  { rintro ⟨i, ih, inA⟩,
    refine ⟨insert i B, inA, subset_insert _ _, _⟩,
    rw card_sdiff (subset_insert _ _),
    simp [card_insert_of_not_mem ih] },
  { rintro ⟨A, hA, a_h_h⟩,
    rw card_eq_one at a_h_h,
    rcases a_h_h with ⟨subs, j, eq⟩,
    refine ⟨j, _, _⟩,
    { intro a,
      have : j ∉ A \ B := not_mem_sdiff_of_mem_right a,
      apply this,
      rw eq,
      apply mem_singleton_self },
    { rwa [insert_eq j B, ←eq, sdiff_union_of_subset subs] } }
end

/-- `B ∈ ∂^k 𝒜` iff `B` is exactly `k` elements less than something from `𝒜`. -/
lemma sub_iff_shadow_iter {𝒜 : finset (finset α)} {B : finset α} (k : ℕ) :
  B ∈ (shadow^[k] 𝒜) ↔ ∃ A ∈ 𝒜, B ⊆ A ∧ (A \ B).card = k :=
begin
  induction k with k ih generalizing 𝒜 B,
  { simp only [sdiff_eq_empty_iff_subset, function.iterate_zero, id.def, card_eq_zero, exists_prop],
    refine ⟨λ p, ⟨B, p, subset.rfl, subset.rfl⟩, _⟩,
    rintro ⟨A, hA, hAB, hBA⟩,
    rwa subset_antisymm hAB hBA },
  simp only [exists_prop, function.comp_app, function.iterate_succ],
  rw @ih (∂𝒜) B,
  clear ih,
  split,
  { rintro ⟨A, hA, BsubA, card_AdiffB_is_k⟩,
    rw sub_iff_shadow_one at hA,
    rcases hA with ⟨C, CinA, AsubC, card_CdiffA_is_1⟩,
    refine ⟨C, CinA, trans BsubA AsubC, _⟩,
    rw card_sdiff (trans BsubA AsubC),
    rw card_sdiff BsubA at card_AdiffB_is_k,
    rw card_sdiff AsubC at card_CdiffA_is_1,
    rw [←nat.sub_add_cancel (card_le_of_subset AsubC),
        nat.add_sub_assoc (card_le_of_subset BsubA), card_CdiffA_is_1,
        card_AdiffB_is_k, add_comm] },
  { rintro ⟨A, hA, hBA, hAB⟩,
    obtain ⟨i, hi⟩ : (A \ B).nonempty,
    { rw [←finset.card_pos, hAB],
      exact nat.succ_pos _ },
    refine ⟨erase A i, mem_shadow_iff.2 ⟨A, hA, i, sdiff_subset _ _ hi, rfl⟩, _, _⟩,
    { intros t th,
      apply mem_erase_of_ne_of_mem _ (hBA th),
      intro a,
      rw mem_sdiff at hi,
      rw a at th,
      exact hi.2 th },
    rw [erase_sdiff_comm, card_erase_of_mem hi, hAB],
    simp only [succ_sub_succ_eq_sub, tsub_zero] }
end

/-- Everything in the `k`-th shadow is `k` smaller than things in the original. -/
lemma _root_.set.sized.shadow_iter (h𝒜 : (𝒜 : set (finset α)).sized r) :
  ((∂^[k] 𝒜 : finset (finset α)) : set (finset α)).sized (r - k) :=
begin
  intro B,
  rw [mem_coe, sub_iff_shadow_iter],
  rintro ⟨A, hA, hBA, card⟩,
  rw [card_sdiff hBA, h𝒜 hA] at card,
  rw [←card, ←h𝒜 hA, nat.sub_sub_self (card_le_of_subset hBA)],
end

end finset
