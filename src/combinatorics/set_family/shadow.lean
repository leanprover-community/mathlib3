/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
import data.finset.lattice

/-!
# Shadows

This file defines shadows of a set family. The shadow of a set family is the set family of sets we
get by removing any element from any set of the original family. If one pictures `finset α` as a big
hypercube (each dimension being membership of a given element), then taking the shadow corresponds
to projecting each finset down once in all available directions.

## Main definitions

The `shadow` of a set family is everything we can get by removing an element from each set.

## Notation

`∂ 𝒜` is notation for `shadow 𝒜`. It is situated in locale `finset_family`.

We also maintain the convention that `a, b : α` are elements of the ground type, `A, B : finset α`
are finsets, and `𝒜, ℬ : finset (finset α)` are finset families.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, set family
-/

open finset nat

variables {α : Type*}

/-!
### Shadows

The shadow of a set family is everything we can get by removing an element
from each set.

This section develops the introductory theory of shadows, with some lemmas on
iterated shadows as well.
-/

variables [decidable_eq α] {𝒜 : finset (finset α)} {A B : finset α} {a : α}

/-- The shadow of a set family `𝒜` is all sets we can get by removing one element
from any set in `𝒜`, and the (`k` times) iterated shadow is all sets we can get
by removing k elements from any set in `𝒜`. -/
def shadow (𝒜 : finset (finset α)) : finset (finset α) := 𝒜.sup (λ A, A.image (erase A))

localized "notation `∂ `:90 := shadow" in finset_family

/-- The shadow of the empty set is empty. -/
lemma shadow_empty : ∂ (∅ : finset (finset α)) = ∅ := rfl

/-- The shadow is monotone. -/
lemma shadow_monotone : monotone (shadow : finset (finset α) → finset (finset α)) :=
λ 𝒜 ℬ, sup_mono

/-- `A` is in the shadow of `𝒜` iff there is an `B ∈ 𝒜` from which we can remove one element to
get `A`. -/
lemma mem_shadow_iff_eq_erase : A ∈ ∂ 𝒜 ↔ ∃ B ∈ 𝒜, ∃ a ∈ B, erase B a = A :=
by simp only [shadow, mem_sup, mem_image]

lemma erase_mem_shadow (hA : A ∈ 𝒜) (ha : a ∈ A) : erase A a ∈ ∂ 𝒜 :=
mem_shadow_iff_eq_erase.2 ⟨A, hA, a, ha, rfl⟩

/-- `B` is in the shadow of `𝒜` iff we can an element to it so that the resulting finset is in `𝒜`.
-/
lemma mem_shadow_iff_insert_mem : A ∈ ∂ 𝒜 ↔ ∃ a ∉ A, insert a A ∈ 𝒜 :=
begin
  refine mem_shadow_iff_eq_erase.trans ⟨_, _⟩,
  { rintro ⟨A, hA, a, ha, rfl⟩,
    refine ⟨a, not_mem_erase a A, _⟩,
    rwa insert_erase ha },
  { rintro ⟨a, ha, hA⟩,
    exact ⟨insert a A, hA, a, mem_insert_self _ _, erase_insert ha⟩ }
end

/-- `A ∈ ∂𝒜` iff `A` is exactly one element less than something from `𝒜` -/
lemma mem_shadow_iff_exists_mem_card_add_one :
  A ∈ ∂ 𝒜 ↔ ∃ B ∈ 𝒜, A ⊆ B ∧ B.card = A.card + 1 :=
begin
  refine mem_shadow_iff_insert_mem.trans ⟨_, _⟩,
  { rintro ⟨a, ha, hA⟩,
    exact ⟨insert a A, hA, subset_insert _ _, card_insert_of_not_mem ha⟩ },
  { rintro ⟨B, hB, hAB, h⟩,
    obtain ⟨a, ha⟩ : ∃ a, B \ A = {a} :=
      card_eq_one.1 (by rw [card_sdiff hAB, h, add_tsub_cancel_left]),
    exact ⟨a, λ haB,
      not_mem_sdiff_of_mem_right haB ((ha.ge : _ ⊆ _) $ mem_singleton_self a),
      by rwa [insert_eq a A, ←ha, sdiff_union_of_subset hAB]⟩ }
end

/-- Being in the shadow of `𝒜` means we have a superset in `𝒜`. -/
lemma exists_subset_of_mem_shadow (hA : A ∈ ∂𝒜) : ∃ B ∈ 𝒜, A ⊆ B :=
let ⟨B, hB, hAB⟩ :=  mem_shadow_iff_exists_mem_card_add_one.1 hA in ⟨B, hB, hAB.1⟩

/-- `B ∈ ∂^k 𝒜` iff `B` is exactly `k` elements less than something in `𝒜`. -/
lemma mem_shadow_iff_exists_mem_card_add {k : ℕ} :
  A ∈ (shadow^[k] 𝒜) ↔ ∃ B ∈ 𝒜, A ⊆ B ∧ B.card = A.card + k :=
begin
  induction k with k ih generalizing 𝒜 A,
  { refine ⟨λ hA, ⟨A, hA, subset.refl _, rfl⟩, _⟩,
    rintro ⟨B, hB, hAB, hcard⟩,
    rwa eq_of_subset_of_card_le hAB hcard.le },
  simp only [exists_prop, function.comp_app, function.iterate_succ],
  refine ih.trans _,
  clear ih,
  split,
  { rintro ⟨B, hB, hAB, hcardAB⟩,
    obtain ⟨C, hC, hBC, hcardBC⟩ := mem_shadow_iff_exists_mem_card_add_one.1 hB,
    refine ⟨C, hC, hAB.trans hBC, _⟩,
    rw [hcardBC, hcardAB],
    refl },
  { rintro ⟨B, hB, hAB, hcard⟩,
    obtain ⟨C, hAC, hCB, hC⟩ := finset.exists_intermediate_set k _ hAB,
    rw add_comm at hC,
    refine ⟨C, mem_shadow_iff_exists_mem_card_add_one.2 ⟨B, hB, hCB, _⟩, hAC, hC⟩,
    rw [hcard, hC],
    refl,
    { rw [add_comm, hcard],
      exact le_succ _ } }
end
