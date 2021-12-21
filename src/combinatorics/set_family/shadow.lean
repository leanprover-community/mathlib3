/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
import data.finset.lattice
import logic.function.iterate

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

We also maintain the convention that `a, b : α` are elements of the ground type, `s, t : finset α`
are finsets, and `𝒜, ℬ : finset (finset α)` are finset families.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, set family
-/

open finset nat

variables {α : Type*}

namespace finset
variables [decidable_eq α] {𝒜 : finset (finset α)} {s t : finset α} {a : α} {k : ℕ}

/-- The shadow of a set family `𝒜` is all sets we can get by removing one element from any set in
`𝒜`, and the (`k` times) iterated shadow (`shadow^[k]`) is all sets we can get by removing `k`
elements from any set in `𝒜`. -/
def shadow (𝒜 : finset (finset α)) : finset (finset α) := 𝒜.sup (λ s, s.image (erase s))

localized "notation `∂ `:90 := finset.shadow" in finset_family

/-- The shadow of the empty set is empty. -/
@[simp] lemma shadow_empty : ∂ (∅ : finset (finset α)) = ∅ := rfl

/-- The shadow is monotone. -/
@[mono] lemma shadow_monotone : monotone (shadow : finset (finset α) → finset (finset α)) :=
λ 𝒜 ℬ, sup_mono

/-- `s` is in the shadow of `𝒜` iff there is an `t ∈ 𝒜` from which we can remove one element to
get `s`. -/
lemma mem_shadow_iff : s ∈ ∂ 𝒜 ↔ ∃ t ∈ 𝒜, ∃ a ∈ t, erase t a = s :=
by simp only [shadow, mem_sup, mem_image]

lemma erase_mem_shadow (hs : s ∈ 𝒜) (ha : a ∈ s) : erase s a ∈ ∂ 𝒜 :=
mem_shadow_iff.2 ⟨s, hs, a, ha, rfl⟩

/-- `t` is in the shadow of `𝒜` iff we can add an element to it so that the resulting finset is in
`𝒜`. -/
lemma mem_shadow_iff_insert_mem : s ∈ ∂ 𝒜 ↔ ∃ a ∉ s, insert a s ∈ 𝒜 :=
begin
  refine mem_shadow_iff.trans ⟨_, _⟩,
  { rintro ⟨s, hs, a, ha, rfl⟩,
    refine ⟨a, not_mem_erase a s, _⟩,
    rwa insert_erase ha },
  { rintro ⟨a, ha, hs⟩,
    exact ⟨insert a s, hs, a, mem_insert_self _ _, erase_insert ha⟩ }
end

/-- `s ∈ ∂ 𝒜` iff `s` is exactly one element less than something from `𝒜` -/
lemma mem_shadow_iff_exists_mem_card_add_one :
  s ∈ ∂ 𝒜 ↔ ∃ t ∈ 𝒜, s ⊆ t ∧ t.card = s.card + 1 :=
begin
  refine mem_shadow_iff_insert_mem.trans ⟨_, _⟩,
  { rintro ⟨a, ha, hs⟩,
    exact ⟨insert a s, hs, subset_insert _ _, card_insert_of_not_mem ha⟩ },
  { rintro ⟨t, ht, hst, h⟩,
    obtain ⟨a, ha⟩ : ∃ a, t \ s = {a} :=
      card_eq_one.1 (by rw [card_sdiff hst, h, add_tsub_cancel_left]),
    exact ⟨a, λ hat,
      not_mem_sdiff_of_mem_right hat ((ha.ge : _ ⊆ _) $ mem_singleton_self a),
      by rwa [insert_eq a s, ←ha, sdiff_union_of_subset hst]⟩ }
end

/-- Being in the shadow of `𝒜` means we have a superset in `𝒜`. -/
lemma exists_subset_of_mem_shadow (hs : s ∈ ∂ 𝒜) : ∃ t ∈ 𝒜, s ⊆ t :=
let ⟨t, ht, hst⟩ := mem_shadow_iff_exists_mem_card_add_one.1 hs in ⟨t, ht, hst.1⟩

/-- `t ∈ ∂^k 𝒜` iff `t` is exactly `k` elements less than something in `𝒜`. -/
lemma mem_shadow_iff_exists_mem_card_add :
  s ∈ (∂^[k]) 𝒜 ↔ ∃ t ∈ 𝒜, s ⊆ t ∧ t.card = s.card + k :=
begin
  induction k with k ih generalizing 𝒜 s,
  { refine ⟨λ hs, ⟨s, hs, subset.refl _, rfl⟩, _⟩,
    rintro ⟨t, ht, hst, hcard⟩,
    rwa eq_of_subset_of_card_le hst hcard.le },
  simp only [exists_prop, function.comp_app, function.iterate_succ],
  refine ih.trans _,
  clear ih,
  split,
  { rintro ⟨t, ht, hst, hcardst⟩,
    obtain ⟨u, hu, htu, hcardtu⟩ := mem_shadow_iff_exists_mem_card_add_one.1 ht,
    refine ⟨u, hu, hst.trans htu, _⟩,
    rw [hcardtu, hcardst],
    refl },
  { rintro ⟨t, ht, hst, hcard⟩,
    obtain ⟨u, hsu, hut, hu⟩ := finset.exists_intermediate_set k
      (by { rw [add_comm, hcard], exact le_succ _ }) hst,
    rw add_comm at hu,
    refine ⟨u, mem_shadow_iff_exists_mem_card_add_one.2 ⟨t, ht, hut, _⟩, hsu, hu⟩,
    rw [hcard, hu],
    refl }
end

end finset
