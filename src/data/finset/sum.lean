/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.multiset.sum
import data.finset.card

/-!
# Disjoint sum of finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the disjoint sum of two finsets as `finset (α ⊕ β)`. Beware not to confuse with
the `finset.sum` operation which computes the additive sum.

## Main declarations

* `finset.disj_sum`: `s.disj_sum t` is the disjoint sum of `s` and `t`.
-/

open function multiset sum

namespace finset
variables {α β : Type*} (s : finset α) (t : finset β)

/-- Disjoint sum of finsets. -/
def disj_sum : finset (α ⊕ β) := ⟨s.1.disj_sum t.1, s.2.disj_sum t.2⟩

@[simp] lemma val_disj_sum : (s.disj_sum t).1 = s.1.disj_sum t.1 := rfl

@[simp] lemma empty_disj_sum : (∅ : finset α).disj_sum t = t.map embedding.inr :=
val_inj.1 $ multiset.zero_disj_sum _

@[simp] lemma disj_sum_empty : s.disj_sum (∅ : finset β) = s.map embedding.inl :=
val_inj.1 $ multiset.disj_sum_zero _

@[simp] lemma card_disj_sum : (s.disj_sum t).card = s.card + t.card := multiset.card_disj_sum _ _

lemma disjoint_map_inl_map_inr : disjoint (s.map embedding.inl) (t.map embedding.inr) :=
by { simp_rw [disjoint_left, mem_map], rintro x ⟨a, _, rfl⟩ ⟨b, _, ⟨⟩⟩ }

@[simp]
lemma map_inl_disj_union_map_inr :
  (s.map embedding.inl).disj_union (t.map embedding.inr) (disjoint_map_inl_map_inr _ _) =
    s.disj_sum t := rfl

variables {s t} {s₁ s₂ : finset α} {t₁ t₂ : finset β} {a : α} {b : β} {x : α ⊕ β}

lemma mem_disj_sum : x ∈ s.disj_sum t ↔ (∃ a, a ∈ s ∧ inl a = x) ∨ ∃ b, b ∈ t ∧ inr b = x :=
multiset.mem_disj_sum

@[simp] lemma inl_mem_disj_sum : inl a ∈ s.disj_sum t ↔ a ∈ s := inl_mem_disj_sum
@[simp] lemma inr_mem_disj_sum : inr b ∈ s.disj_sum t ↔ b ∈ t := inr_mem_disj_sum

lemma disj_sum_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁.disj_sum t₁ ⊆ s₂.disj_sum t₂ :=
val_le_iff.1 $ disj_sum_mono (val_le_iff.2 hs) (val_le_iff.2 ht)

lemma disj_sum_mono_left (t : finset β) : monotone (λ s : finset α, s.disj_sum t) :=
λ s₁ s₂ hs, disj_sum_mono hs subset.rfl

lemma disj_sum_mono_right (s : finset α) : monotone (s.disj_sum : finset β → finset (α ⊕ β)) :=
λ t₁ t₂, disj_sum_mono subset.rfl

lemma disj_sum_ssubset_disj_sum_of_ssubset_of_subset (hs : s₁ ⊂ s₂) (ht : t₁ ⊆ t₂) :
  s₁.disj_sum t₁ ⊂ s₂.disj_sum t₂ :=
val_lt_iff.1 $ disj_sum_lt_disj_sum_of_lt_of_le (val_lt_iff.2 hs) (val_le_iff.2 ht)

lemma disj_sum_ssubset_disj_sum_of_subset_of_ssubset (hs : s₁ ⊆ s₂) (ht : t₁ ⊂ t₂) :
  s₁.disj_sum t₁ ⊂ s₂.disj_sum t₂ :=
val_lt_iff.1 $ disj_sum_lt_disj_sum_of_le_of_lt (val_le_iff.2 hs) (val_lt_iff.2 ht)

lemma disj_sum_strict_mono_left (t : finset β) : strict_mono (λ s : finset α, s.disj_sum t) :=
λ s₁ s₂ hs, disj_sum_ssubset_disj_sum_of_ssubset_of_subset hs subset.rfl

lemma disj_sum_strict_mono_right (s : finset α) :
  strict_mono (s.disj_sum : finset β → finset (α ⊕ β)) :=
λ s₁ s₂, disj_sum_ssubset_disj_sum_of_subset_of_ssubset subset.rfl

end finset
