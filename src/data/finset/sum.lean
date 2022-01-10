/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.basic
import data.multiset.sum
/-!
# Disjoint sum of finsets

This file defines the disjoint sum of two finsets as `finset (α ⊕ β)`. Beware not to confuse with
the `finset.sum` operation which computes the additive sum.

## Main declarations

* `finset.disj_sum`: `s.disj_sum t` is the disjoint sum of `s` and `t`.
-/

namespace finset
variables {α β : Type*} (s : finset α) (t : finset β)

/-- Disjoint sum of finsets. -/
def disj_sum : finset (α ⊕ β) := ⟨s.1.disj_sum t.1, s.2.disj_sum t.2⟩

@[simp] lemma val_disj_sum : (s.disj_sum t).1 = s.1.disj_sum t.1 := rfl

@[simp] lemma zero_disj_sum : (∅ : finset α).disj_sum t = t.map embedding_inr := rfl
@[simp] lemma disj_sum_zero : s.disj_sum (∅ : finset β) = s.map embedding_inl := rfl

@[simp] lemma card_disj_sum : (s.disj_sum t).card = s.card + t.card := multiset.card_disj_sum

variables {s t} {a : α} {b : β} {x : α ⊕ β}

lemma mem_disj_sum : x ∈ s.disj_sum t ↔ (∃ a, a ∈ s ∧ inl a = x) ∨ ∃ b, b ∈ t ∧ inr b = x :=
multiset.mem_disj_sum

@[simp] lemma card_disj_sum : (s.disj_sum t).card = s.card + t.card :=
by rw [disj_sum, card_add, card_map, card_map]

@[simp] lemma inl_mem_disj_sum : inl a ∈ s.disj_sum t ↔ a ∈ s := multiset.inl_mem_disj_sum
@[simp] lemma inr_mem_disj_sum : inr b ∈ s.disj_sum t ↔ b ∈ t := multiset.inr_mem_disj_sum

lemma disj_sum_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁.disj_sum t₁ ≤ s₂.disj_sum t₂ :=
add_le_add (map_le_map hs) (map_le_map ht)

lemma disj_sum_strict_mono (hs : s₁ ⊂ s₂) (ht : t₁ ⊂ t₂) : s₁.disj_sum t₁ < s₂.disj_sum t₂ :=
add_lt_add (map_lt_map hs) (map_lt_map ht)

lemma disj_sum_mono_left (hs : s₁ ≤ s₂) (t : finset β) : s₁.disj_sum t ≤ s₂.disj_sum t :=
add_le_add_right (map_le_map hs) _

lemma disj_sum_mono_right (s : finset α) :
  monotone (s.disj_sum : multiset β → multiset (α ⊕ β)) :=
λ t₁ t₂ ht, add_le_add_left (map_le_map ht) _

end finset
