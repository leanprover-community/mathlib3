/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.multiset.nodup

/-!
# Disjoint sum of multisets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the disjoint sum of two multisets as `multiset (α ⊕ β)`. Beware not to confuse
with the `multiset.sum` operation which computes the additive sum.

## Main declarations

* `multiset.disj_sum`: `s.disj_sum t` is the disjoint sum of `s` and `t`.
-/

open sum

namespace multiset
variables {α β : Type*} (s : multiset α) (t : multiset β)

/-- Disjoint sum of multisets. -/
def disj_sum : multiset (α ⊕ β) := s.map inl + t.map inr

@[simp] lemma zero_disj_sum : (0 : multiset α).disj_sum t = t.map inr := zero_add _
@[simp] lemma disj_sum_zero : s.disj_sum (0 : multiset β) = s.map inl := add_zero _

@[simp] lemma card_disj_sum : (s.disj_sum t).card = s.card + t.card :=
by rw [disj_sum, card_add, card_map, card_map]

variables {s t} {s₁ s₂ : multiset α} {t₁ t₂ : multiset β} {a : α} {b : β} {x : α ⊕ β}

lemma mem_disj_sum : x ∈ s.disj_sum t ↔ (∃ a, a ∈ s ∧ inl a = x) ∨ ∃ b, b ∈ t ∧ inr b = x :=
by simp_rw [disj_sum, mem_add, mem_map]

@[simp] lemma inl_mem_disj_sum : inl a ∈ s.disj_sum t ↔ a ∈ s :=
begin
  rw [mem_disj_sum, or_iff_left],
  simp only [exists_eq_right],
  rintro ⟨b, _, hb⟩,
  exact inr_ne_inl hb,
end

@[simp] lemma inr_mem_disj_sum : inr b ∈ s.disj_sum t ↔ b ∈ t :=
begin
  rw [mem_disj_sum, or_iff_right],
  simp only [exists_eq_right],
  rintro ⟨a, _, ha⟩,
  exact inl_ne_inr ha,
end

lemma disj_sum_mono (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) : s₁.disj_sum t₁ ≤ s₂.disj_sum t₂ :=
add_le_add (map_le_map hs) (map_le_map ht)

lemma disj_sum_mono_left (t : multiset β) : monotone (λ s : multiset α, s.disj_sum t) :=
λ s₁ s₂ hs, add_le_add_right (map_le_map hs) _

lemma disj_sum_mono_right (s : multiset α) :
  monotone (s.disj_sum : multiset β → multiset (α ⊕ β)) :=
λ t₁ t₂ ht, add_le_add_left (map_le_map ht) _

lemma disj_sum_lt_disj_sum_of_lt_of_le (hs : s₁ < s₂) (ht : t₁ ≤ t₂) :
  s₁.disj_sum t₁ < s₂.disj_sum t₂ :=
add_lt_add_of_lt_of_le (map_lt_map hs) (map_le_map ht)

lemma disj_sum_lt_disj_sum_of_le_of_lt (hs : s₁ ≤ s₂) (ht : t₁ < t₂) :
  s₁.disj_sum t₁ < s₂.disj_sum t₂ :=
add_lt_add_of_le_of_lt (map_le_map hs) (map_lt_map ht)

lemma disj_sum_strict_mono_left (t : multiset β) : strict_mono (λ s : multiset α, s.disj_sum t) :=
λ s₁ s₂ hs, disj_sum_lt_disj_sum_of_lt_of_le hs le_rfl

lemma disj_sum_strict_mono_right (s : multiset α) :
  strict_mono (s.disj_sum : multiset β → multiset (α ⊕ β)) :=
λ s₁ s₂, disj_sum_lt_disj_sum_of_le_of_lt le_rfl

protected lemma nodup.disj_sum (hs : s.nodup) (ht : t.nodup) : (s.disj_sum t).nodup :=
begin
  refine ((hs.map inl_injective).add_iff $ ht.map inr_injective).2 (λ x hs ht, _),
  rw multiset.mem_map at hs ht,
  obtain ⟨a, _, rfl⟩ := hs,
  obtain ⟨b, _, h⟩ := ht,
  exact inr_ne_inl h,
end

end multiset
