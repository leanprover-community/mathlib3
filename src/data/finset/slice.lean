/-
Copyright (c) 2021 Bhavik Mehta, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
import data.fintype.basic
import order.antichain
import order.polytope.grade

/-!
# `n`-sets and slice

This file defines the `n`-th slice of a set family and provides a way to say that a set family is
made of `n`-sets.

An `n`-set is a finset of cardinality `n` (aka of *size* `n`). The `n`-th slice of a set family is
the set family made of its `n`-sets.

## Main declarations

* `set.sized`: `s.sized n` means that `s` only contains `n`-sets.
* `finset.slice`: `s.slice n` is the set of `n`-sets in `s`.

## Notation

`s # n` is notation for `s.slice n` in locale `finset_family`.
-/

open finset nat

variables {α : Type*}

namespace set
section preorder
variables [preorder α] [order_bot α] [grade_order α] {s t : set α} {n : ℕ}

/-! ### Families of `n`-sets -/

/-- `sized n s` means that every element in `s` has grade `n`. -/
def sized (n : ℕ) (s : set α) : Prop := ∀ ⦃a⦄, a ∈ s → grade a = n

lemma sized.mono (h : s ⊆ t) (ht : t.sized n) : s.sized n := λ a ha, ht $ h ha

lemma sized_union : (s ∪ t).sized n ↔ s.sized n ∧ t.sized n :=
⟨λ hs, ⟨hs.mono $ subset_union_left _ _, hs.mono $ subset_union_right _ _⟩,
  λ hs a ha, ha.elim (λ h, hs.1 h) $ λ h, hs.2 h⟩

alias sized_union ↔ _ set.sized.union

attribute [protected] set.sized.union

end preorder

section partial_order
variables [partial_order α] [order_bot α] [grade_order α] {s t : set α} {n : ℕ}

protected lemma sized.is_antichain (hs : s.sized n) : is_antichain (≤) s :=
λ a ha b hb h hab, (grade_strict_mono $ hab.lt_of_ne h).ne $ (hs ha).trans (hs hb).symm

end partial_order
end set

namespace finset
section sized
variables [fintype α] {𝒜 : finset (finset α)} {s : finset α} {n : ℕ}

lemma subset_powerset_len_univ_iff : 𝒜 ⊆ powerset_len n univ ↔ (𝒜 : set (finset α)).sized n :=
forall_congr $ λ s, by rw [mem_powerset_len_univ_iff, finset.grade, mem_coe]

alias subset_powerset_len_univ_iff  ↔ _ set.sized.subset_powerset_len_univ

lemma _root_.set.sized.card_le (h𝒜 : (𝒜 : set (finset α)).sized n) :
  card 𝒜 ≤ (fintype.card α).choose n :=
begin
  rw [fintype.card, ←card_powerset_len],
  exact card_le_of_subset h𝒜.subset_powerset_len_univ,
end

end sized

/-! ### Slices -/

section slice
variables [preorder α] [order_bot α] [grade_order α] {s : finset α} {a b c : α} {m n : ℕ}

/-- The `n`-th slice of a set family is the subset of its elements which have cardinality `n`. -/
def slice (s : finset α) (n : ℕ) : finset α := s.filter (λ a, grade a = n)

localized "infix ` # `:90 := finset.slice" in finset_family

/-- `a` is in the `n`-th slice of `s` iff it's in `s` and has grade `n`. -/
lemma mem_slice : a ∈ s # n ↔ a ∈ s ∧ grade a = n := mem_filter

/-- The `n`-th slice of `s` is a subset of `s`. -/
lemma slice_subset : s # n ⊆ s := filter_subset _ _

/-- Everything in the `n`-th slice of `s` has size `n`. -/
lemma sized_slice : (s # n : set α).sized n := λ _, and.right ∘ mem_slice.mp

lemma eq_of_mem_slice (h₁ : a ∈ s # m) (h₂ : a ∈ s # n) : m = n :=
(sized_slice h₁).symm.trans $ sized_slice h₂

/-- Elements in distinct slices must be distinct. -/
lemma ne_of_mem_slice (ha : a ∈ s # m) (hb : b ∈ s # n) : m ≠ n → a ≠ b :=
mt $ λ h, (sized_slice ha).symm.trans ((congr_arg grade h).trans (sized_slice hb))

variables [decidable_eq α]

lemma pairwise_disjoint_slice : (set.univ : set ℕ).pairwise_disjoint (slice s) :=
λ m _ n _ hmn, disjoint_filter.2 $ λ s hs hm hn, hmn $ hm.symm.trans hn

end slice
end finset
