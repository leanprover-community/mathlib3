/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.sum.order
import order.locally_finite

/-!
# Finite intervals in a disjoint union

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the `locally_finite_order` instance for the disjoint sum of two orders.

## TODO

Do the same for the lexicographic sum of orders.
-/

open function sum

namespace finset
variables {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type*}

section sum_lift₂
variables (f f₁ g₁ : α₁ → β₁ → finset γ₁) (g f₂ g₂ : α₂ → β₂ → finset γ₂)

/-- Lifts maps `α₁ → β₁ → finset γ₁` and `α₂ → β₂ → finset γ₂` to a map
`α₁ ⊕ α₂ → β₁ ⊕ β₂ → finset (γ₁ ⊕ γ₂)`. Could be generalized to `alternative` functors if we can
make sure to keep computability and universe polymorphism. -/
@[simp] def sum_lift₂ : Π (a : α₁ ⊕ α₂) (b : β₁ ⊕ β₂), finset (γ₁ ⊕ γ₂)
| (inl a) (inl b) := (f a b).map embedding.inl
| (inl a) (inr b) := ∅
| (inr a) (inl b) := ∅
| (inr a) (inr b) := (g a b).map embedding.inr

variables {f f₁ g₁ g f₂ g₂} {a : α₁ ⊕ α₂} {b : β₁ ⊕ β₂} {c : γ₁ ⊕ γ₂}

lemma mem_sum_lift₂ :
  c ∈ sum_lift₂ f g a b ↔ (∃ a₁ b₁ c₁, a = inl a₁ ∧ b = inl b₁ ∧ c = inl c₁ ∧ c₁ ∈ f a₁ b₁)
    ∨ ∃ a₂ b₂ c₂, a = inr a₂ ∧ b = inr b₂ ∧ c = inr c₂ ∧ c₂ ∈ g a₂ b₂ :=
begin
  split,
  { cases a; cases b,
    { rw [sum_lift₂, mem_map],
      rintro ⟨c, hc, rfl⟩,
      exact or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩ },
    { refine λ h, (not_mem_empty _ h).elim },
    { refine λ h, (not_mem_empty _ h).elim },
    { rw [sum_lift₂, mem_map],
      rintro ⟨c, hc, rfl⟩,
      exact or.inr ⟨a, b, c, rfl, rfl, rfl, hc⟩ } },
  { rintro (⟨a, b, c, rfl, rfl, rfl, h⟩ | ⟨a, b, c, rfl, rfl, rfl, h⟩); exact mem_map_of_mem _ h }
end

lemma inl_mem_sum_lift₂ {c₁ : γ₁} :
  inl c₁ ∈ sum_lift₂ f g a b ↔ ∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ c₁ ∈ f a₁ b₁ :=
begin
  rw [mem_sum_lift₂, or_iff_left],
  simp only [exists_and_distrib_left, exists_eq_left'],
  rintro ⟨_, _, c₂, _, _, h, _⟩,
  exact inl_ne_inr h,
end

lemma inr_mem_sum_lift₂ {c₂ : γ₂} :
  inr c₂ ∈ sum_lift₂ f g a b ↔ ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ c₂ ∈ g a₂ b₂ :=
begin
  rw [mem_sum_lift₂, or_iff_right],
  simp only [exists_and_distrib_left, exists_eq_left'],
  rintro ⟨_, _, c₂, _, _, h, _⟩,
  exact inr_ne_inl h,
end

lemma sum_lift₂_eq_empty :
  (sum_lift₂ f g a b) = ∅ ↔ (∀ a₁ b₁, a = inl a₁ → b = inl b₁ → f a₁ b₁ = ∅)
    ∧ ∀ a₂ b₂, a = inr a₂ → b = inr b₂ → g a₂ b₂ = ∅ :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { split; { rintro a b rfl rfl, exact map_eq_empty.1 h } },
  cases a; cases b,
  { exact map_eq_empty.2 (h.1 _ _ rfl rfl) },
  { refl },
  { refl },
  { exact map_eq_empty.2 (h.2 _ _ rfl rfl) }
end

lemma sum_lift₂_nonempty :
  (sum_lift₂ f g a b).nonempty ↔ (∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ (f a₁ b₁).nonempty)
    ∨ ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ (g a₂ b₂).nonempty :=
by simp [nonempty_iff_ne_empty, sum_lift₂_eq_empty, not_and_distrib]

lemma sum_lift₂_mono (h₁ : ∀ a b, f₁ a b ⊆ g₁ a b) (h₂ : ∀ a b, f₂ a b ⊆ g₂ a b) :
  ∀ a b, sum_lift₂ f₁ f₂ a b ⊆ sum_lift₂ g₁ g₂ a b
| (inl a) (inl b) := map_subset_map.2 (h₁ _ _)
| (inl a) (inr b) := subset.rfl
| (inr a) (inl b) := subset.rfl
| (inr a) (inr b) := map_subset_map.2 (h₂ _ _)

end sum_lift₂
end finset

open finset function

namespace sum
variables {α β : Type*}

/-! ### Disjoint sum of orders -/

section disjoint
variables [preorder α] [preorder β] [locally_finite_order α] [locally_finite_order β]

instance : locally_finite_order (α ⊕ β) :=
{ finset_Icc := sum_lift₂ Icc Icc,
  finset_Ico := sum_lift₂ Ico Ico,
  finset_Ioc := sum_lift₂ Ioc Ioc,
  finset_Ioo := sum_lift₂ Ioo Ioo,
  finset_mem_Icc := by rintro (a | a) (b | b) (x | x); simp,
  finset_mem_Ico := by rintro (a | a) (b | b) (x | x); simp,
  finset_mem_Ioc := by rintro (a | a) (b | b) (x | x); simp,
  finset_mem_Ioo := by rintro (a | a) (b | b) (x | x); simp }

variables (a₁ a₂ : α) (b₁ b₂ : β) (a b : α ⊕ β)

lemma Icc_inl_inl : Icc (inl a₁ : α ⊕ β) (inl a₂) = (Icc a₁ a₂).map embedding.inl := rfl
lemma Ico_inl_inl : Ico (inl a₁ : α ⊕ β) (inl a₂) = (Ico a₁ a₂).map embedding.inl := rfl
lemma Ioc_inl_inl : Ioc (inl a₁ : α ⊕ β) (inl a₂) = (Ioc a₁ a₂).map embedding.inl := rfl
lemma Ioo_inl_inl : Ioo (inl a₁ : α ⊕ β) (inl a₂) = (Ioo a₁ a₂).map embedding.inl := rfl
@[simp] lemma Icc_inl_inr : Icc (inl a₁) (inr b₂) = ∅ := rfl
@[simp] lemma Ico_inl_inr : Ico (inl a₁) (inr b₂) = ∅ := rfl
@[simp] lemma Ioc_inl_inr : Ioc (inl a₁) (inr b₂) = ∅ := rfl
@[simp] lemma Ioo_inl_inr : Ioo (inl a₁) (inr b₂) = ∅ := rfl
@[simp] lemma Icc_inr_inl : Icc (inr b₁) (inl a₂) = ∅ := rfl
@[simp] lemma Ico_inr_inl : Ico (inr b₁) (inl a₂) = ∅ := rfl
@[simp] lemma Ioc_inr_inl : Ioc (inr b₁) (inl a₂) = ∅ := rfl
@[simp] lemma Ioo_inr_inl : Ioo (inr b₁) (inl a₂) = ∅ := rfl
lemma Icc_inr_inr : Icc (inr b₁ : α ⊕ β) (inr b₂) = (Icc b₁ b₂).map embedding.inr := rfl
lemma Ico_inr_inr : Ico (inr b₁ : α ⊕ β) (inr b₂) = (Ico b₁ b₂).map embedding.inr := rfl
lemma Ioc_inr_inr : Ioc (inr b₁ : α ⊕ β) (inr b₂) = (Ioc b₁ b₂).map embedding.inr := rfl
lemma Ioo_inr_inr : Ioo (inr b₁ : α ⊕ β) (inr b₂) = (Ioo b₁ b₂).map embedding.inr := rfl

end disjoint
end sum
