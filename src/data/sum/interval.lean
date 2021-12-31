/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.sum.order
import order.locally_finite

/-!
# Finite intervals in a disjoint union

This file provides the `locally_finite_order` instance for the disjoint sum and linear sum of two
orders and calculates the cardinality of their finite intervals.
-/

open function

namespace finset
variables {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type*} (f f₁ g₁ : α₁ → β₁ → finset γ₁)
  (g f₂ g₂ : α₂ → β₂ → finset γ₂)

/-- Lifts maps `α₁ → β₁ → finset γ₁` and `α₂ → β₂ → finset γ₂` to a map
`α₁ ⊕ α₂ → β₁ ⊕ β₂ → finset (γ₁ ⊕ γ₂)`. -/
def sum_lift₂ : Π (a : α₁ ⊕ α₂) (b : β₁ ⊕ β₂), finset (γ₁ ⊕ γ₂)
| (inl a) (inl b) := (f a b).map ⟨_, inl_injective⟩
| (inl a) (inr b) := ∅
| (inr a) (inl b) := ∅
| (inr a) (inr b) := (g a b).map ⟨_, inr_injective⟩

@[simp] lemma sum_lift₂_inl_inl (a : α₁) (b : β₁) :
  sum_lift₂ f g (inl a) (inl b) = (f a b).map ⟨_, inl_injective⟩ := rfl

@[simp] lemma sum_lift₂_inl_inr (a : α₁) (b : β₂) : sum_lift₂ f g (inl a) (inr b) = ∅ := rfl
@[simp] lemma sum_lift₂_inr_inl (a : α₂) (b : β₁) : sum_lift₂ f g (inr a) (inl b) = ∅ := rfl

@[simp] lemma sum_lift₂_inr_inr (a : α₂) (b : β₂) :
  sum_lift₂ f g (inr a) (inr b) = (g a b).map ⟨_, inr_injective⟩ := rfl

variables {f f₁ g₁ g f₂ g₂} {a : α₁ ⊕ α₂} {b : β₁ ⊕ β₂} {c : γ₁ ⊕ γ₂}

lemma mem_sum_lift₂ :
  c ∈ sum_lift₂ f g a b ↔ (∃ a₁ b₁ c₁, a = inl a₁ ∧ b = inl b₁ ∧ c = inl c₁ ∧ c₁ ∈ f a₁ b₁)
    ∨ ∃ a₂ b₂ c₂, a = inl a₂ ∧ b = inl b₂ ∧ c = inl c₂ ∧ c₂ ∈ g a₂ b₂ :=
begin
  split,
  { cases a; cases b,
    { rw [sum_lift₂, mem_map],
      rintro ⟨c, hc, rfl⟩,
      refine or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩ },
    { refine iff_of_false (not_mem_empty _) _,
       } },
  { rintro (⟨a, b, c, rfl, rfl, rfl, hc⟩ | ⟨a, b, c, rfl, rfl, rfl, hc⟩),
    exact mem_map_of_mem hc }
end

lemma sum_lift₂_nonempty :
  (sum_lift₂ f g a b).nonempty ↔ (∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ (f a₁ b₁).nonempty)
    ∨ ∃ a₂ b₂, a = inl a₂ ∧ b = inl b₂ ∧ (g a₂ b₂).nonempty :=
begin
  sorry
end

lemma sum_lift_eq_empty :
  (sum_lift₂ f g a b) = ∅ ↔ (∀ a₁ b₁, a = inl a₁ → b = inl b₁ → f a₁ b₁ = ∅)
    ∧ ∀ a₂ b₂, a = inl a₂ → b = inl b₂ → g a₂ b₂ = ∅ :=
begin
  sorry
end

lemma sum_lift_mono (h₁ : ∀ ⦃a b⦄, f₁ a b ⊆ g₁ a b) (h₂ : ∀ ⦃a b⦄, f₂ a b ⊆ g₂ a b) (a : α₁ ⊕ α₂)
  (b : β₁ ⊕ β₂) :
  sum_lift₂ f₁ f₂ a b ⊆ sum_lift₂ g₁ g₂ a b :=
begin
  sorry
end

variables (f a b)

lemma card_sum_lift₂_inl_inl :
  (sum_lift₂ f a b).card = dite (a.1 = b.1) (λ h, (f (h.rec a.2) b.2).card) (λ _, 0) :=
sorry

end finset

open finset function

namespace sum
variables {ι : Type*} {α : ι → Type*}

/-! ### Disjoint sum of orders -/

section disjoint
variables [preorder α] [preorder β] [locally_finite_order α] [locally_finite_order β]

instance : locally_finite_order (α ⊕ β) :=
{ finset_Icc := sum_lift₂ Icc Icc,
  finset_Ico := sum_lift₂ Ico Ico,
  finset_Ioc := sum_lift₂ Ioc Ioc,
  finset_Ioo := sum_lift₂ Ioo Ioo,
  finset_mem_Icc := λ ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩, begin
    simp_rw [mem_sum_lift, le_def, mem_Icc, exists_and_distrib_left, ←exists_and_distrib_right,
      ←exists_prop],
    exact bex_congr (λ _ _, by split; rintro ⟨⟨⟩, ht⟩; exact ⟨rfl, ht⟩),
  end,
  finset_mem_Ico := λ ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩, begin
    simp_rw [mem_sum_lift, le_def, lt_def, mem_Ico, exists_and_distrib_left,
      ←exists_and_distrib_right, ←exists_prop],
    exact bex_congr (λ _ _, by split; rintro ⟨⟨⟩, ht⟩; exact ⟨rfl, ht⟩),
  end,
  finset_mem_Ioc := λ ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩, begin
    simp_rw [mem_sum_lift, le_def, lt_def, mem_Ioc, exists_and_distrib_left,
      ←exists_and_distrib_right, ←exists_prop],
    exact bex_congr (λ _ _, by split; rintro ⟨⟨⟩, ht⟩; exact ⟨rfl, ht⟩),
  end,
  finset_mem_Ioo := λ ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩, begin
    simp_rw [mem_sum_lift, lt_def, mem_Ioo, exists_and_distrib_left, ←exists_and_distrib_right,
      ←exists_prop],
    exact bex_congr (λ _ _, by split; rintro ⟨⟨⟩, ht⟩; exact ⟨rfl, ht⟩),
  end }

variables (a₁ a₂ : α) (b₁ b₂ : β) (a b : α ⊕ β)

lemma Icc_inl_inl : Icc (inl a₁ : α ⊕ β) (inl a₂) = (Icc a₁ a₂).map ⟨_, inl_injective⟩ :=
sum_lift₂_inl_inl _ _

end disjoint

/-! ### Lexicographical sum of orders -/

namespace lex

end lex
end sum
