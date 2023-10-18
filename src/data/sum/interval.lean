/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.sum
import data.sum.order
import order.locally_finite

/-!
# Finite intervals in a disjoint union

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the `locally_finite_order` instance for the disjoint sum and linear sum of two
orders and calculates the cardinality of their finite intervals.
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

section sum_lex_lift
variables (f₁ f₁' : α₁ → β₁ → finset γ₁) (f₂ f₂' : α₂ → β₂ → finset γ₂)
          (g₁ g₁' : α₁ → β₂ → finset γ₁) (g₂ g₂' : α₁ → β₂ → finset γ₂)

/-- Lifts maps `α₁ → β₁ → finset γ₁`, `α₂ → β₂ → finset γ₂`, `α₁ → β₂ → finset γ₁`,
`α₂ → β₂ → finset γ₂`  to a map `α₁ ⊕ α₂ → β₁ ⊕ β₂ → finset (γ₁ ⊕ γ₂)`. Could be generalized to
alternative monads if we can make sure to keep computability and universe polymorphism. -/
def sum_lex_lift : Π (a : α₁ ⊕ α₂) (b : β₁ ⊕ β₂), finset (γ₁ ⊕ γ₂)
| (inl a) (inl b) := (f₁ a b).map embedding.inl
| (inl a) (inr b) := (g₁ a b).disj_sum (g₂ a b)
| (inr a) (inl b) := ∅
| (inr a) (inr b) := (f₂ a b).map ⟨_, inr_injective⟩

@[simp] lemma sum_lex_lift_inl_inl (a : α₁) (b : β₁) :
  sum_lex_lift f₁ f₂ g₁ g₂ (inl a) (inl b) = (f₁ a b).map embedding.inl := rfl

@[simp] lemma sum_lex_lift_inl_inr (a : α₁) (b : β₂) :
  sum_lex_lift f₁ f₂ g₁ g₂ (inl a) (inr b) = (g₁ a b).disj_sum (g₂ a b) := rfl

@[simp] lemma sum_lex_lift_inr_inl (a : α₂) (b : β₁) :
  sum_lex_lift f₁ f₂ g₁ g₂ (inr a) (inl b) = ∅ := rfl

@[simp] lemma sum_lex_lift_inr_inr (a : α₂) (b : β₂) :
  sum_lex_lift f₁ f₂ g₁ g₂ (inr a) (inr b) = (f₂ a b).map ⟨_, inr_injective⟩ := rfl

variables {f₁ g₁ f₂ g₂ f₁' g₁' f₂' g₂'} {a : α₁ ⊕ α₂} {b : β₁ ⊕ β₂} {c : γ₁ ⊕ γ₂}

lemma mem_sum_lex_lift :
  c ∈ sum_lex_lift f₁ f₂ g₁ g₂ a b ↔
    (∃ a₁ b₁ c₁, a = inl a₁ ∧ b = inl b₁ ∧ c = inl c₁ ∧ c₁ ∈ f₁ a₁ b₁) ∨
    (∃ a₁ b₂ c₁, a = inl a₁ ∧ b = inr b₂ ∧ c = inl c₁ ∧ c₁ ∈ g₁ a₁ b₂) ∨
    (∃ a₁ b₂ c₂, a = inl a₁ ∧ b = inr b₂ ∧ c = inr c₂ ∧ c₂ ∈ g₂ a₁ b₂) ∨
     ∃ a₂ b₂ c₂, a = inr a₂ ∧ b = inr b₂ ∧ c = inr c₂ ∧ c₂ ∈ f₂ a₂ b₂ :=
begin
  split,
  { cases a; cases b,
    { rw [sum_lex_lift, mem_map],
      rintro ⟨c, hc, rfl⟩,
      exact or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩ },
    { refine λ h, (mem_disj_sum.1 h).elim _ _,
      { rintro ⟨c, hc, rfl⟩,
        refine or.inr (or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩) },
      { rintro ⟨c, hc, rfl⟩,
        refine or.inr (or.inr $ or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩) } },
    { refine λ h, (not_mem_empty _ h).elim },
    { rw [sum_lex_lift, mem_map],
      rintro ⟨c, hc, rfl⟩,
      exact or.inr (or.inr $ or.inr $ ⟨a, b, c, rfl, rfl, rfl, hc⟩) } },
  { rintro (⟨a, b, c, rfl, rfl, rfl, hc⟩ | ⟨a, b, c, rfl, rfl, rfl, hc⟩ |
      ⟨a, b, c, rfl, rfl, rfl, hc⟩ | ⟨a, b, c, rfl, rfl, rfl, hc⟩),
    { exact mem_map_of_mem _ hc },
    { exact inl_mem_disj_sum.2 hc },
    { exact inr_mem_disj_sum.2 hc },
    { exact mem_map_of_mem _ hc } }
end

lemma inl_mem_sum_lex_lift {c₁ : γ₁} :
  inl c₁ ∈ sum_lex_lift f₁ f₂ g₁ g₂ a b ↔
    (∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ c₁ ∈ f₁ a₁ b₁) ∨
     ∃ a₁ b₂, a = inl a₁ ∧ b = inr b₂ ∧ c₁ ∈ g₁ a₁ b₂ :=
by simp [mem_sum_lex_lift]

lemma inr_mem_sum_lex_lift {c₂ : γ₂} :
  inr c₂ ∈ sum_lex_lift f₁ f₂ g₁ g₂ a b ↔
    (∃ a₁ b₂, a = inl a₁ ∧ b = inr b₂ ∧ c₂ ∈ g₂ a₁ b₂) ∨
     ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ c₂ ∈ f₂ a₂ b₂ :=
by simp [mem_sum_lex_lift]

lemma sum_lex_lift_mono (hf₁ : ∀ a b, f₁ a b ⊆ f₁' a b) (hf₂ : ∀ a b, f₂ a b ⊆ f₂' a b)
  (hg₁ : ∀ a b, g₁ a b ⊆ g₁' a b) (hg₂ : ∀ a b, g₂ a b ⊆ g₂' a b) (a : α₁ ⊕ α₂) (b : β₁ ⊕ β₂) :
  sum_lex_lift f₁ f₂ g₁ g₂ a b ⊆ sum_lex_lift f₁' f₂' g₁' g₂' a b :=
begin
  cases a; cases b,
  exacts [map_subset_map.2 (hf₁ _ _), disj_sum_mono (hg₁ _ _) (hg₂ _ _), subset.rfl,
    map_subset_map.2 (hf₂ _ _)],
end

lemma sum_lex_lift_eq_empty :
  (sum_lex_lift f₁ f₂ g₁ g₂ a b) = ∅ ↔ (∀ a₁ b₁, a = inl a₁ → b = inl b₁ → f₁ a₁ b₁ = ∅) ∧
    (∀ a₁ b₂, a = inl a₁ → b = inr b₂ → g₁ a₁ b₂ = ∅ ∧ g₂ a₁ b₂ = ∅) ∧
    ∀ a₂ b₂, a = inr a₂ → b = inr b₂ → f₂ a₂ b₂ = ∅ :=
begin
  refine ⟨λ h, ⟨_, _, _⟩, λ h, _⟩,
  any_goals { rintro a b rfl rfl, exact map_eq_empty.1 h },
  { rintro a b rfl rfl, exact disj_sum_eq_empty.1 h },
  cases a; cases b,
  { exact map_eq_empty.2 (h.1 _ _ rfl rfl) },
  { simp [h.2.1 _ _ rfl rfl] },
  { refl },
  { exact map_eq_empty.2 (h.2.2 _ _ rfl rfl) }
end

lemma sum_lex_lift_nonempty :
  (sum_lex_lift f₁ f₂ g₁ g₂ a b).nonempty ↔ (∃ a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ (f₁ a₁ b₁).nonempty)
    ∨ (∃ a₁ b₂, a = inl a₁ ∧ b = inr b₂ ∧ ((g₁ a₁ b₂).nonempty ∨ (g₂ a₁ b₂).nonempty))
    ∨ ∃ a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ (f₂ a₂ b₂).nonempty :=
by simp [nonempty_iff_ne_empty, sum_lex_lift_eq_empty, not_and_distrib]

end sum_lex_lift
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

/-! ### Lexicographical sum of orders -/

namespace lex
variables [preorder α] [preorder β] [order_top α] [order_bot β] [locally_finite_order α]
  [locally_finite_order β]

/-- Throwaway tactic. -/
private meta def simp_lex : tactic unit :=
`[refine to_lex.surjective.forall₃.2 _, rintro (a | a) (b | b) (c | c); simp only
    [sum_lex_lift_inl_inl, sum_lex_lift_inl_inr, sum_lex_lift_inr_inl, sum_lex_lift_inr_inr,
    inl_le_inl_iff, inl_le_inr, not_inr_le_inl, inr_le_inr_iff, inl_lt_inl_iff, inl_lt_inr,
    not_inr_lt_inl, inr_lt_inr_iff, mem_Icc, mem_Ico, mem_Ioc, mem_Ioo, mem_Ici, mem_Ioi, mem_Iic,
    mem_Iio, equiv.coe_to_embedding, to_lex_inj, exists_false, and_false, false_and, map_empty,
    not_mem_empty, true_and, inl_mem_disj_sum, inr_mem_disj_sum, and_true, of_lex_to_lex, mem_map,
    embedding.coe_fn_mk, exists_prop, exists_eq_right, embedding.inl_apply]]

instance locally_finite_order : locally_finite_order (α ⊕ₗ β) :=
{ finset_Icc := λ a b,
    (sum_lex_lift Icc Icc (λ a _, Ici a) (λ _, Iic) (of_lex a) (of_lex b)).map to_lex.to_embedding,
  finset_Ico := λ a b,
    (sum_lex_lift Ico Ico (λ a _, Ici a) (λ _, Iio) (of_lex a) (of_lex b)).map to_lex.to_embedding,
  finset_Ioc := λ a b,
    (sum_lex_lift Ioc Ioc (λ a _, Ioi a) (λ _, Iic) (of_lex a) (of_lex b)).map to_lex.to_embedding,
  finset_Ioo := λ a b,
    (sum_lex_lift Ioo Ioo (λ a _, Ioi a) (λ _, Iio) (of_lex a) (of_lex b)).map to_lex.to_embedding,
  finset_mem_Icc := by simp_lex,
  finset_mem_Ico := by simp_lex,
  finset_mem_Ioc := by simp_lex,
  finset_mem_Ioo := by simp_lex }

variables (a a₁ a₂ : α) (b b₁ b₂ : β)

lemma Icc_inl_inl :
  Icc (inlₗ a₁ : α ⊕ₗ β) (inlₗ a₂) = (Icc a₁ a₂).map (embedding.inl.trans to_lex.to_embedding) :=
by { rw ←finset.map_map, refl }

lemma Ico_inl_inl :
  Ico (inlₗ a₁ : α ⊕ₗ β) (inlₗ a₂) = (Ico a₁ a₂).map (embedding.inl.trans to_lex.to_embedding) :=
by { rw ←finset.map_map, refl }

lemma Ioc_inl_inl :
  Ioc (inlₗ a₁ : α ⊕ₗ β) (inlₗ a₂) = (Ioc a₁ a₂).map (embedding.inl.trans to_lex.to_embedding) :=
by { rw ←finset.map_map, refl }

lemma Ioo_inl_inl :
  Ioo (inlₗ a₁ : α ⊕ₗ β) (inlₗ a₂) = (Ioo a₁ a₂).map (embedding.inl.trans to_lex.to_embedding) :=
by { rw ←finset.map_map, refl }

@[simp] lemma Icc_inl_inr :
  Icc (inlₗ a) (inrₗ b) = ((Ici a).disj_sum (Iic b)).map to_lex.to_embedding := rfl
@[simp] lemma Ico_inl_inr :
  Ico (inlₗ a) (inrₗ b) = ((Ici a).disj_sum (Iio b)).map to_lex.to_embedding := rfl
@[simp] lemma Ioc_inl_inr :
  Ioc (inlₗ a) (inrₗ b) = ((Ioi a).disj_sum (Iic b)).map to_lex.to_embedding := rfl
@[simp] lemma Ioo_inl_inr :
  Ioo (inlₗ a) (inrₗ b) = ((Ioi a).disj_sum (Iio b)).map to_lex.to_embedding := rfl

@[simp] lemma Icc_inr_inl : Icc (inrₗ b) (inlₗ a) = ∅ := rfl
@[simp] lemma Ico_inr_inl : Ico (inrₗ b) (inlₗ a) = ∅ := rfl
@[simp] lemma Ioc_inr_inl : Ioc (inrₗ b) (inlₗ a) = ∅ := rfl
@[simp] lemma Ioo_inr_inl : Ioo (inrₗ b) (inlₗ a) = ∅ := rfl

lemma Icc_inr_inr :
  Icc (inrₗ b₁ : α ⊕ₗ β) (inrₗ b₂) = (Icc b₁ b₂).map (embedding.inr.trans to_lex.to_embedding) :=
by { rw ←finset.map_map, refl }

lemma Ico_inr_inr :
  Ico (inrₗ b₁ : α ⊕ₗ β) (inrₗ b₂) = (Ico b₁ b₂).map (embedding.inr.trans to_lex.to_embedding) :=
by { rw ←finset.map_map, refl }

lemma Ioc_inr_inr :
  Ioc (inrₗ b₁ : α ⊕ₗ β) (inrₗ b₂) = (Ioc b₁ b₂).map (embedding.inr.trans to_lex.to_embedding) :=
by { rw ←finset.map_map, refl }

lemma Ioo_inr_inr :
  Ioo (inrₗ b₁ : α ⊕ₗ β) (inrₗ b₂) = (Ioo b₁ b₂).map (embedding.inr.trans to_lex.to_embedding) :=
by { rw ←finset.map_map, refl }

end lex
end sum
