/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.big_operators.order
import data.nat.basic

/-!
# Equitable functions

This file defines equitable functions.

A function `f` is equitable on a set `s` if `f a₁ ≤ f a₂ + 1` for all `a₁, a₂ ∈ s`. This is mostly
useful when the domain of `f` is `ℕ` or `ℤ` (or more generally a successor order).

## TODO

`ℕ` can be replaced by any `succ_order` + `conditionally_complete_monoid`, but we don't have either
of those yet.
-/

open_locale big_operators

variables {α β : Type*}

namespace set

/-- A set is equitable if no element value is more than one bigger than another. -/
def equitable_on [has_le β] [has_add β] [has_one β] (s : set α) (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, a₁ ∈ s → a₂ ∈ s → f a₁ ≤ f a₂ + 1

@[simp]
lemma equitable_on_empty [has_le β] [has_add β] [has_one β] (f : α → β) :
  equitable_on ∅ f :=
λ a _ ha, (set.not_mem_empty _ ha).elim

lemma equitable_on_iff_exists_le_le_add_one {s : set α} {f : α → ℕ} :
  s.equitable_on f ↔ ∃ b, ∀ a ∈ s, b ≤ f a ∧ f a ≤ b + 1 :=
begin
  refine ⟨_, λ ⟨b, hb⟩ x y hx hy, (hb x hx).2.trans (add_le_add_right (hb y hy).1 _)⟩,
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty,
  { simp },
  intros hs,
  by_cases h : ∀ y ∈ s, f x ≤ f y,
  { exact ⟨f x, λ y hy, ⟨h _ hy, hs hy hx⟩⟩ },
  push_neg at h,
  obtain ⟨w, hw, hwx⟩ := h,
  refine ⟨f w, λ y hy, ⟨nat.le_of_succ_le_succ _, hs hy hw⟩⟩,
  rw (nat.succ_le_of_lt hwx).antisymm (hs hx hw),
  exact hs hx hy,
end

lemma equitable_on_iff_exists_image_subset_Icc {s : set α} {f : α → ℕ} :
  s.equitable_on f ↔ ∃ b, f '' s ⊆ Icc b (b + 1) :=
by simpa only [image_subset_iff] using equitable_on_iff_exists_le_le_add_one

lemma equitable_on_iff_exists_eq_eq_add_one {s : set α} {f : α → ℕ} :
  s.equitable_on f ↔ ∃ b, ∀ a ∈ s, f a = b ∨ f a = b + 1 :=
by simp_rw [equitable_on_iff_exists_le_le_add_one, nat.le_and_le_add_one_iff]

end set

open set

namespace finset

lemma equitable_on_iff_le_le_add_one {s : finset α} {f : α → ℕ} :
  equitable_on (s : set α) f ↔
    ∀ a ∈ s, (∑ i in s, f i) / s.card ≤ f a ∧ f a ≤ (∑ i in s, f i) / s.card + 1 :=
begin
  rw set.equitable_on_iff_exists_le_le_add_one,
  refine ⟨_, λ h, ⟨_, h⟩ ⟩,
  rintro ⟨b, hb⟩,
  by_cases h : ∀ a ∈ s, f a = b + 1,
  { intros a ha,
    rw [h _ ha, sum_const_nat h, nat.mul_div_cancel_left _ (card_pos.2 ⟨a, ha⟩)],
    exact ⟨le_rfl, nat.le_succ _⟩ },
  push_neg at h,
  obtain ⟨x, hx₁, hx₂⟩ := h,
  suffices h : b = (∑ i in s, f i) / s.card,
  { simp_rw ←h,
    apply hb },
  symmetry,
  refine nat.div_eq_of_lt_le (le_trans (by simp [mul_comm]) (sum_le_sum (λ a ha, (hb a ha).1)))
    ((sum_lt_sum (λ a ha, (hb a ha).2) ⟨_, hx₁, (hb _ hx₁).2.lt_of_ne hx₂⟩).trans_le _),
  rw [mul_comm, sum_const_nat],
  exact λ _ _, rfl,
end

lemma equitable_on_iff {s : finset α} {f : α → ℕ} :
  equitable_on (s : set α) f ↔
    ∀ a ∈ s, f a = (∑ i in s, f i) / s.card ∨ f a = (∑ i in s, f i) / s.card + 1 :=
by simp_rw [equitable_on_iff_le_le_add_one, nat.le_and_le_add_one_iff]

end finset
