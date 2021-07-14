/-
Copyright (c) 2021 Bhavik Mehta, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
import algebra.big_operators.basic
import algebra.ordered_ring
import data.nat.basic

/-!
# Equitable functions

This file provides a way to state that a function is equitable.

A function `f` is equitable on a set `s` if `f a₁ ≤ f a₂ + 1` for all `a₁, a₂ ∈ s`.
-/

open_locale big_operators

variables {α β : Type*} [ordered_semiring β]

namespace set

/-- A set is equitable if no element value is more than one bigger than another. -/
def equitable_on (s : set α) (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, a₁ ∈ s → a₂ ∈ s → f a₁ ≤ f a₂ + 1

@[simp]
lemma equitable_on_empty (f : α → β) :
  equitable_on ∅ f :=
λ a _ ha, (set.not_mem_empty _ ha).elim

lemma equitable_on_iff (s : set α) (f : α → β) :
  equitable_on s f ↔ ∀ ⦃a₁ a₂⦄, a₁ ∈ s → a₂ ∈ s → f a₂ - f a₁ ≤ 1 :=
begin
  split,
  { intros hf a₁ a₂ ha₁ ha₂,
    cases le_total (f a₁) (f a₂),
    { apply hf ha₁ ha₂ h },
    rw nat.sub_eq_zero_of_le h,
    exact nat.zero_le _ },
  exact λ hf a₁ a₂ ha₁ ha₂ _, hf ha₁ ha₂,
end

lemma equitable_on_iff_almost_eq_constant {s : set α} {f : α → β} :
  equitable_on s f ↔ ∃ b, ∀ a ∈ s, f a = b ∨ f a = b + 1 :=
begin
  classical,
  split,
  { rw equitable_on_iff,
    obtain rfl | hs := s.eq_empty_or_nonempty,
    { simp },
    intros h,
    refine ⟨nat.find (set.nonempty.image f hs), _⟩,
    obtain ⟨w, hw₁, hw₂⟩ := nat.find_spec (set.nonempty.image f hs),
    intros a ha,
    have : nat.find (set.nonempty.image f hs) ≤ f a := nat.find_min' _ ⟨_, ha, rfl⟩,
    cases eq_or_lt_of_le this with q q,
    { exact or.inl q.symm },
    refine or.inr (le_antisymm _ (nat.succ_le_of_lt q)),
      rw [←hw₂, ←nat.sub_le_left_iff_le_add],
      exact h hw₁ ha },
  rintro ⟨b, hb⟩ x₁ x₂ hx₁ hx₂ h,
  rcases hb x₁ hx₁ with rfl | hx₁';
  cases hb x₂ hx₂ with hx₂' hx₂',
  { simp [hx₂'] },
  { simp [hx₂'] },
  { simpa [hx₁', hx₂'] using h },
  { simp [hx₁', hx₂'] }
end

lemma equitable_on_finset_iff_eq_average {s : finset α} {f : α → β} :
  equitable_on (s : set α) f ↔
    ∀ a ∈ s, f a = (∑ i in s, f i) / s.card ∨ f a = (∑ i in s, f i) / s.card + 1 :=
begin
  rw equitable_on_iff_almost_eq_constant,
  refine ⟨_, λ h, ⟨_, h⟩ ⟩,
  rintro ⟨b, hb⟩,
  by_cases h : ∀ a ∈ s, f a = b + 1,
  { clear hb,
    intros a ha,
    left,
    symmetry,
    apply nat.div_eq_of_eq_mul_left (finset.card_pos.2 ⟨_, ha⟩),
    rw [mul_comm, sum_const_nat],
    intros c hc,
    rw [h _ ha, h _ hc] },
  push_neg at h,
  obtain ⟨x, hx₁, hx₂⟩ := h,
  suffices : b = (∑ i in s, f i) / s.card,
  { simp_rw [←this],
    apply hb },
  simp_rw between_nat_iff at hb,
  symmetry,
  refine nat.div_eq_of_lt_le (le_trans (by simp [mul_comm]) (sum_le_sum (λ a ha, (hb a ha).1)))
    ((sum_lt_sum (λ a ha, (hb a ha).2) ⟨_, hx₁, (hb _ hx₁).2.lt_of_ne hx₂⟩).trans_le _),
  rw [mul_comm, sum_const_nat],
  exact λ _ _, rfl,
end

lemma equitable_on_finset_iff {s : finset α} {f : α → β} :
  equitable_on (s : set α) f ↔
    ∀ a ∈ s, (∑ i in s, f i) / s.card ≤ f a ∧ f a ≤ (∑ i in s, f i) / s.card + 1 :=
by simp_rw [equitable_on_finset_iff_eq_average, between_nat_iff]

end set
