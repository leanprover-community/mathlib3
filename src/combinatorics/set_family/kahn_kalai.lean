/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.special_functions.log
import order.upper_lower

/-!
# The Kahn-Kalai conjecture

This file proves the Kahn-Kalai conjecture.
-/

variables {α : Type*}

namespace upper_set
variables [preorder α] {s : set α} {a : α}

/-- The smallest upper set containing `s`. -/
def generate (s : set α) : upper_set α :=
{ carrier := {a | ∃ b ∈ s, b ≤ a},
  upper' := λ a b h, Exists₂.imp $ λ c _ hc, hc.trans h }

@[simp] lemma coe_generate (s : set α) : ↑(generate s) = {a | ∃ b ∈ s, b ≤ a} := rfl
@[simp] lemma mem_generate_iff : a ∈ generate s ↔ ∃ b ∈ s, b ≤ a := iff.rfl
lemma subset_generate (s : set α) : s ⊆ generate s := λ a ha, ⟨a, ha, le_rfl⟩

end upper_set

open finset real
open_locale big_operators

variables [fintype α] [decidable_eq α] {𝒜 : finset (finset α)}

/-- The product measure of a finset. -/
def product_measure (p : ℝ) (s : finset α) : ℝ := p ^ s.card * (1 - p) ^ sᶜ.card

/-- The product measure of a set family. -/
def family_measure (p : ℝ) (𝒜 : finset (finset α)) : ℝ := ∑ s in 𝒜, product_measure p s

/-- The price of a set family. -/
def price (p : ℝ) (𝒜 : finset (finset α)) : ℝ := ∑ s in 𝒜, p ^ s.card

def p_small (p : ℝ) (𝒜 : finset (finset α)) : Prop :=
∃ ℬ : finset (finset α), (𝒜 : set (finset α)) ⊆ upper_set.generate (ℬ : set (finset α)) ∧
  price p ℬ ≤ 1/2

noncomputable def expectation_threshold (𝒜 : finset (finset α)) : ℝ := ⨆ p : {p // p_small p 𝒜}, p

/-- The size of the largest minimal element of `𝒜`. -/
def finset.largest_min (𝒜 : finset (finset α)) : ℕ :=
(𝒜.filter $ λ s, ∀ t ∈ 𝒜, t ⊆ s → s ⊆ t).sup finset.card

/-- A set family is `l`-bounded if all its elements have size less than `l`. -/
def finset.bounded (l : ℕ) (𝒜 : finset (finset α)) : Prop := ∀ ⦃s : finset α⦄, s ∈ 𝒜 → s.card ≤ l

/-- The `(s, t)`-fragments of a set family `𝒜` are the sets of the form `u \ t` where `u ∈ 𝒜` and
`u ⊆ s ∪ t`. -/
def fragments (s t : finset α) (𝒜 : finset (finset α)) : finset (finset α) :=
(𝒜.filter (⊆ s ∪ t)).image (\ t)

/-- The good sets are those `s ∈ 𝒜` such that all `(s, t)`fragments have size at least `n`. -/
def good_sets (n : ℕ) (t : finset α) (𝒜 : finset (finset α)) : finset (finset α) :=
𝒜.filter $ λ s, ∀ u ∈ fragments s t 𝒜, n ≤ card u

def theorem12_bound : ℝ := sorry

-- `L` must come before `α`, so I think we want `L` somewhat explicit and out of this theorem
lemma theorem12 (p : ℝ) (l : ℕ) : ∀ 𝒜 : finset (finset α), 𝒜.bounded l → ¬ p_small p 𝒜 → true :=
sorry

def kahn_kalai_const : ℝ := sorry

theorem kahn_kalai (𝒜 : finset (finset α)) :
  (1/2 : ℝ) ≤ family_measure (kahn_kalai_const * expectation_threshold 𝒜 * log 𝒜.largest_min) 𝒜 :=
sorry
