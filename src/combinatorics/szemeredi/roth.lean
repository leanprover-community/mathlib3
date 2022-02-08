/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .corner

/-!
# Roth's theorem

This file proves Roth's theorem
-/

open finset

variables {N : ℕ} (A : finset (fin (2 * N + 1)))

inductive roth_mod_graph :
  fin 3 × fin (2 * N + 1) → fin 3 × fin (2 * N + 1) → Prop
| xy {x y} : y - x ∈ A → roth_mod_graph (0, x) (1, y)
| yz {y z} : z - y ∈ A → roth_mod_graph (1, y) (2, z)
| xz {x z} : (z - x) * (N + 1 : fin (2 * N + 1)) ∈ A → roth_mod_graph (0, x) (2, z)

/-- The graph used in the proof of Roth's theorem. -/
def roth_graph : simple_graph (fin 3 × fin (2 * N + 1)) :=
simple_graph.from_rel (roth_mod_graph A)

open_locale classical

def three_aps : finset (finset (fin (2 * N + 1))) :=
A.powerset.filter (λ i, ∃ (a d : fin (2 * N + 1)), i = {a,a+d,a+2*d})

def nontrivial_three_aps : finset (finset (fin (2 * N + 1))) :=
A.powerset.filter (λ i, ∃ (a d : fin (2 * N + 1)), d ≠ 0 ∧ i = {a,a+d,a+2*d})

lemma nontrivial_three_aps_subset_three_aps :
  nontrivial_three_aps A ⊆ three_aps A :=
begin
  rintro t ht,
  simp only [nontrivial_three_aps, three_aps, mem_powerset, mem_filter] at ht ⊢,
  tauto
end

lemma m_le_card_three_aps : A.card ≤ (three_aps A).card :=
begin
  refine card_le_card_of_inj_on (λ i, {i}) (λ i hi, _) (singleton_injective.inj_on _),
  simp only [three_aps, mem_filter, mem_powerset, singleton_subset_iff, hi, true_and],
  exact ⟨hi, i, 0, by simp only [add_zero, mul_zero, insert_singleton_self_eq]⟩,
end
