/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .mathlib

/-!
# Witnesses of non uniformity
-/

open_locale classical

variables {α : Type*}

namespace simple_graph
variables (G : simple_graph α)

lemma not_witness_prop {G : simple_graph α} {ε : ℝ} {U V : finset α} (h : ¬G.is_uniform ε U V) :
  ∃ U', U' ⊆ U ∧ ∃ V', V' ⊆ V ∧ ↑U.card * ε ≤ U'.card ∧ ↑V.card * ε ≤ V'.card ∧
    ε ≤ |G.edge_density U' V' - G.edge_density U V| :=
by { rw [is_uniform] at h, push_neg at h, exact h }

/-- Extracts a witness of the non-uniformity of `(U, V)`. Witnesses for `(U, V)` and `(V, U)` don't
necessarily match. Hence the motivation to define `witness_aux`. -/
noncomputable def witness_aux (ε : ℝ) (U V : finset α) : finset α × finset α :=
if h : ¬G.is_uniform ε U V
  then ((not_witness_prop h).some, (not_witness_prop h).some_spec.2.some)
  else (U, V)

/-- Extracts a witness of the non-uniformity of `(U, V)`. It uses an arbitrary ordering of
`finset α` (`well_ordering_rel`) to ensure that the witnesses of `(U, V)` and `(V, U)` are related
(the existentials don't ensure we would take the same from `¬G.is_uniform ε U V` and
`¬G.is_uniform ε V U`). -/
noncomputable def witness (ε : ℝ) (U V : finset α) : finset α :=
ite (well_ordering_rel U V) (G.witness_aux ε U V).1 (G.witness_aux ε V U).2

variables (G) {ε : ℝ} {U V : finset α}

lemma left_witness_aux_subset (h : ¬G.is_uniform ε U V) : (G.witness_aux ε U V).1 ⊆ U :=
by { rw [witness_aux, dif_pos h], apply (not_witness_prop h).some_spec.1 }

lemma left_witness_aux_card (h : ¬ G.is_uniform ε U V) :
  (U.card : ℝ) * ε ≤ (G.witness_aux ε U V).1.card :=
by { rw [witness_aux, dif_pos h], apply (not_witness_prop h).some_spec.2.some_spec.2.1 }

lemma right_witness_aux_subset (h : ¬ G.is_uniform ε U V) : (G.witness_aux ε U V).2 ⊆ V :=
by { rw [witness_aux, dif_pos h], apply (not_witness_prop h).some_spec.2.some_spec.1 }

lemma right_witness_aux_card (h : ¬ G.is_uniform ε U V) :
  (V.card : ℝ) * ε ≤ (G.witness_aux ε U V).2.card :=
by { rw [witness_aux, dif_pos h], apply (not_witness_prop h).some_spec.2.some_spec.2.2.1 }

lemma witness_aux_pair_spec (h : ¬ G.is_uniform ε U V) :
  ε ≤ |G.edge_density (G.witness_aux ε U V).1 (G.witness_aux ε U V).2 - G.edge_density U V| :=
by { rw [witness_aux, dif_pos h], apply (not_witness_prop h).some_spec.2.some_spec.2.2.2 }

lemma witness_subset (h : ¬ G.is_uniform ε U V) : G.witness ε U V ⊆ U :=
begin
  dsimp [witness],
  split_ifs,
  { apply G.left_witness_aux_subset h },
  { apply G.right_witness_aux_subset (λ i, h i.symm) },
end

lemma witness_card (h : ¬ G.is_uniform ε U V) : (U.card : ℝ) * ε ≤ (G.witness ε U V).card :=
begin
  dsimp [witness],
  split_ifs,
  { apply G.left_witness_aux_card h },
  { apply G.right_witness_aux_card (λ i, h i.symm) }
end

lemma witness_pair_spec (h₁ : U ≠ V) (h₂ : ¬ G.is_uniform ε U V) :
  ε ≤ |G.edge_density (G.witness ε U V) (G.witness ε V U) - G.edge_density U V| :=
begin
  unfold witness,
  rcases trichotomous_of well_ordering_rel U V with lt | rfl | gt,
  { rw [if_pos lt, if_neg (asymm lt)],
    exact G.witness_aux_pair_spec h₂ },
  { cases h₁ rfl },
  { rw [if_neg (asymm gt), if_pos gt, edge_density_comm, edge_density_comm _ U],
    apply G.witness_aux_pair_spec (λ i, h₂ i.symm) }
end

end simple_graph
