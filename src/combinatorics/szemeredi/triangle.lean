/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .regularity_lemma
import combinatorics.simple_graph.subgraph

/-!
# Triangle counting lemma
-/

open finset fintype

variables {α : Type*} (G : simple_graph α)

namespace simple_graph

-- def is_triangle (a b c : α) : Prop := G.adj a b ∧ G.adj b c ∧ G.adj c a

-- def is_n_clique (n : ℕ) (s : finset α) : Prop := s.card = n ∧ (s : set α).pairwise_on G.adj


-- variables {α : Type*} (G : simple_graph α)

-- noncomputable def triangle_removal_bound (ε : ℝ) (l : ℕ) : ℝ :=
-- (1 - ε/2) * (ε/4)^3 * (ε/(4 * szemeredi_bound ε l))^3

-- variables [fintype α] [decidable_eq α] [decidable_rel G.adj]

-- lemma triangle_removal (α : Type*) [fintype α] (ε : ℝ)
--   (hG : (G.edge_finset.card : ℝ) ≤ (card α)^3 * triangle_removal_bound ε (card α)) :
--   ∃ (G' : subgraph G) (s : finset (sym2 α)),
--     ((G.edge_finset \ G'.edge_finset).card : ℝ) ≤ (card α)^2 * ε ∧ ∀ t, ¬ G.is_n_clique 3 t :=
-- sorry

end simple_graph
