/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .mathlib
import combinatorics.weighted_graph.dart
import combinatorics.weighted_graph.matching

/-!
# Weighted graphs
-/

open_locale big_operators

-- `α`: Vertices
-- `W`: Weights
-- `𝒸`: Colors
variables {α W 𝒸 : Type*}

namespace weighted_graph

structure edge_bicoloring (G : weighted_graph α W) (𝒸 : Type*) :=
(color : G.dart → 𝒸)

structure edge_coloring (G : weighted_graph α W) (𝒸 : Type*) extends edge_bicoloring G 𝒸 :=
(color_rev (ab : G.dart) : color ab.rev = color ab)

section comm_monoid
variables [fintype α] [decidable_eq α] [comm_monoid W] {G : weighted_graph α W}

/-- The product of the weights of the edges of a subgraph. -/
@[to_additive]
def subgraph.prod_weight (G' : G.subgraph) [decidable_rel G'.adj] : W :=
∏ e in G'.edge_finset.attach, option.get (G'.is_some_edge_weight_iff.2 $ G'.mem_edge_finset.1 e.2)

end comm_monoid

section semiring
variables [semiring W] (G : weighted_graph α (Sort*))

def coloring_weight (f : Π a b (h : (G.weight a b).is_some), option.get h → W × 𝒸) : W :=
∑

/-- -/
def monochromatic : Prop := ∀ f, G.coloring_weight f

def col : ℕ :=
sorry

end semiring

section canonically_ordered_comm_semiring
variables [fintype α] [canonically_ordered_comm_semiring W] (G : weighted_graph α W)

lemma canon_bogdanov2 (hα : 5 ≤ fintype.card α) : col ≤ 2 := sorry

lemma canon_bogdanov3 : col ≤ 3 := sorry

end canonically_ordered_comm_semiring
end weighted_graph
