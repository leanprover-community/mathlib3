/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .mathlib

/-!
# `k`-factors of a graph
-/

variables {α : Type*}

namespace simple_graph
variables (k : ℕ) (G H : simple_graph α)

/-- A graph is a `k`-factor if it is a subgraph and is `k`-regular. -/
def is_factor [locally_finite H] : Prop := H ≤ G ∧ H.is_regular_of_degree k

variables {G k H} [locally_finite H]

lemma is_factor.le (h : G.is_factor k H) : H ≤ G := h.1

lemma is_factor.is_regular (h : G.is_factor k H) : H.is_regular_of_degree k:= h.2

/-
Here, put stuff about factors over sums of graphs
-/

namespace subgraph
variables (G k H)

/-- Subgraph way. -/
def k_factors [locally_finite G] (H : subgraph G) (k : ℕ) : set (subgraph G) :=
{G'' | G'.verts = G''.verts ∧ G''.coe.is_regular_of_degree k}

end subgraph
end simple_graph
