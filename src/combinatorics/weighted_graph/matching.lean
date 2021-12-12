/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.weighted_graph.subgraph

/-!
# Matchings

A *matching* for a weighted graph is a set of disjoint pairs of adjacent vertices, and the set of all
the vertices in a matching is called its *support* (and sometimes the vertices in the support are
said to be *saturated* by the matching). A *perfect matching* is a matching whose support contains
every vertex of the graph.

In this module, we represent a matching as a subgraph whose vertices are each incident to at most
one edge, and the edges of the subgraph represent the paired vertices.

## Main definitions

* `weighted_graph.subgraph.is_matching`: `G'.is_matching` means that `G'` is a matching of its
  underlying graph.
  denoted `G'.is_matching`.

* `weighted_graph.subgraph.is_perfect_matching` defines when a subgraph `G'` of a weighted graph is a
  perfect matching, denoted `G'.is_perfect_matching`.
-/

variables {α W : Type*}

namespace weighted_graph
variables {G : weighted_graph α W} (G' : G.subgraph)

namespace subgraph

/-- The subgraph `G'` of `G` is a matching if every vertex of `G'` is incident to exactly one edge in `G'`.
We say that the vertices in `G'.support` are *matched* or *saturated*. -/
def is_matching : Prop := ∀ ⦃a⦄, a ∈ G'.verts → ∃! b, G'.weight a b ≠ none

/-- The subgraph `G'` of `G` is a perfect matching on `G` if it's a matching and every vertex `G` is
matched. -/
def is_perfect_matching : Prop := G'.is_matching ∧ G'.is_spanning

lemma is_matching.support_eq_verts {G' : subgraph G} (h : G'.is_matching) : G'.support = G'.verts :=
begin
  refine G'.support_subset_verts.antisymm (λ a ha, _),
  obtain ⟨b, hvb, -⟩ := h ha,
  exact ⟨_, hab⟩,
end

lemma is_perfect_matching_iff : G'.is_perfect_matching ↔ ∀ a, ∃! b, G'.weight a b ≠ none :=
begin
  refine ⟨λ h a, h.1 (h.2 a), λ h, ⟨λ a ha, h a, λ a, _⟩⟩,
  obtain ⟨b, hb, -⟩ := h a,
  exact G'.edge_vert h,
end

end subgraph

end weighted_graph
