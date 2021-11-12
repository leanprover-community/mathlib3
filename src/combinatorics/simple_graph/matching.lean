/-
Copyright (c) 2020 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Arthur Paulino, Kyle Miller
-/
import combinatorics.simple_graph.subgraph

/-!
# Matchings

The idea of a matching refers to the pairing of adjacent vertices. In this approach we're
representing a matching as a subgraph that contains all vertices of a graph.

## Main definitions

* A *matching* `M` on a simple graph `G` is a subgraph of `G`, such that every vertex of `G` is a
  vertex of `M` and no two edges of `M` share an endpoint.

* A *perfect matching* on a simple graph is a matching in which every vertex forms an edge.

## Todo

* Lemma stating that the existence of a perfect matching on `G` implies that
  the cardinality of `V` is even (assuming it's finite)

* Hall's Marriage Theorem (see combinatorics.hall)

* Tutte's Theorem

* https://github.com/leanprover-community/mathlib/pull/5156#discussion_r532906131
-/

universe u

namespace simple_graph
variables {V : Type u} {G : simple_graph V} (M : subgraph G)

namespace subgraph

/--
The subgraph `M` of `G` is a matching if every vertex of `M` is incident to exactly one edge in `M`.
We say that the vertices in `M.support` are *matched* or *saturated*.
-/
def is_matching : Prop := ∀ ⦃v⦄, v ∈ M.verts → ∃! w, M.adj v w

/--
`M` is a perfect matching on `G` if it's a matching and every vertex `G` is matched.
-/
def is_perfect_matching : Prop := M.is_matching ∧ M.is_spanning

lemma support_eq_verts {M : subgraph G} (h : M.is_matching) : M.support = M.verts :=
begin
  rw set.subset.antisymm_iff,
  split,
  { exact M.support_subset_verts, },
  { intros v hv,
    obtain ⟨w, hvw, -⟩ := h hv,
    exact ⟨_, hvw⟩, },
end

lemma is_perfect_matching_iff : M.is_perfect_matching ↔ ∀ (v : V), ∃! (w : V), M.adj v w :=
begin
  refine ⟨_, λ hm, ⟨λ v hv, hm v, λ v, _⟩⟩,
  { rintro ⟨hm, hs⟩ v,
    exact hm (hs v) },
  { obtain ⟨w, hw, -⟩ := hm v,
    exact M.edge_vert hw }
end

end subgraph

end simple_graph
