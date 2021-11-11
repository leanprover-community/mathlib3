/-
Copyright (c) 2020 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Arthur Paulino
-/
import combinatorics.simple_graph.subgraph
import combinatorics.simple_graph.degree_sum

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
The subgraph `M` of `G` is a matching if every vertex of `M` forms exactly one edge in `M`.
-/
structure is_matching : Prop :=
(disjoint : ∀ ⦃v w w': V⦄, M.adj v w → M.adj v w' → w = w')
(verts_eq_support : M.verts = M.support)

/--
`M` is a perfect matching on `G` if it's a matching and if every vertex forms an edge of `G`.
-/
def is_perfect_matching : Prop := M.is_matching ∧ M.is_spanning

lemma is_matching_iff : M.is_matching ↔ ∀ (v ∈ M.support), ∃! (w ∈ M.support), M.adj v w :=
begin
  sorry
end

lemma is_perfect_iff : M.is_perfect_matching ↔ ∀ (v : V), ∃! (w : V), M.adj v w :=
begin
  simp [is_perfect_matching, is_matching_iff, subgraph.is_spanning, exists_unique],
  split,
  { intros h v,
    cases h with ee ss,
    sorry, },
  { intro h,
    split,
    { intros v hv,
      sorry, },
    { intro v,
      sorry, }, },
end

end subgraph

end simple_graph
