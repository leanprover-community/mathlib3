/-
Copyright (c) 2020 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Arthur Paulino, Kyle Miller
-/
import combinatorics.simple_graph.degree_sum
import combinatorics.simple_graph.subgraph

/-!
# Matchings

A *matching* for a simple graph is a set of disjoint pairs of adjacent vertices, and the set of all
the vertices in a matching is called its *support* (and sometimes the vertices in the support are
said to be *saturated* by the matching). A *perfect matching* is a matching whose support contains
every vertex of the graph.

In this module, we represent a matching as a subgraph whose vertices are each incident to at most
one edge, and the edges of the subgraph represent the paired vertices.

## Main definitions

* `simple_graph.subgraph.is_matching`: `M.is_matching` means that `M` is a matching of its
  underlying graph.
  denoted `M.is_matching`.

* `simple_graph.subgraph.is_perfect_matching` defines when a subgraph `M` of a simple graph is a
  perfect matching, denoted `M.is_perfect_matching`.

## TODO

* Define an `other` function and prove useful results about it (https://leanprover.zulipchat.com/#narrow/stream/252551-graph-theory/topic/matchings/near/266205863)

* Provide a bicoloring for matchings (https://leanprover.zulipchat.com/#narrow/stream/252551-graph-theory/topic/matchings/near/265495120)

* Tutte's Theorem

* Hall's Marriage Theorem (see combinatorics.hall)
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

/-- Given a vertex, returns the unique edge of the matching it is incident to. -/
noncomputable def is_matching.to_edge {M : subgraph G} (h : M.is_matching)
  (v : M.verts) : M.edge_set :=
⟨⟦(v, (h v.property).some)⟧, (h v.property).some_spec.1⟩

lemma is_matching.to_edge_eq_of_adj {M : subgraph G} (h : M.is_matching) {v w : V}
  (hv : v ∈ M.verts) (hvw : M.adj v w) : h.to_edge ⟨v, hv⟩ = ⟨⟦(v, w)⟧, hvw⟩ :=
begin
  simp only [is_matching.to_edge, subtype.mk_eq_mk],
  congr,
  exact ((h (M.edge_vert hvw)).some_spec.2 w hvw).symm,
end

lemma is_matching.to_edge.surjective {M : subgraph G} (h : M.is_matching) :
  function.surjective h.to_edge :=
begin
  rintro ⟨e, he⟩,
  refine sym2.ind (λ x y he, _) e he,
  exact ⟨⟨x, M.edge_vert he⟩, h.to_edge_eq_of_adj _ he⟩,
end

lemma is_matching.to_edge_eq_to_edge_of_adj {M : subgraph G} {v w : V}
  (h : M.is_matching) (hv : v ∈ M.verts) (hw : w ∈ M.verts) (ha : M.adj v w) :
  h.to_edge ⟨v, hv⟩ = h.to_edge ⟨w, hw⟩ :=
by rw [h.to_edge_eq_of_adj hv ha, h.to_edge_eq_of_adj hw (M.symm ha),
       subtype.mk_eq_mk, sym2.eq_swap]

/--
The subgraph `M` of `G` is a perfect matching on `G` if it's a matching and every vertex `G` is
matched.
-/
def is_perfect_matching : Prop := M.is_matching ∧ M.is_spanning

lemma is_matching.support_eq_verts {M : subgraph G} (h : M.is_matching) : M.support = M.verts :=
begin
  refine M.support_subset_verts.antisymm (λ v hv, _),
  obtain ⟨w, hvw, -⟩ := h hv,
  exact ⟨_, hvw⟩,
end

lemma is_matching_iff_forall_degree {M : subgraph G} [Π (v : V), fintype (M.neighbor_set v)] :
  M.is_matching ↔ ∀ (v : V), v ∈ M.verts → M.degree v = 1 :=
by simpa [degree_eq_one_iff_unique_adj]

lemma is_matching.even_card {M : subgraph G} [fintype M.verts] (h : M.is_matching) :
  even M.verts.to_finset.card :=
begin
  classical,
  rw is_matching_iff_forall_degree at h,
  use M.coe.edge_finset.card,
  rw [← two_mul, ← M.coe.sum_degrees_eq_twice_card_edges],
  simp [h, finset.card_univ],
end

lemma is_perfect_matching_iff : M.is_perfect_matching ↔ ∀ v, ∃! w, M.adj v w :=
begin
  refine ⟨_, λ hm, ⟨λ v hv, hm v, λ v, _⟩⟩,
  { rintro ⟨hm, hs⟩ v,
    exact hm (hs v) },
  { obtain ⟨w, hw, -⟩ := hm v,
    exact M.edge_vert hw }
end

lemma is_perfect_matching_iff_forall_degree {M : subgraph G} [Π v, fintype (M.neighbor_set v)] :
  M.is_perfect_matching ↔ ∀ v, M.degree v = 1 :=
by simp [degree_eq_one_iff_unique_adj, is_perfect_matching_iff]

lemma is_perfect_matching.even_card {M : subgraph G} [fintype V] (h : M.is_perfect_matching) :
  even (fintype.card V) :=
by { classical, simpa [h.2.card_verts] using is_matching.even_card h.1 }

end subgraph

end simple_graph
