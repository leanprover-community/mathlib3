/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson, Jalex Stark, Kyle Miller.
-/
import data.fintype.basic
import data.sym2
/-!
# Simple graphs

This module defines simple graphs on a vertex type `V` as an
irreflexive symmetric relation.

There is a basic API for locally finite graphs and for graphs with
finitely many vertices.

## Main definitions

* `simple_graph` is a structure for symmetric, irreflexive relations

* `neighbor_set` is the `set` of vertices adjacent to a given vertex

* `neighbor_finset` is the `finset` of vertices adjacent to a given vertex,
   if `neighbor_set` is finite

## Implementation notes

* A locally finite graph is one with instances `∀ v, fintype (G.neighbor_set v)`.

* Given instances `decidable_rel G.adj` and `fintype V`, then the graph
is locally finite, too.

TODO: This is the simplest notion of an unoriented graph.  This should
eventually fit into a more complete combinatorics hierarchy which
includes multigraphs and directed graphs.  We begin with simple graphs
in order to start learning what the combinatorics hierarchy should
look like.

TODO: Part of this would include defining, for example, subgraphs of a
simple graph.

-/
open finset
universe u

/--
A simple graph is an irreflexive symmetric relation `adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent edges;
see `simple_graph.edge_set` for the corresponding edge set.
-/
structure simple_graph (V : Type u) :=
(adj : V → V → Prop)
(sym : symmetric adj . obviously)
(loopless : irreflexive adj . obviously)

/--
The complete graph on a type `V` is the simple graph with all pairs of distinct vertices adjacent.
-/
def complete_graph (V : Type u) : simple_graph V :=
{ adj := ne }

instance (V : Type u) : inhabited (simple_graph V) :=
⟨complete_graph V⟩

instance complete_graph_adj_decidable (V : Type u) [decidable_eq V] :
  decidable_rel (complete_graph V).adj :=
by { dsimp [complete_graph], apply_instance }

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/-- `G.neighbor_set v` is the set of vertices adjacent to `v` in `G`. -/
def neighbor_set (v : V) : set V := set_of (G.adj v)

lemma ne_of_adj {a b : V} (hab : G.adj a b) : a ≠ b :=
by { rintro rfl, exact G.loopless a hab }

/--
The edges of G consist of the unordered pairs of vertices related by
`G.adj`.
-/
def edge_set : set (sym2 V) := sym2.from_rel G.sym

@[simp]
lemma mem_edge_set {v w : V} : ⟦(v, w)⟧ ∈ G.edge_set ↔ G.adj v w :=
by refl

/--
Two vertices are adjacent iff there is an edge between them.  The
condition `v ≠ w` ensures they are different endpoints of the edge,
which is necessary since when `v = w` the existential
`∃ (e ∈ G.edge_set), v ∈ e ∧ w ∈ e` is satisfied by every edge
incident to `v`.
-/
lemma adj_iff_exists_edge {v w : V} :
  G.adj v w ↔ v ≠ w ∧ ∃ (e ∈ G.edge_set), v ∈ e ∧ w ∈ e :=
begin
  split, { intro, split, { exact G.ne_of_adj ‹_›, }, {use ⟦(v,w)⟧, simpa} },
  { rintro ⟨hne, e, he, hv⟩,
    rw sym2.elems_iff_eq hne at hv,
    subst e,
    rwa mem_edge_set at he, }
end

lemma edge_other_ne {e : sym2 V} (he : e ∈ G.edge_set) {v : V} (h : v ∈ e) : h.other ≠ v :=
begin
  erw [← sym2.mem_other_spec h, sym2.eq_swap] at he,
  exact G.ne_of_adj he,
end

instance edges_fintype [decidable_eq V] [fintype V] [decidable_rel G.adj] :
  fintype G.edge_set := by { dunfold edge_set, exact subtype.fintype _ }

/--
The `edge_set` of the graph as a `finset`.
-/
def edge_finset [decidable_eq V] [fintype V] [decidable_rel G.adj] : finset (sym2 V) :=
set.to_finset G.edge_set

@[simp] lemma mem_edge_finset [decidable_eq V] [fintype V] [decidable_rel G.adj] (e : sym2 V) :
  e ∈ G.edge_finset ↔ e ∈ G.edge_set :=
by { dunfold edge_finset, simp }

@[simp] lemma irrefl {v : V} : ¬G.adj v v := G.loopless v

@[symm] lemma edge_symm (u v : V) : G.adj u v ↔ G.adj v u := ⟨λ x, G.sym x, λ x, G.sym x⟩

@[simp] lemma mem_neighbor_set (v w : V) : w ∈ G.neighbor_set v ↔ G.adj v w :=
by tauto

section finite_at

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote this condition by
`fintype (G.neighbor_set v)`.

We define `G.neighbor_finset v` to be the `finset` version of `G.neighbor_set v`.
Use `neighbor_finset_eq_filter` to rewrite this definition as a `filter`.
-/

variables (v : V) [fintype (G.neighbor_set v)]
/--
`G.neighbors v` is the `finset` version of `G.adj v` in case `G` is
locally finite at `v`.
-/
def neighbor_finset : finset V := (G.neighbor_set v).to_finset

@[simp] lemma mem_neighbor_finset (w : V) :
  w ∈ G.neighbor_finset v ↔ G.adj v w :=
by simp [neighbor_finset]

/--
`G.degree v` is the number of vertices adjacent to `v`.
-/
def degree : ℕ := (G.neighbor_finset v).card

@[simp]
lemma card_neighbor_set_eq_degree : fintype.card (G.neighbor_set v) = G.degree v :=
by simp [degree, neighbor_finset]

end finite_at

section locally_finite

/--
A graph is locally finite if every vertex has a finite neighbor set.
-/
@[reducible]
def locally_finite := Π (v : V), fintype (G.neighbor_set v)

variable [locally_finite G]

/--
A locally finite simple graph is regular of degree `d` if every vertex has degree `d`.
-/
def is_regular_of_degree (d : ℕ) : Prop := ∀ (v : V), G.degree v = d

end locally_finite

section finite

variables [fintype V]

instance neighbor_set_fintype [decidable_rel G.adj] (v : V) : fintype (G.neighbor_set v) :=
@subtype.fintype _ _ (by { simp_rw mem_neighbor_set, apply_instance }) _

lemma neighbor_finset_eq_filter {v : V} [decidable_rel G.adj] :
  G.neighbor_finset v = finset.univ.filter (G.adj v) :=
by { ext, simp }

@[simp]
lemma complete_graph_degree [decidable_eq V] (v : V) :
  (complete_graph V).degree v = fintype.card V - 1 :=
begin
  convert univ.card.pred_eq_sub_one,
  erw [degree, neighbor_finset_eq_filter, filter_ne, card_erase_of_mem (mem_univ v)],
end

lemma complete_graph_is_regular [decidable_eq V] :
  (complete_graph V).is_regular_of_degree (fintype.card V - 1) :=
by { intro v, simp }

end finite

end simple_graph
