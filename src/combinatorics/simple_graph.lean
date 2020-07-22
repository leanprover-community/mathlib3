/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson, Jalex Stark, Kyle Miller.
-/
import data.fintype.basic
import data.sym2

open finset

/-!
# Simple graphs

This module defines simple graphs on a vertex type `V` as an
irreflexive symmetric relation.

There is a basic API for locally finite graphs and for graphs with
finitely many vertices.

* A locally finite graph is one with instances `∀ v, fintype (G.adj v)`.

* Given instances `decidable_rel G.adj` and `fintype V`, then the graph
is locally finite, too.


## Implementation notes

TODO: This is the simplest notion of an unoriented graph.  This should
eventually fit into a more complete combinatorics hierarchy which
includes multigraphs and directed graphs.  We begin with simple graphs
in order to start learning what the combinatorics hierarchy should
look like.

TODO: Part of this would include defining, for example, subgraphs of a
simple graph.

-/

universe u

/--
A simple graph is an irreflexive symmetric relation `adj` on a vertex
type `V`.  The relation describes which pairs of vertices are
adjacent.  There is exactly one edge for every pair of adjacent edges;
see `simple_graph.E` for the corresponding type of edges.

Note: The type of the relation is given as `V → set V` rather than
`V → V → Prop` so that, given vertices `v` and `w`, then `w ∈ G.adj v`
works as another way to write `G.adj v w`.  Otherwise Lean cannot find
a `has_mem` instance.
-/
structure simple_graph (V : Type u) :=
(adj : V → set V)
(sym : symmetric adj . obviously)
(loopless : irreflexive adj . obviously)

/--
The complete graph on a type `V` is the simple graph where all pairs of distinct vertices are adjacent.
-/
def complete_graph (V : Type u) : simple_graph V :=
{ adj := λ v w, v ≠ w }

instance (V : Type u) : inhabited (simple_graph V) :=
⟨complete_graph V⟩

instance complete_graph_adj_decidable (V : Type u) [decidable_eq V] :
  decidable_rel (complete_graph V).adj :=
by { dsimp [complete_graph], apply_instance }

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/--
The edges of G consist of the unordered pairs of vertices related by
`G.adj`.  It is given as a subtype of the symmetric square.
-/
def E : Type u := { x : sym2 V // x ∈ sym2.from_rel G.sym }

instance E.inhabited [inhabited {p : V × V | G.adj p.1 p.2}] : inhabited G.E :=
⟨begin
  rcases inhabited.default {p : V × V | G.adj p.1 p.2} with ⟨⟨x, y⟩, h⟩,
  use ⟦(x, y)⟧,
  rwa sym2.from_rel_prop,
end⟩

@[simp] lemma irrefl {v : V} : ¬G.adj v v := G.loopless v

@[symm] lemma edge_symm (u v : V) : G.adj u v ↔ G.adj v u :=
by split; apply G.sym

lemma ne_of_edge {a b : V} (hab : G.adj a b) : a ≠ b :=
by { intro h, rw h at hab, apply G.loopless b, exact hab }

@[simp] lemma in_adj_iff_adj (v w : V) : w ∈ G.adj v ↔ G.adj v w :=
by tauto

/--
`G.incident v` is the set of edges incident to `v`.  Due to the way
sets are defined, `G.incident v e` denotes that `v` is incident to `e`.

As a convenience, we define a `has_mem` instance by `v ∈ e = G.incident v e`.
-/
def incident (v : V) : set G.E := {e : G.E | v ∈ e.1}

instance incident.has_mem : has_mem V G.E :=
⟨incident G⟩


section finite_at

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote this condition by
`fintype (G.adj v)`.

We define `G.neighbors v` to be the `finset` version of `G.adj v`.
Use `neighbors_eq_filter` to rewrite this definition as a `filter`.
-/

/--
`G.neighbors v` is the `finset` version of `G.adj v` in case `G` is
locally finite at `v`.
-/
def neighbors (v : V) [fintype (G.adj v)] : finset V := set.to_finset (G.adj v)

@[simp] lemma in_neighbors_iff_in_adj (v w : V) [fintype (G.adj v)] :
  w ∈ G.neighbors v ↔ w ∈ G.adj v :=
by simp [neighbors]

/--
`G.degree v` is the number of vertices adjacent to `v`.
-/
def degree (v : V) [fintype (G.adj v)] : ℕ := (G.neighbors v).card

@[simp]
lemma adj_card_is_degree (v : V) [fintype (G.adj v)] : fintype.card (G.adj v) = G.degree v :=
by simp [degree, neighbors]

end finite_at


section locally_finite

variable [∀ (v : V), fintype (G.adj v)]

/--
A regular graph is a locally finite graph such that every vertex has the same degree.
-/
def regular_graph (d : ℕ) : Prop := ∀ (v : V), G.degree v = d

end locally_finite


section finite

variables [fintype V]

instance edges_fintype [decidable_eq V] [decidable_rel G.adj] : fintype G.E := subtype.fintype _

@[simp] lemma neighbors_eq_filter {v : V} [decidable_pred (G.adj v)] :
  G.neighbors v = finset.univ.filter (G.adj v) :=
by {ext, simp}

@[simp]
lemma complete_graph_degree [decidable_eq V] (v : V) :
  (complete_graph V).degree v = fintype.card V - 1 :=
begin
  dsimp [complete_graph, degree],
  rw neighbors_eq_filter,
  change (finset.univ.filter (λ w, v ≠ w)).card = univ.card - 1,
  rw [filter_ne, card_erase_of_mem (mem_univ v)],
  exact univ.card.pred_eq_sub_one,
end

lemma complete_graph_is_regular [decidable_eq V] :
  regular_graph (complete_graph V) (fintype.card V - 1) :=
by { intro v, simp }

end finite

end simple_graph
