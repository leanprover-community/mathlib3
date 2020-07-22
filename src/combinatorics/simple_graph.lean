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

## Implementation notes

TODO: This is the simplest notion of an unoriented graph.  This should
eventually fit into a more complete combinatorics hierarchy which
includes multigraphs and directed graphs.  We begin with simple graphs
in order to start learning what the combinatorics hierarchy should
look like.

TODO: Part of would include defining, for example, subgraphs of a
simple graph.

-/

universe u

/--
A simple graph is an irreflexive symmetric relation `adj` on a vertex
type `V`.  The relation describes which pairs of vertices are
adjacent.  There is exactly one edge for every pair of adjacent edges;
see `simple_graph.E` for the corresponding type of edges.
-/
structure simple_graph (V : Type u) :=
(adj : V → V → Prop)
(sym : symmetric adj . obviously)
(loopless : irreflexive adj . obviously)

/--
The complete graph on a type `V` is the simple graph where all pairs of distinct vertices are adjacent.
-/
def complete_graph (V : Type u) : simple_graph V :=
{ adj := λ v w, v ≠ w,
  sym := by tidy,
  loopless := by tidy }

instance (V : Type u) : inhabited (simple_graph V) :=
⟨complete_graph V⟩

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/--
The edges of G consist of the unordered pairs of vertices related by
`G.adj`.  It is given as a subtype of the symmetric square.
-/
def E : Type u := { x : sym2 V // x ∈ sym2.from_rel G.sym }

instance E.inhabited [inhabited {p : V × V | G.adj p.1 p.2}] : inhabited G.E :=
{ default := begin
  rcases inhabited.default {p : V × V | G.adj p.1 p.2} with ⟨⟨x, y⟩, h⟩,
  use ⟦(x, y)⟧,
  rwa sym2.from_rel_prop,
end }

@[simp] lemma irrefl {v : V} : ¬ G.adj v v := G.loopless v

@[symm] lemma edge_symm (u v : V) : G.adj u v ↔ G.adj v u :=
by split; apply G.sym

lemma ne_of_edge {a b : V} (hab : G.adj a b) : a ≠ b :=
by { intro h, rw h at hab, apply G.loopless b, exact hab }

/--
`G.neighbors v` is the set of vertices adjacent to `v`.
-/
def neighbors (v : V) : set V := G.adj v

@[simp] lemma neighbor_iff_adjacent (v w : V) :
  w ∈ G.neighbors v ↔ G.adj v w :=
by { tauto }

/--
`G.incident v` is the set of edges incident to `v`.  Due to the way
sets are defined, `G.incident v e` denotes that `v` is incident to `e`.
-/
def incident (v : V) : set (G.E) := {e : G.E | v ∈ e.1}


section finite

instance edges_fintype [decidable_eq V] [decidable_rel G.adj] [fintype V] : fintype G.E :=
subtype.fintype _

/--
A graph with finitely many vertices is locally finite.
-/
instance neighbors_fintype [decidable_rel G.adj] [fintype V] (v : V) : fintype (G.neighbors v) :=
by { dsimp [neighbors], apply_instance }

/--
`G.degree v` is the number of vertices adjacent to `v`.
-/
def degree (v : V) [fintype (G.neighbors v)] : ℕ := fintype.card (neighbors G v)

/--
A regular graph is a locally finite graph such that every vertex has the same degree.
-/
def regular_graph [∀ (v : V), fintype (G.neighbors v)] (d : ℕ) : Prop :=
 ∀ v : V, degree G v = d

instance complete_graph_adj_decidable [decidable_eq V] : decidable_rel (complete_graph V).adj :=
by { dsimp [complete_graph], apply_instance }

lemma complete_graph_is_regular [fintype V] [decidable_eq V] : regular_graph (complete_graph V) (fintype.card V - 1) :=
begin
  intro v,
  change fintype.card {w : V | v ≠ w} = fintype.card V - 1,
  have h : fintype.card {w : V | v ≠ w} = (univ.filter (ne v)).card := by tidy,
  rw h,
  change _ = univ.card - 1,
  rw filter_ne,
  rw card_erase_of_mem (mem_univ v),
  exact univ.card.pred_eq_sub_one,
end

end finite

end simple_graph
