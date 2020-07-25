/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson, Jalex Stark, Kyle Miller.
-/
import data.fintype.basic
import data.sym2

open finset
-- noncomputable theory

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

universe u

/--
A simple graph is an irreflexive symmetric relation `adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent edges;
see `simple_graph.E` for the corresponding type of edges.

Note: The type of the relation is given as `V → set V` rather than
`V → V → Prop` so that, given vertices `v` and `w`, then `w ∈ G.adj v`
works as another way to write `G.adj v w`.  Otherwise Lean cannot find
a `has_mem` instance.
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

def neighbor_set (v : V) : set V := set_of (G.adj v)

lemma ne_of_edge {a b : V} (hab : G.adj a b) : a ≠ b :=
by { rintro rfl, exact G.loopless a hab }

/--
The edges of G consist of the unordered pairs of vertices related by
`G.adj`.  It is given as a subtype of the symmetric square.
-/
def E : Type u := {x : sym2 V // x ∈ sym2.from_rel G.sym}

def E.of_adj {v w : V} (h : G.adj v w) : G.E := ⟨⟦(v,w)⟧, h⟩
-- begin
--   fsplit,
-- end

/-- Allows us to refer to a vertex being a member of an edge. -/
instance E.has_mem : has_mem V G.E := { mem := λ v e, v ∈ e.val }

lemma adj_iff_exists_edge {v w : V} (hne : v ≠ w) :
G.adj v w ↔ ∃ (e : G.E), v ∈ e ∧ w ∈ e :=
begin
  split, { intro, use ⟦(v,w)⟧, assumption, iterate 2 { erw sym2.mem_iff }, simp },
  rintro ⟨e, ⟨w', hve⟩, ⟨v', hew⟩⟩,
  have : e.val = ⟦(v,w)⟧, { rw [hve, sym2.eq_iff] at hew ⊢, cc },
  have key := e.property, rwa this at key,
end

variables {G}

noncomputable def E.other (e : G.E) {v : V} (h : v ∈ e) : V :=
by { have : v ∈ e.val, apply h, exact this.other }

lemma E.other_mem (e : G.E) {v : V} (h : v ∈ e) : e.other h ∈ e :=
begin
  change sym2.mem.other h ∈ e.val, have := sym2.mem_other_spec h,
  convert sym2.mk_has_mem_right _ _; tauto,
end

lemma E.other_ne (e : G.E) {v : V} (h : v ∈ e) : e.other h ≠ v :=
begin
  have key := e.property,
  erw [← sym2.mem_other_spec h, sym2.eq_swap] at key,
  exact G.ne_of_edge key,
end

attribute [irreducible] E.other
variables (G)

instance E.inhabited [inhabited {p : V × V | G.adj p.1 p.2}] : inhabited G.E :=
⟨begin
  rcases inhabited.default {p : V × V | G.adj p.1 p.2} with ⟨⟨x, y⟩, h⟩,
  use ⟦(x, y)⟧, rwa sym2.from_rel_prop,
end⟩

instance edges_fintype [decidable_eq V] [fintype V] [decidable_rel G.adj] :
  fintype G.E := subtype.fintype _

attribute [irreducible] E

@[simp] lemma irrefl {v : V} : ¬G.adj v v := G.loopless v

@[symm] lemma edge_symm (u v : V) : G.adj u v ↔ G.adj v u :=
by split; apply G.sym

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

variable [∀ (v : V), fintype (G.neighbor_set v)]

/--
A regular graph is a locally finite graph such that every vertex has the same degree.
-/
def regular_graph (d : ℕ) : Prop := ∀ (v : V), G.degree v = d

end locally_finite

section finite

variables [fintype V]

instance neighbor_set_fintype [decidable_rel G.adj] (v : V) : fintype (G.neighbor_set v) :=
  @subtype.fintype _ _ (by {simp_rw mem_neighbor_set, apply_instance}) _

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
  regular_graph (complete_graph V) (fintype.card V - 1) :=
by { intro v, simp }

end finite

end simple_graph
