/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov
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

* `incidence_set` is the `set` of edges containing a given vertex

* `incidence_finset` is the `finset` of edges containing a given vertex,
   if `incidence_set` is finite

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
@[ext]
structure simple_graph (V : Type u) :=
(adj : V → V → Prop)
(sym : symmetric adj . obviously)
(loopless : irreflexive adj . obviously)

/--
Construct the simple graph induced by the given relation.  It
symmetrizes the relation and makes it irreflexive.
-/
def simple_graph.from_rel {V : Type u} (r : V → V → Prop) : simple_graph V :=
{ adj := λ a b, (a ≠ b) ∧ (r a b ∨ r b a),
  sym := λ a b ⟨hn, hr⟩, ⟨hn.symm, hr.symm⟩,
  loopless := λ a ⟨hn, _⟩, hn rfl }

noncomputable instance {V : Type u} [fintype V] : fintype (simple_graph V) :=
by { classical, exact fintype.of_injective simple_graph.adj simple_graph.ext }

@[simp]
lemma simple_graph.from_rel_adj {V : Type u} (r : V → V → Prop) (v w : V) :
  (simple_graph.from_rel r).adj v w ↔ v ≠ w ∧ (r v w ∨ r w v) :=
by refl

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

/--
The `incidence_set` is the set of edges incident to a given vertex.
-/
def incidence_set (v : V) : set (sym2 V) := {e ∈ G.edge_set | v ∈ e}

lemma incidence_set_subset (v : V) : G.incidence_set v ⊆ G.edge_set :=
λ _ h, h.1

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
  refine ⟨λ _, ⟨G.ne_of_adj ‹_›, ⟦(v,w)⟧, _⟩, _⟩,
  { simpa },
  { rintro ⟨hne, e, he, hv⟩,
    rw sym2.elems_iff_eq hne at hv,
    subst e,
    rwa mem_edge_set at he }
end

lemma edge_other_ne {e : sym2 V} (he : e ∈ G.edge_set) {v : V} (h : v ∈ e) : h.other ≠ v :=
begin
  erw [← sym2.mem_other_spec h, sym2.eq_swap] at he,
  exact G.ne_of_adj he,
end

instance edges_fintype [decidable_eq V] [fintype V] [decidable_rel G.adj] :
  fintype G.edge_set := by { dunfold edge_set, exact subtype.fintype _ }

instance mem_edge_set_decidable [decidable_rel G.adj] (e : sym2 V) :
  decidable (e ∈ G.edge_set) := by { dunfold edge_set, apply_instance }

instance mem_incidence_set_decidable [decidable_eq V] [decidable_rel G.adj] (v : V) (e : sym2 V) :
  decidable (e ∈ G.incidence_set v) := by { dsimp [incidence_set], apply_instance }

/--
The `edge_set` of the graph as a `finset`.
-/
def edge_finset [decidable_eq V] [fintype V] [decidable_rel G.adj] : finset (sym2 V) :=
set.to_finset G.edge_set

@[simp] lemma mem_edge_finset [decidable_eq V] [fintype V] [decidable_rel G.adj] (e : sym2 V) :
  e ∈ G.edge_finset ↔ e ∈ G.edge_set :=
by { dunfold edge_finset, simp }

@[simp] lemma edge_set_univ_card [decidable_eq V] [fintype V] [decidable_rel G.adj] :
  (univ : finset G.edge_set).card = G.edge_finset.card :=
fintype.card_of_subtype G.edge_finset (mem_edge_finset _)

@[simp] lemma irrefl {v : V} : ¬G.adj v v := G.loopless v

@[symm] lemma edge_symm (u v : V) : G.adj u v ↔ G.adj v u := ⟨λ x, G.sym x, λ x, G.sym x⟩

@[simp] lemma mem_neighbor_set (v w : V) : w ∈ G.neighbor_set v ↔ G.adj v w :=
by tauto

@[simp] lemma mem_incidence_set (v w : V) : ⟦(v, w)⟧ ∈ G.incidence_set v ↔ G.adj v w :=
by simp [incidence_set]

lemma mem_incidence_iff_neighbor {v w : V} : ⟦(v, w)⟧ ∈ G.incidence_set v ↔ w ∈ G.neighbor_set v :=
by simp only [mem_incidence_set, mem_neighbor_set]

lemma adj_incidence_set_inter {v : V} {e : sym2 V} (he : e ∈ G.edge_set) (h : v ∈ e) :
  G.incidence_set v ∩ G.incidence_set h.other = {e} :=
begin
  ext e',
  simp only [incidence_set, set.mem_sep_eq, set.mem_inter_eq, set.mem_singleton_iff],
  split,
  { intro h', rw ←sym2.mem_other_spec h,
    exact (sym2.elems_iff_eq (edge_other_ne G he h).symm).mp ⟨h'.1.2, h'.2.2⟩, },
  { rintro rfl, use [he, h, he], apply sym2.mem_other_mem, },
end

section incidence
variable [decidable_eq V]

/--
Given an edge incident to a particular vertex, get the other vertex on the edge.
-/
def other_vertex_of_incident {v : V} {e : sym2 V} (h : e ∈ G.incidence_set v) : V := h.2.other'

lemma edge_mem_other_incident_set {v : V} {e : sym2 V} (h : e ∈ G.incidence_set v) :
  e ∈ G.incidence_set (G.other_vertex_of_incident h) :=
by { use h.1, simp [other_vertex_of_incident, sym2.mem_other_mem'] }

lemma incidence_other_prop {v : V} {e : sym2 V} (h : e ∈ G.incidence_set v) :
  G.other_vertex_of_incident h ∈ G.neighbor_set v :=
by { cases h with he hv, rwa [←sym2.mem_other_spec' hv, mem_edge_set] at he }

@[simp]
lemma incidence_other_neighbor_edge {v w : V} (h : w ∈ G.neighbor_set v) :
  G.other_vertex_of_incident (G.mem_incidence_iff_neighbor.mpr h) = w :=
sym2.congr_right.mp (sym2.mem_other_spec' (G.mem_incidence_iff_neighbor.mpr h).right)

/--
There is an equivalence between the set of edges incident to a given
vertex and the set of vertices adjacent to the vertex.
-/
@[simps] def incidence_set_equiv_neighbor_set (v : V) : G.incidence_set v ≃ G.neighbor_set v :=
{ to_fun := λ e, ⟨G.other_vertex_of_incident e.2, G.incidence_other_prop e.2⟩,
  inv_fun := λ w, ⟨⟦(v, w.1)⟧, G.mem_incidence_iff_neighbor.mpr w.2⟩,
  left_inv := λ x, by simp [other_vertex_of_incident],
  right_inv := λ ⟨w, hw⟩, by simp }

end incidence

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

lemma degree_pos_iff_exists_adj : 0 < G.degree v ↔ ∃ w, G.adj v w :=
by simp only [degree, card_pos, finset.nonempty, mem_neighbor_finset]

instance incidence_set_fintype [decidable_eq V] : fintype (G.incidence_set v) :=
fintype.of_equiv (G.neighbor_set v) (G.incidence_set_equiv_neighbor_set v).symm

/--
This is the `finset` version of `incidence_set`.
-/
def incidence_finset [decidable_eq V] : finset (sym2 V) := (G.incidence_set v).to_finset

@[simp]
lemma card_incidence_set_eq_degree [decidable_eq V] :
  fintype.card (G.incidence_set v) = G.degree v :=
by { rw fintype.card_congr (G.incidence_set_equiv_neighbor_set v), simp }

@[simp]
lemma mem_incidence_finset [decidable_eq V] (e : sym2 V) :
  e ∈ G.incidence_finset v ↔ e ∈ G.incidence_set v :=
set.mem_to_finset

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

/--
The minimum degree of all vertices
-/
def min_degree (G : simple_graph V) [nonempty V] [decidable_rel G.adj] : ℕ :=
finset.min' (univ.image (λ (v : V), G.degree v)) (nonempty.image univ_nonempty _)

/--
The maximum degree of all vertices
-/
def max_degree (G : simple_graph V) [nonempty V] [decidable_rel G.adj] : ℕ :=
finset.max' (univ.image (λ (v : V), G.degree v)) (nonempty.image univ_nonempty _)


end finite

end simple_graph
