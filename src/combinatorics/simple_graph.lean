/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson, Jalex Stark, Kyle Miller.
-/
import data.fintype.basic
import data.sym2
import order.bounded_lattice
import tactic
/-!
# Simple graphs

This module defines simple graphs as irreflexive symmetric
relations.  The basic interface is that one defines an instance
`[simple_graphs α]` to declare that every term of `α` has an
interpretation as a simple graph, and then one may write `G : α` to
obtain individual graphs.

To construct a simple graph from a specific relation, one uses
`simple_graph.from_rel`.

There is a basic API for locally finite graphs and for graphs with
finitely many vertices.

## Main definitions

* `simple_graphs` is a class for types whose terms can be interpreted as
  symmetric, irreflexive relations (i.e., simple graphs)

* `neighbor_set` is the `set` of vertices adjacent to a given vertex

* `neighbor_finset` is the `finset` of vertices adjacent to a given vertex,
   if `neighbor_set` is finite

* `subgraph G` is a type of all subgraphs of the simple graph `G`.  The type
  forms a bounded lattice.

## Implementation notes

* A locally finite graph is one with instances `∀ (v : V G), fintype (neighbor_set v)`.

* Given instances `decidable_rel (adj G)` and `fintype (V G)`, then the graph
is locally finite, too.

TODO: This should eventually fit into a more complete combinatorics
hierarchy which includes multigraphs and directed graphs.  We begin
with simple graphs in order to start learning what the combinatorics
hierarchy should look like.
-/
open finset
universes u v

/--
A simple graph is an irreflexive symmetric relation `adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent edges;
see `simple_graphs.edge_set` for the corresponding edge set.

To construct a simple graph, use `simple_graph.from_rel`.

The way the interface works is you define an instance `[simple_graphs α]`
for a type `α`, and then terms `G : α` refer to graphs.
-/
class simple_graphs (α : Type u) :=
(V : α → Type v)
(adj : Π (G : α), V G → V G → Prop)
(symm : Π (G : α), symmetric (adj G) . obviously)
(loopless : Π (G : α), irreflexive (adj G) . obviously)

namespace simple_graph
open simple_graphs

/--
This is `simple_graphs.adj` but with an implicit `G`.  It is used for the
`v ~ w` notation for `(v w : V G)`, meaning `v` and `w` are adjacent.
-/
@[reducible]
abbreviation adj_rel {α : Type u} [simple_graphs α] {G : α} (v w : V G) := adj G v w

local infix ` ~ ` := adj_rel

/--
Basic constructor for a simple graph, using a symmetric irreflexive relation.
-/
structure from_rel (V : Type u) :=
(rel : V → V → Prop)
(sym : symmetric rel . obviously)
(irr : irreflexive rel . obviously)

instance (V : Type u) : simple_graphs (from_rel V) :=
{ V := λ _, V,
  adj := from_rel.rel,
  symm := from_rel.sym,
  loopless := from_rel.irr }

variables {α : Type u} [simple_graphs α] (G : α)

/-- `neighbor_set v` is the set of vertices adjacent to `v` in `G`. -/
def neighbor_set {G : α} (v : V G) : set (V G) := set_of (adj G v)

lemma ne_of_edge {a b : V G} (hab : a ~ b) : a ≠ b :=
by { rintro rfl, exact loopless G a hab }

/--
The edges of G consist of the unordered pairs of vertices related by `adj`.
-/
def edge_set : set (sym2 (V G)) := sym2.from_rel (symm G)

@[simp]
lemma edge_iff_adj {v w : V G} : ⟦(v, w)⟧ ∈ edge_set G ↔ v ~ w :=
by refl

lemma adj_iff_exists_edge {v w : V G} (hne : v ≠ w) :
  v ~ w ↔ ∃ (e ∈ edge_set G), v ∈ e ∧ w ∈ e :=
begin
  split, { intro, use ⟦(v,w)⟧, simpa },
  { rintro ⟨e, he, hv⟩,
    rw sym2.elems_iff_eq hne at hv,
    subst e,
    rwa edge_iff_adj at he, }
end

lemma edge_other_ne {e : sym2 (V G)} (he : e ∈ edge_set G) {v : V G} (h : v ∈ e) : h.other ≠ v :=
begin
  erw [← sym2.mem_other_spec h, sym2.eq_swap] at he,
  exact ne_of_edge G he,
end

instance edges_fintype [decidable_eq (V G)] [fintype (V G)] [decidable_rel (adj G)] :
  fintype (edge_set G) := by { dunfold edge_set, exact subtype.fintype _ }

/--
The `edge_set` of the graph as a `finset`.
-/
def edge_finset [decidable_eq (V G)] [fintype (V G)] [decidable_rel (adj G)] : finset (sym2 (V G)) :=
set.to_finset (edge_set G)

@[simp] lemma mem_edge_finset [decidable_eq (V G)] [fintype (V G)] [decidable_rel (adj G)] (e : sym2 (V G)) :
  e ∈ edge_finset G ↔ e ∈ edge_set G :=
by { dunfold edge_finset, simp }

@[simp] lemma irrefl {v : V G} : ¬(v ~ v) := loopless G v

@[symm] lemma edge_symm (u v : V G) : u ~ v ↔ v ~ u := ⟨λ x, symm G x, λ x, symm G x⟩

@[simp] lemma mem_neighbor_set (v w : V G) : w ∈ neighbor_set v ↔ v ~ w :=
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

variables {G} (v : V G) [fintype (neighbor_set v)]
/--
`G.neighbors v` is the `finset` version of `G.adj v` in case `G` is
locally finite at `v`.
-/
def neighbor_finset : finset (V G) := (neighbor_set v).to_finset

@[simp] lemma mem_neighbor_finset (w : V G) :
  w ∈ neighbor_finset v ↔ v ~ w :=
by simp [neighbor_finset]

/--
`degree v` is the number of vertices adjacent to `v`.
-/
def degree : ℕ := (neighbor_finset v).card

@[simp]
lemma card_neighbor_set_eq_degree : fintype.card (neighbor_set v) = degree v :=
by simp [degree, neighbor_finset]

end finite_at

section locally_finite

/--
A graph is locally finite if every vertex has a finite neighbor set.
-/
@[reducible]
def locally_finite := Π (v : V G), fintype (neighbor_set v)

variable [locally_finite G]

/--
A locally finite simple graph is regular of degree `d` if every vertex has degree `d`.
-/
def is_regular_of_degree (d : ℕ) : Prop := ∀ (v : V G), degree v = d

end locally_finite

section finite

variables [fintype (V G)]

instance neighbor_set_fintype [decidable_rel (adj G)] (v : V G) : fintype (neighbor_set v) :=
  @subtype.fintype _ _ (by { simp_rw mem_neighbor_set, apply_instance }) _

lemma neighbor_finset_eq_filter {v : V G} [decidable_rel (adj G)] :
  neighbor_finset v = finset.univ.filter (adj G v) :=
by { ext, simp }

end finite

section subgraphs

/--
A subgraph of a graph is a subset of vertices and a subset of edges
such that each endpoint of an edge is contained in the vertex set.

Subgraphs implement the `simple_graphs` class.  They also form a bounded lattice.
-/
structure subgraph (G : α) :=
(V' : set (V G))
(E' : set (sym2 (V G)))
(edge_sub : E' ⊆ edge_set G)
(has_verts : ∀ (e ∈ E') (v ∈ e), v ∈ V')

instance subgraph.simple_graphs : simple_graphs (subgraph G) :=
{ V := λ G', G'.V',
  adj := λ G' v w, ⟦(v.val, w.val)⟧ ∈ G'.E',
  symm := λ G' v w h, by rwa sym2.eq_swap,
  loopless := λ G' ⟨v, _⟩ h, loopless G v (sym2.from_rel_prop.mp (G'.edge_sub h)) }

variable {G}

/--
The relation that one subgraph is a subgraph of another.
-/
def is_subgraph (x y : subgraph G) : Prop := x.V' ⊆ y.V' ∧ x.E' ⊆ y.E'

/--
The union of two subgraphs.
-/
def union (x y : subgraph G) : subgraph G :=
{ V' := x.V' ∪ y.V',
  E' := x.E' ∪ y.E',
  edge_sub := λ e h, begin
    cases h,
    exact x.edge_sub h,
    exact y.edge_sub h,
  end,
  has_verts := λ e h v hv, begin
    cases h,
    apply or.inl (x.has_verts e h v hv),
    apply or.inr (y.has_verts e h v hv),
  end }

/--
The intersection of two subgraphs.
-/
def inter (x y : subgraph G) : subgraph G :=
{ V' := x.V' ∩ y.V',
  E' := x.E' ∩ y.E',
  edge_sub := λ e h, x.edge_sub h.1,
  has_verts := λ e h v hv, ⟨x.has_verts e h.1 v hv, y.has_verts e h.2 v hv⟩ }

instance : has_subset (subgraph G) := ⟨is_subgraph⟩
instance : has_union (subgraph G) := ⟨union⟩
instance : has_inter (subgraph G) := ⟨inter⟩

/--
The `top` subgraph is `G` as a subgraph of itself.
-/
def top : subgraph G :=
{ V' := set.univ,
  E' := edge_set G,
  edge_sub := by refl,
  has_verts := by { rintros e he v hv, apply set.mem_univ } }

/--
The `bot` subgraph is the subgraph with no vertices or edges.
-/
def bot : subgraph G :=
{ V' := ∅,
  E' := ∅,
  edge_sub := set.empty_subset _,
  has_verts := set.empty_subset _ }

instance subgraph_inhabited : inhabited (subgraph G) := ⟨bot⟩

instance : bounded_lattice (subgraph G) :=
{ top := top,
  bot := bot,
  le := is_subgraph,
  le_refl := by { intro a, split; refl },
  le_trans := by { intros x y z hxy hyz,
                   exact ⟨set.subset.trans hxy.1 hyz.1, set.subset.trans hxy.2 hyz.2⟩},
  le_antisymm := begin
    intros x y hxy hyx,
    cases x, cases y, congr,
    exact set.subset.antisymm hxy.1 hyx.1,
    exact set.subset.antisymm hxy.2 hyx.2,
  end,
  le_top := λ x, ⟨set.subset_univ _, x.edge_sub⟩,
  bot_le := by { intro a, split; exact set.empty_subset _, },
  sup := union,
  inf := inter,
  sup_le := by { intros x y z hxy hyz,
                 exact ⟨set.union_subset hxy.1 hyz.1, set.union_subset hxy.2 hyz.2⟩, },
  le_sup_left :=
    by { intros x y,
         exact ⟨set.subset_union_left x.V' y.V', set.subset_union_left x.E' y.E'⟩, },
  le_sup_right :=
    by { intros x y,
         exact ⟨set.subset_union_right x.V' y.V', set.subset_union_right x.E' y.E'⟩, },
  le_inf :=
    by { intros x y z hxy hyz, exact ⟨set.subset_inter hxy.1 hyz.1, set.subset_inter hxy.2 hyz.2⟩, },
  inf_le_left :=
    by { intros x y,
         exact ⟨set.inter_subset_left x.V' y.V', set.inter_subset_left x.E' y.E'⟩, },
  inf_le_right :=
    by { intros x y,
         exact ⟨set.inter_subset_right x.V' y.V', set.inter_subset_right x.E' y.E'⟩, } }

/--
The induced subgraph of a graph is the graph with a specified vertex
set along with all the edges whose endpoints lie in the set.
-/
def induced (V' : set (V G)) : subgraph G :=
{ V' := V',
  E' := {e ∈ edge_set G | ∀ v ∈ e, v ∈ V'},
  edge_sub := λ _ ⟨h, _⟩, h,
  has_verts := λ e ⟨he, h⟩ v hv, h v hv, }

end subgraphs

end simple_graph

namespace simple_graph
open simple_graphs

section complete_graphs

/--
The complete graph on a type `α` is the simple graph with all pairs of distinct vertices adjacent.
-/
def complete_graph (α : Type u) : from_rel α :=
{ rel := ne }

instance from_rel_inhabited (α : Type u) : inhabited (from_rel α) :=
⟨complete_graph α⟩

variables (α : Type u) [decidable_eq α]

instance complete_graph_adj_decidable :
  decidable_rel (complete_graph α).rel :=
by { dsimp [complete_graph], apply_instance }

variables [fintype α]

@[simp]
lemma complete_graph_degree (v : V (complete_graph α)) :
  degree v = fintype.card α - 1 :=
begin
  convert univ.card.pred_eq_sub_one,
  erw [degree, neighbor_finset_eq_filter, filter_ne, card_erase_of_mem (mem_univ v)],
end

lemma complete_graph_is_regular :
  is_regular_of_degree (complete_graph α) (fintype.card α - 1) :=
by { intro v, simp }

end complete_graphs

end simple_graph
