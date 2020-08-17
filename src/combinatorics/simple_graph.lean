/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson, Jalex Stark, Kyle Miller.
-/
import data.fintype.basic
import data.sym2
import data.equiv.basic
import order.bounded_lattice
import algebra.big_operators
import tactic
/-!
# Simple graphs

This module defines simple graphs as irreflexive symmetric relations.
Since graphs are terms, the basic interface is that a term `G` is a
simple graph if there is an instance `[simple_graph G]`.

To construct a simple graph from a specific relation, one uses
`simple_graph.from_adj_rel`.

There is a basic API for locally finite graphs and for graphs with
finitely many vertices.

## Main definitions

* `simple_graph` is a class for terms that can be interpreted as
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
open_locale big_operators
universes u v

/--
A simple graph is an irreflexive symmetric relation `adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent edges;
see `simple_graph.edge_set` for the corresponding edge set.

To construct a simple graph, use `simple_graph.from_rel`.
-/
class simple_graph {α : Type u} (G : α) :=
(V : Type v)
(adj : V → V → Prop)
(symm [] : symmetric adj . obviously)
(loopless [] : irreflexive adj . obviously)

namespace simple_graph

/--
This is `simple_graph.adj` but with an explicit `G`.  It is used for situations such as `[decidable_rel (adj_rel G)]`.
-/
@[reducible]
abbreviation adj_rel {α : Type u} (G : α) [simple_graph G] (v w : V G) := adj v w

local infix ` ~ ` := adj

/--
Basic constructor for a simple graph, using a symmetric irreflexive relation.
-/
structure from_adj_rel (V : Type u) :=
(rel : V → V → Prop)
(symm : symmetric rel . obviously)
(irrefl : irreflexive rel . obviously)

instance (V : Type u) (G : from_adj_rel V) : simple_graph G :=
{ V := V,
  adj := G.rel,
  symm := G.symm,
  loopless := G.irrefl }

variables {α : Type u} {G : α} [simple_graph G]

/-- `neighbor_set v` is the set of vertices adjacent to `v` in `G`. -/
def neighbor_set (v : V G) : set (V G) := set_of (adj v)

lemma ne_of_adj {a b : V G} (hab : a ~ b) : a ≠ b :=
by { rintro rfl, exact loopless G a hab }

variable (G)
/--
The edges of G consist of the unordered pairs of vertices related by `adj`.
-/
def edge_set : set (sym2 (V G)) := sym2.from_rel (symm G)

variable {G}

/--
The `incident_set` is the set of edges incident to a given vertex.
-/
def incident_set (v : V G) : set (sym2 (V G)) := {e ∈ edge_set G | v ∈ e}

lemma incident_set_subset (v : V G) : incident_set v ⊆ edge_set G :=
by tidy

@[simp]
lemma edge_iff_adj {v w : V G} : ⟦(v, w)⟧ ∈ edge_set G ↔ v ~ w :=
by refl

lemma adj_iff_exists_edge {v w : V G} :
  v ~ w ↔ v ≠ w ∧ ∃ (e ∈ edge_set G), v ∈ e ∧ w ∈ e :=
begin
  split, { intro, use [ne_of_adj a, ⟦(v,w)⟧], simpa },
  { rintro ⟨hne, e, he, hv⟩,
    rw sym2.elems_iff_eq hne at hv,
    subst e,
    rwa edge_iff_adj at he, }
end

lemma edge_other_ne {e : sym2 (V G)} (he : e ∈ edge_set G) {v : V G} (h : v ∈ e) : v ≠ h.other :=
by { rw [←sym2.mem_other_spec h] at he, exact ne_of_adj he }

instance edge_set_fintype [decidable_eq (V G)] [fintype (V G)] [decidable_rel (adj_rel G)] :
  fintype (edge_set G) :=
by { dunfold edge_set, exact subtype.fintype _ }

section edge_finset
variable (G)
variables [decidable_eq (V G)] [fintype (V G)] [decidable_rel (adj_rel G)]

/--
The `edge_set` of the graph as a `finset`.
-/
def edge_finset : finset (sym2 (V G)) :=
set.to_finset (edge_set G)

variable {G}

@[simp] lemma mem_edge_finset (e : sym2 (V G)) :
  e ∈ edge_finset G ↔ e ∈ edge_set G :=
by { dunfold edge_finset, simp }

@[simp] lemma edge_set_univ_card : (univ : finset (edge_set G)).card = (edge_finset G).card :=
fintype.card_of_subtype (edge_finset G) mem_edge_finset

end edge_finset

@[simp] lemma irrefl {v : V G} : ¬(v ~ v) := loopless G v

@[symm] lemma edge_symm (u v : V G) : u ~ v ↔ v ~ u := ⟨λ x, symm G x, λ x, symm G x⟩

@[simp] lemma mem_neighbor_set (v w : V G) : w ∈ neighbor_set v ↔ v ~ w :=
by tauto

@[simp] lemma mem_incident_set (v w : V G) : ⟦(v, w)⟧ ∈ incident_set v ↔ v ~ w :=
by { dsimp [incident_set], simp }

lemma neighbor_set_edge_prop {v w : V G} (h : w ∈ neighbor_set v) : ⟦(v, w)⟧ ∈ incident_set v :=
by { rw mem_neighbor_set at h, simpa }

lemma adj_incident_set_inter {v : V G} {e : sym2 (V G)} (he : e ∈ edge_set G) (h : v ∈ e) :
  incident_set v ∩ incident_set h.other = {e} :=
begin
  ext e',
  simp only [incident_set, set.mem_sep_eq, set.mem_inter_eq, set.mem_singleton_iff],
  split,
  { intro h', rw ←sym2.mem_other_spec h,
    exact (sym2.elems_iff_eq (edge_other_ne he h)).mp ⟨h'.1.2, h'.2.2⟩, },
  { rintro rfl, use [he, h, he], apply sym2.mem_other_mem, },
end

section incidence
variable [decidable_eq (V G)]

/--
Given an edge incident to a particular vertex, get the other vertex on the edge.
-/
def incident_set_other {v : V G} {e : sym2 (V G)} (h : e ∈ incident_set v) : V G := h.2.other'

lemma incident_other_prop {v : V G} {e : sym2 (V G)} (h : e ∈ incident_set v) : incident_set_other h ∈ neighbor_set v :=
by { cases h, rwa [←sym2.mem_other_spec' h_right, edge_iff_adj] at h_left }

@[simp]
lemma incident_other_neighbor_edge {v w : V G} (h : w ∈ neighbor_set v) :
  incident_set_other (neighbor_set_edge_prop h) = w :=
sym2.congr_right.mp (sym2.mem_other_spec' (neighbor_set_edge_prop h).right)

/--
There is an equivalence between the set of edges incident to a given
vertex and the set of vertices adjacent to the vertex.
-/
def incident_set_equiv_neighbor_set (v : V G) : incident_set v ≃ neighbor_set v :=
{ to_fun := λ e, ⟨incident_set_other e.2, incident_other_prop e.2⟩,
  inv_fun := λ w, ⟨⟦(v, w.1)⟧, neighbor_set_edge_prop w.2⟩,
  left_inv := by { intro x, dsimp [incident_set_other], simp },
  right_inv := by { intro x, rcases x with ⟨w, hw⟩, simp, } }

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

lemma degree_pos_iff_exists_adj : 0 < degree v ↔ ∃ w, v ~ w :=
by { dunfold degree, rw card_pos, dunfold finset.nonempty, simp }

instance incident_set_fintype [decidable_eq (V G)] : fintype (incident_set v) :=
fintype.of_equiv (neighbor_set v) (incident_set_equiv_neighbor_set v).symm

/--
This is the `finset` version of `incident_set`.
-/
def incident_finset [decidable_eq (V G)] : finset (sym2 (V G)) := (incident_set v).to_finset

@[simp]
lemma card_incident_set_eq_degree [decidable_eq (V G)] : fintype.card (incident_set v) = degree v :=
by { rw fintype.card_congr (incident_set_equiv_neighbor_set v), simp }

@[simp]
lemma mem_incident_finset [decidable_eq (V G)] (e : sym2 (V G)) :
  e ∈ incident_finset v ↔ e ∈ incident_set v :=
by { dunfold incident_finset, simp }

end finite_at

section locally_finite

variable (G)

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

instance neighbor_set_fintype [decidable_rel (adj_rel G)] (v : V G) : fintype (neighbor_set v) :=
@subtype.fintype _ _ (by { simp_rw mem_neighbor_set, apply_instance }) _

lemma neighbor_finset_eq_filter {v : V G} [decidable_rel (adj_rel G)] :
  neighbor_finset v = univ.filter (adj v) :=
by { ext, simp }

end finite

section subgraphs

variable (G)

/--
A subgraph of a graph is a subset of vertices and a subset of edges
such that each endpoint of an edge is contained in the vertex set.

Subgraphs implement the `simple_graph` class.  They also form a bounded lattice.
-/
structure subgraph :=
(V' : set (V G))
(E' : set (sym2 (V G)))
(edge_sub : E' ⊆ edge_set G)
(has_verts : ∀ (e ∈ E') (v ∈ e), v ∈ V')

@[simps]
instance subgraph.simple_graph (G' : subgraph G) : simple_graph G' :=
{ V := G'.V',
  adj := λ v w, ⟦(v.val, w.val)⟧ ∈ G'.E',
  symm := λ v w h, by rwa sym2.eq_swap,
  loopless := λ ⟨v, _⟩ h, loopless G v (sym2.from_rel_prop.mp (G'.edge_sub h)) }

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

/--
Map each vertex of a subgraph to the graph's vertex type.
-/
def subgraph_vert_emb (G' : subgraph G) : V G' ↪ V G :=
function.embedding.subtype _

/--
A characterization of the neighbor set of a subgraph as a subset of the neighbor set of the graph.
TODO fix API so it's not `v.val` for the vertex as a vertex in `V G`.
-/
def subgraph_neighbor_set_in_graph (G' : subgraph G) (v : V G') :
  neighbor_set v ≃ {w : neighbor_set v.val | ⟦(v.val, w.val)⟧ ∈ G'.E'} :=
{ to_fun := λ w, ⟨⟨w.1.1, begin
      cases w with w1 w2,
      rw mem_neighbor_set,
      rw [mem_neighbor_set, subgraph.simple_graph_adj] at w2,
      exact edge_iff_adj.mp (G'.edge_sub w2),
    end⟩, by { cases w with w1 w2, rw [mem_neighbor_set, subgraph.simple_graph_adj] at w2, exact w2 }⟩,
  inv_fun := λ w, ⟨⟨w.1, begin
      cases w with w1 w2,
      rw [set.mem_set_of_eq, sym2.eq_swap] at w2,
      exact subgraph.has_verts G' _ w2 w1.1 (sym2.mk_has_mem _ _),
    end⟩, begin
      rcases w with ⟨⟨w11, w12⟩, w2⟩,
      simp only [subtype.coe_mk],
      rw mem_neighbor_set v ⟨w11, G'.has_verts _ w2 _ (sym2.mk_has_mem_right _ _)⟩, simpa,
    end⟩,
  left_inv := λ w, by simp,
  right_inv := λ w, by simp }

instance subgraph_finite_at
{G' : subgraph G} [decidable_pred G'.E'] (v : V G') [fintype (neighbor_set v.val)] :
  fintype (neighbor_set v) :=
fintype.of_equiv _ (subgraph_neighbor_set_in_graph G' v).symm

/--
TODO: fix API so vertex in `V G` is not referred to as `v.val`
-/
lemma subgraph_degree_le
{G' : subgraph G} [decidable_pred G'.E'] (v : V G') [fintype (neighbor_set v.val)] :
  degree v ≤ degree v.val :=
begin
  dunfold degree,
  sorry,
end

end subgraphs

end simple_graph

namespace simple_graph

section complete_graphs

/--
The complete graph on a type `α` is the simple graph with all pairs of distinct vertices adjacent.
-/
def complete_graph (α : Type u) : from_adj_rel α :=
{ rel := ne }

instance from_rel_inhabited (α : Type u) : inhabited (from_adj_rel α) :=
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

section degree_sum

variables {α : Type u} (G : α) [simple_graph G] [fintype (V G)] [decidable_eq (V G)] [decidable_rel (adj_rel G)]

/--
A dart is a vertex along with an incident edge.
-/
def darts := Σ (v : V G), incident_set v

/--
Gives the dart's edge.
-/
def dart_to_edge : darts G → edge_set G := λ d, ⟨d.2.1, incident_set_subset d.1 d.2.2⟩
/--
Gives the dart's vertex.
-/
def dart_to_vert : darts G → V G := λ d, d.1
/--
Reverses the dart: the new vertex is the vertex across the edge.
-/
def dart_reverse : darts G → darts G := λ d, ⟨d.2.2.2.other', d.2.1, d.2.2.1, begin
  rcases d with ⟨v, e, he, hv⟩,
  rw ←(sym2.mem_other_spec' hv) at hv,
  apply sym2.mem_other_mem',
end⟩

@[simp]
lemma dart_to_edge_of_dart_reverse (d : darts G) : dart_to_edge G (dart_reverse G d) = dart_to_edge G d := rfl

lemma dart_reverse_invol : function.involutive (dart_reverse G) :=
begin
  rintro ⟨v, e, hd⟩,
  dsimp [dart_reverse],
  congr, delta dart_reverse._proof_2, delta dart_reverse._proof_1, dsimp only,
  apply sym2.other_invol',
  ext e, delta dart_reverse._proof_2, delta dart_reverse._proof_1, dsimp only,
  rw sym2.other_invol',
  apply proof_irrel_heq,
end

lemma dart_reverse_no_fixedpoint (d : darts G) : d ≠ dart_reverse G d :=
begin
  intro h,
  rcases d with ⟨v, e, he, hv⟩,
  rw ←sym2.mem_other_spec' hv at he,
  dsimp [dart_reverse] at h,
  rw sigma.mk.inj_iff at h,
  rw [←h.1, edge_iff_adj] at he,
  exact loopless G v he,
end

lemma dart_edge_preimage (d₁ d₂ : darts G) :
  dart_to_edge G d₁ = dart_to_edge G d₂ ↔ d₁ = d₂ ∨ d₁ = dart_reverse G d₂ :=
begin
  split,
  { intro h,
    rcases d₁ with ⟨v₁, e₁, he₁, hv₁⟩,
    rcases d₂ with ⟨v₂, e₂, he₂, hv₂⟩,
    simp only [dart_to_edge, subtype.mk_eq_mk] at h,
    subst e₂,
    by_cases h : v₁ = v₂, { left, subst v₂, },
    have hh : hv₂.other' = v₁,
    { have he' := eq.trans (sym2.mem_other_spec' hv₂) ((sym2.elems_iff_eq h).mp ⟨hv₁, hv₂⟩),
      rw sym2.eq_iff at he',
      cases he', exfalso, cc, cc, },
    right, simp only [dart_reverse, sigma.mk.inj_iff],
    split,
    exact hh.symm,
    delta dart_reverse._proof_2, dsimp,
    congr,
    { ext e', delta dart_reverse._proof_1, dsimp,
      rw hh, },
    exact hh.symm,
    apply proof_irrel_heq, },
  { intro h, cases h; subst d₁, simp, }
end

instance : fintype (darts G) :=
by { dunfold darts, apply_instance }

lemma dart_to_edge_prop (e : edge_set G) (d : darts G) (h : dart_to_edge G d = e) : d.1 ∈ e.1 :=
by tidy

lemma dart_to_edge_surj : function.surjective (dart_to_edge G) :=
begin
  rintro ⟨e, he⟩,
  induction e,
  cases e with v w,
  use [v, ⟦(v, w)⟧],
  exact (mem_incident_set v w).mpr (edge_iff_adj.mp he),
  dsimp [dart_to_edge], refl,
  refl,
end

lemma dart_to_edge_surj' : image (dart_to_edge G) univ = univ :=
begin
  ext e,
  simp only [mem_image, mem_univ, iff_true, exists_prop_of_true],
  exact dart_to_edge_surj G e,
end

lemma dart_to_vert_preimage_card_eq_degree (v : V G):
  (univ.filter (λ (x : darts G), dart_to_vert G x = v)).card = degree v :=
begin
  dunfold degree, rw neighbor_finset_eq_filter,
  let f := λ (x : darts G), dart_to_vert G (dart_reverse G x),
  let s := univ.filter (λ (x : darts G), dart_to_vert G x = v),
  have H : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y, {
    rintros ⟨v₁, e₁, he₁, hv₁⟩ hd₁ ⟨v₂, e₂, he₂, hv₂⟩ hd₂ heq,
    dsimp [f, dart_reverse, dart_to_vert] at heq,
    have aa₁ := sym2.mem_other_spec' hv₁,
    have aa₂ := sym2.mem_other_spec' hv₂,
    simp only [dart_to_vert, true_and, mem_filter, mem_univ] at hd₁ hd₂,
    subst v₁, subst v₂,
    congr, rw ←heq at aa₂,
    exact eq.trans aa₁.symm aa₂,
  },
  rw ←card_image_of_inj_on H,
  congr,
  ext w,
  simp,
  split,
  { rintros ⟨⟨v', e', he', hv'⟩, hd, hw⟩,
    dsimp [dart_to_vert] at hd, subst v',
    dsimp [f, dart_reverse, dart_to_vert] at hw,
    have aa := sym2.mem_other_spec' hv',
    rw hw at aa,
    rwa [←aa, edge_iff_adj] at he', },
  { intro a,
    use [v, ⟦(v, w)⟧], simpa,
    dsimp [dart_to_vert, f, dart_reverse],
    use rfl,
    rw ←@sym2.congr_right _ v,
    simp, }
end

lemma dart_to_edge_two_to_one (e : edge_set G) : (univ.filter (λ x, dart_to_edge G x = e)).card = 2 :=
begin
  cases e with e he,
  rcases dart_to_edge_surj G ⟨e, he⟩ with ⟨d, hd⟩,
  have key : univ.filter (λ (x : darts G), dart_to_edge G x = ⟨e, he⟩) = {d, dart_reverse G d},
  { ext d',
    simp only [true_and, mem_filter, mem_insert, mem_univ, mem_singleton],
    rw [←hd, dart_edge_preimage], },
  rw key,
  have key' : d ∉ {dart_reverse G d},
  { rw not_mem_singleton, apply dart_reverse_no_fixedpoint, },
  rw card_insert_of_not_mem key',
  simp,
end

lemma dart_card_twice_edges : fintype.card (darts G) = 2 * (edge_finset G).card :=
begin
  change univ.card = _,
  rw card_eq_sum_card_image (dart_to_edge G),
  rw dart_to_edge_surj',
  simp only [dart_to_edge_two_to_one, edge_set_univ_card, nat.cast_id, nsmul_eq_mul, sum_const],
  rw mul_comm,
end

lemma dart_card_sum_degrees : fintype.card (darts G) = ∑ v : V G, degree v :=
begin
  change univ.card = _,
  rw card_eq_sum_card_image (dart_to_vert G),
  have key' := @sum_filter_of_ne (V G) ℕ univ (λ (v : V G), degree v) _ (λ x, x ∈ univ.image (dart_to_vert G)) _ begin
    intros v _ hd,
    rcases (degree_pos_iff_exists_adj v).mp (nat.pos_of_ne_zero hd) with ⟨w, hw⟩,
    simp only [mem_image, mem_univ, exists_prop_of_true],
    use [v, ⟦(v, w)⟧], simp [hw],
    simp [dart_to_vert],
  end,
  rw ←key',
  have key'' : univ.filter (λ (x : V G), x ∈ univ.image (dart_to_vert G)) = univ.image (dart_to_vert G),
  { ext v, simp, },
  rw key'',
  congr,
  ext v,
  rw dart_to_vert_preimage_card_eq_degree,
end

lemma degree_sum : ∑ v : V G, degree v = 2 * (edge_finset G).card :=
by { rw [←dart_card_sum_degrees, ←dart_card_twice_edges] }

end degree_sum

end simple_graph
