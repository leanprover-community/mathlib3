/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson, Jalex Stark, Kyle Miller.
-/
import data.fintype.basic
import data.sym2
import data.equiv.basic
import data.zmod.basic
import order.bounded_lattice
import algebra.big_operators
import tactic
/-!
# Simple graphs

This module defines simple graphs as irreflexive symmetric relations.
Since graphs are terms, the basic interface is that a term `G` is a
simple graph if there is an instance `[simple_graph G]`.

To construct a simple graph from a specific relation, one uses
`simple_graph_on`.

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

/--
Basic constructor for a simple graph, using a symmetric irreflexive relation.
-/
@[ext]
structure simple_graph_on (V : Type u) :=
(adj : V → V → Prop)
(symm : symmetric adj . obviously)
(loopless : irreflexive adj . obviously)

instance simple_graph_on.simple_graph (V : Type u) (G : simple_graph_on V) : simple_graph G :=
{ V := V,
  adj := G.adj,
  symm := G.symm,
  loopless := G.loopless }

/--
TODO remove this.  It's only here to demonstrate an interesting but probably unreasonable instance.
-/
instance from_rel (V : Type u) (r : V → V → Prop) [hs : fact (symmetric r)] [hi : fact (irreflexive r)] :
  simple_graph r :=
{ V := V,
  adj := r,
  symm := hs,
  loopless := hi }

/--
Construct the simple graph induced by the given relation.  It
symmetrizes the relation and makes it irreflexive.
-/
def simple_graph_from_rel {V : Type u} (r : V → V → Prop) : simple_graph_on V :=
{ adj := λ a b, (a ≠ b) ∧ (r a b ∨ r b a),
  symm := by finish,
  loopless := by finish }

namespace simple_graph

/--
This is `simple_graph.adj` but with an explicit `G`.  It is used for situations such as `[decidable_rel (adj_rel G)]`.
-/
@[reducible]
abbreviation adj_rel {α : Type u} (G : α) [simple_graph G] (v w : V G) := adj v w

infix ` ~g ` : 40 := adj

variables {α : Type u} {G : α} [simple_graph G]

/-- `neighbor_set v` is the set of vertices adjacent to `v` in `G`. -/
def neighbor_set (v : V G) : set (V G) := set_of (adj v)

lemma ne_of_adj {a b : V G} (hab : a ~g b) : a ≠ b :=
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
lemma edge_iff_adj {v w : V G} : ⟦(v, w)⟧ ∈ edge_set G ↔ v ~g w :=
by refl

lemma adj_iff_exists_edge {v w : V G} :
  v ~g w ↔ v ≠ w ∧ ∃ (e ∈ edge_set G), v ∈ e ∧ w ∈ e :=
begin
  split, { intro, use [ne_of_adj a, ⟦(v,w)⟧], simpa },
  { rintro ⟨hne, e, he, hv⟩,
    rw sym2.elems_iff_eq hne at hv,
    subst e,
    rwa edge_iff_adj at he, }
end

lemma edge_other_ne {e : sym2 (V G)} (he : e ∈ edge_set G) {v : V G} (h : v ∈ e) : h.other ≠ v :=
sym2.mem_from_rel_irrefl_other_ne (loopless G) he h

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

@[simp] lemma irrefl {v : V G} : ¬(v ~g v) := loopless G v

@[symm] lemma adj_symm (u v : V G) : u ~g v ↔ v ~g u := ⟨λ x, symm G x, λ x, symm G x⟩

@[simp] lemma mem_neighbor_set (v w : V G) : w ∈ neighbor_set v ↔ v ~g w :=
by tauto

@[simp] lemma mem_incident_set (v w : V G) : ⟦(v, w)⟧ ∈ incident_set v ↔ v ~g w :=
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
    exact (sym2.elems_iff_eq (edge_other_ne he h).symm).mp ⟨h'.1.2, h'.2.2⟩, },
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
  w ∈ neighbor_finset v ↔ v ~g w :=
by simp [neighbor_finset]

/--
`degree v` is the number of vertices adjacent to `v`.
-/
def degree : ℕ := (neighbor_finset v).card

@[simp]
lemma card_neighbor_set_eq_degree : fintype.card (neighbor_set v) = degree v :=
by simp [degree, neighbor_finset]

lemma degree_pos_iff_exists_adj : 0 < degree v ↔ ∃ w, v ~g w :=
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

end simple_graph

namespace simple_graph

section maps

variables {α α' : Type*} (G : α) [simple_graph G] (G' : α') [simple_graph G']

/--
A graph homomorphism is a map on vertex sets that respects the adjacency relations.
-/
@[ext]
structure homomorphism :=
(to_fun : V G → V G')
(map_adj' : ∀ {v w : V G}, v ~g w → to_fun v ~g to_fun w)

infix ` →g ` : 50 := homomorphism

namespace homomorphism

instance coe_to_fun : has_coe_to_fun (G →g G') :=
⟨_, homomorphism.to_fun⟩

variables {G} {G'} {f : G →g G'}

def map_adj {v w : V G} : v ~g w → f v ~g f w :=
by apply f.map_adj'

end homomorphism

/--
A graph embedding is an embedding on vertex sets that respects the adjacency relations.
-/
structure embedding extends V G ↪ V G' :=
(map_adj' : ∀ {v w : V G}, v ~g w → to_fun v ~g to_fun w)

infix ` ↪g ` : 50 := embedding

namespace embedding

instance coe_to_fun : has_coe_to_fun (G ↪g G') :=
⟨_, λ f, f.to_fun⟩

variables {G} {G'} {f : G ↪g G'}

def map_adj {v w : V G} : v ~g w → f v ~g f w :=
by apply f.map_adj'

end embedding

/--
An injective homomorphism gives an embedding of graphs.
-/
def inj_homomorphism_to_embedding (f : G →g G') (h : function.injective f) : G ↪g G' :=
{ to_fun := f.to_fun,
  inj' := h,
  map_adj' := f.map_adj' }

/--
An embedding of graphs gives rise to a homomorphism of graphs.
-/
def embedding_to_homomorphism (f : G ↪g G') : G →g G' :=
{ to_fun := f.to_fun,
  map_adj' := f.map_adj' }

/--
A graph isomorphism is an equivalence on vertex sets that preserves the adjacency relations exactly.
-/
@[reducible]
def isomorphism := rel_iso (adj_rel G) (adj_rel G')

infix ` ≃g ` : 50 := isomorphism

namespace isomorphism

variables {G} {G'} {f : G ≃g G'}

def map_adj_iff {v w : V G} : v ~g w ↔ f v ~g f w :=
by apply f.map_rel_iff'

end isomorphism

def isomorphism_to_embedding (f : G ≃g G') : G ↪g G' :=
{ to_fun := f.to_fun,
  inj' := f.injective,
  map_adj' := λ v w h, (rel_iso.map_rel_iff f).mp h }

end maps

section subgraphs

/-!
## Subgraphs of a graph
-/

variables {α : Type u} (G : α) [simple_graph G]

/--
A subgraph of a graph is a subset of vertices and a subset of edges
such that each endpoint of an edge is contained in the vertex set.

Subgraphs implement the `simple_graph` class.  They also form a bounded lattice.

NOTE: another definition could have been.
```
structure subgraph :=
(V' : set (V G))
(adj' : V' → V' → Prop)
(symm' : symmetric adj')
(sub_adj' : ∀ {v w : V G} (hv : v ∈ V') (hw : w ∈ V'), adj' ⟨v, hv⟩ ⟨w, hw⟩ → (v ~g w))
```
It's not clear which is better!
-/
@[ext]
structure subgraph :=
(V' : set (V G))
(E' : set (sym2 (V G)))
(edge_sub : E' ⊆ edge_set G)
(has_verts : ∀ {e : sym2 (V G)} {v : V G}, e ∈ E' → v ∈ e → v ∈ V')

namespace subgraph

variable {G}

@[simps]
instance subgraph.simple_graph (G' : subgraph G) : simple_graph G' :=
{ V := G'.V',
  adj := λ v w, ⟦(↑v, ↑w)⟧ ∈ G'.E',
  symm := λ v w h, by rwa sym2.eq_swap,
  loopless := λ ⟨v, _⟩ h, loopless G v (sym2.from_rel_prop.mp (G'.edge_sub h)) }

/--
Given a subgraph, replace the vertex set with an equal set.
The resulting subgraph is equal (see `copy_eq`).
-/
def copy (G' : subgraph G)
(V'' : set (V G)) (hV : V'' = G'.V')
(E'' : set (sym2 (V G))) (hE : E'' = G'.E') :
  subgraph G :=
{ V' := V'',
  E' := E'',
  edge_sub := hE.symm ▸ G'.edge_sub,
  has_verts := hE.symm ▸ hV.symm ▸ G'.has_verts }

lemma copy_eq (G' : subgraph G)
(V'' : set (V G)) (hV : V'' = G'.V')
(E'' : set (sym2 (V G))) (hE : E'' = G'.E') :
  G'.copy V'' hV E'' hE = G' :=
subgraph.ext _ _ hV hE

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
  has_verts := λ e v h hv, begin
    cases h,
    apply or.inl (x.has_verts h hv),
    apply or.inr (y.has_verts h hv),
  end }

/--
The intersection of two subgraphs.
-/
def inter (x y : subgraph G) : subgraph G :=
{ V' := x.V' ∩ y.V',
  E' := x.E' ∩ y.E',
  edge_sub := λ e h, x.edge_sub h.1,
  has_verts := λ e v h hv, ⟨x.has_verts h.1 hv, y.has_verts h.2 hv⟩ }

instance : has_union (subgraph G) := ⟨union⟩
instance : has_inter (subgraph G) := ⟨inter⟩

/--
The `top` subgraph is `G` as a subgraph of itself.
-/
def top : subgraph G :=
{ V' := set.univ,
  E' := edge_set G,
  edge_sub := by refl,
  has_verts := λ e v he hv, by apply set.mem_univ }

/--
The `bot` subgraph is the subgraph with no vertices or edges.
-/
def bot : subgraph G :=
{ V' := ∅,
  E' := ∅,
  edge_sub := set.empty_subset _,
  has_verts := λ e v he hv, by { exfalso, apply set.not_mem_empty e he } }

instance subgraph_inhabited : inhabited (subgraph G) := ⟨bot⟩

instance : bounded_lattice (subgraph G) :=
{ le := is_subgraph,
  sup := union,
  inf := inter,
  top := top,
  bot := bot,
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
Given two subgraphs, one a subgraph of the other, there is an induced embedding of the subgraphs as graphs.
-/
def map {x y : subgraph G} (h : x ≤ y) : x ↪g y :=
{ to_fun := λ v, ⟨↑v, and.left h v.property⟩,
  inj' := λ v w h, subtype.ext (subtype.mk_eq_mk.mp h),
  map_adj' := λ v w hvw, begin
    rw subgraph.simple_graph_adj, apply and.right h,
    cases v, cases w, rwa subgraph.simple_graph_adj at hvw,
  end }

/--
A subgraph of `G` embeds in `G`.
-/
def map_top (x : subgraph G) : x ↪g G :=
{ to_fun := λ v, ↑v,
  inj' := λ v w h, subtype.ext h,
  map_adj' := λ v w hvw, begin
    cases v, cases w, rw subgraph.simple_graph_adj at hvw,
    apply edge_iff_adj.mp (x.edge_sub hvw),
  end }

@[simp]
lemma map_top_to_fun {x : subgraph G} (v : x.V') : x.map_top v = v.val := rfl

/--
Give the vertex as an element of the subgraph's vertex type.
-/
@[reducible]
def in_subgraph (G' : subgraph G) {v : V G} (h : v ∈ G'.V') : V G' :=
⟨v, h⟩

/--
The induced subgraph of a graph is the graph with a specified vertex
set along with all the edges whose endpoints lie in the set.
-/
def induced (V' : set (V G)) : subgraph G :=
{ V' := V',
  E' := {e ∈ edge_set G | ∀ v ∈ e, v ∈ V'},
  edge_sub := λ _ ⟨h, _⟩, h,
  has_verts := λ e v ⟨he, h⟩ hv, h v hv, }


/--
A characterization of the neighbor set of a subgraph as a subset of the neighbor set of the graph.
-/
def subgraph_neighbor_set_in_graph (G' : subgraph G) (v : V G') :
  neighbor_set v ≃ {w : neighbor_set (G'.map_top v) | ⟦(G'.map_top v, ↑w)⟧ ∈ G'.E'} :=
{ to_fun := λ w, ⟨⟨w.1.1, begin
      cases w with w1 w2,
      rw mem_neighbor_set,
      rw [mem_neighbor_set, subgraph.simple_graph_adj] at w2,
      exact edge_iff_adj.mp (G'.edge_sub w2),
    end⟩, by { cases w with w1 w2, rw [mem_neighbor_set, subgraph.simple_graph_adj] at w2, exact w2 }⟩,
  inv_fun := λ w, ⟨⟨w.1, begin
      cases w with w1 w2,
      rw [set.mem_set_of_eq, sym2.eq_swap] at w2,
      exact subgraph.has_verts G' w2 (sym2.mk_has_mem _ _),
    end⟩, begin
      rcases w with ⟨⟨w11, w12⟩, w2⟩,
      simp only [subtype.coe_mk],
      rw mem_neighbor_set v ⟨w11, G'.has_verts w2 (sym2.mk_has_mem_right _ _)⟩, simpa,
    end⟩,
  left_inv := λ w, by simp,
  right_inv := λ w, by simp }

def subgraph_neighbor_set_in_supergraph {G' G'' : subgraph G} (h : G' ≤ G'') (v : V G') :
  neighbor_set v ≃ {w : neighbor_set (map h v) | ⟦(↑v, ↑w)⟧ ∈ G'.E'} :=
{ to_fun := λ w, ⟨⟨map h w.1, begin
      cases w with w1 w2,
      rw mem_neighbor_set,
      rw [mem_neighbor_set, subgraph.simple_graph_adj] at w2,
      apply edge_iff_adj.mp,
      simp only [subgraph.simple_graph_adj, edge_iff_adj],
      apply h.2 w2,
    end⟩, by { cases w with w1 w2, rw [mem_neighbor_set, subgraph.simple_graph_adj] at w2, exact w2 }⟩,
  inv_fun := λ w, ⟨⟨w.1, begin
      cases w with w1 w2,
      rw [set.mem_set_of_eq, sym2.eq_swap] at w2,
      exact subgraph.has_verts G' w2 (sym2.mk_has_mem _ _),
    end⟩, begin
      rcases w with ⟨⟨w11, w12⟩, w2⟩,
      simp only [subtype.coe_mk],
      simp at w2, simp,
      have hw11 := G'.has_verts w2 (sym2.mk_has_mem_right _ _),
      convert_to (⟨↑w11, hw11⟩ : V G') ∈ neighbor_set v,
      rw mem_neighbor_set v ⟨w11, G'.has_verts w2 (sym2.mk_has_mem_right _ _)⟩, simpa,
    end⟩,
  left_inv := λ w, by tidy,
  right_inv := λ w, by tidy }


instance finite_at
{G' : subgraph G} [decidable_pred G'.E'] (v : V G) (h : v ∈ G'.V') [fintype (neighbor_set v)] :
  fintype (neighbor_set (G'.in_subgraph h)) := sorry
--fintype.of_equiv _ (subgraph_neighbor_set_in_graph G' (G'.in_subgraph h)).symm

instance finite_at_subgraph {G' G'' : subgraph G} [decidable_pred G'.E'] [decidable_pred G''.E']
(h : G' ≤ G'') (v : V G) (hv : v ∈ G'.V') [hf : fintype (neighbor_set (map h (G'.in_subgraph hv)))] :
  fintype (neighbor_set (G'.in_subgraph hv)) := sorry
--fintype.of_equiv _ (subgraph_neighbor_set_in_supergraph h v).symm


/--
This instance helps `subgraph.finite_at` get applied given a `fintype (V G)` instance.
-/
instance subgraph_of_finite
{G' : subgraph G} [decidable_rel (adj_rel G)] [fintype (V G)] (v : V G') :
  fintype (neighbor_set (G'.map_top v)) := sorry
--by { cases v, simp, apply_instance, }

lemma degree_le_top
{G' : subgraph G} [decidable_pred G'.E'] (v : V G) (h : v ∈ G'.V') [fintype (neighbor_set v)] :
  degree (G'.in_subgraph h) ≤ degree v :=
begin
  sorry,
end

lemma degree_le
{G' G'' : subgraph G} [decidable_pred G'.E'] [decidable_pred G''.E'] (h : G' ≤ G'')
(v : V G) (hv : v ∈ G'.V') [fintype (neighbor_set (map h (G'.in_subgraph hv)))] :
  degree (G'.in_subgraph hv) ≤ degree (map h (G'.in_subgraph hv)) :=
begin
  sorry,
end

end subgraph

end subgraphs

section simple_graph_on

/-!
## Simple graphs on a given vertex type
-/

variables {α : Type u}

/--
A spanning subgraph is a graph containing all the vertices of the
other and a subset of its edges. This is the natural notion for graphs from `simple_graph_on`.
-/
def is_spanning_subgraph (x y : simple_graph_on α) : Prop := ∀ (v w : α), x.adj v w → y.adj v w

def union (x y : simple_graph_on α) : simple_graph_on α :=
{ adj := λ (v w : α), x.adj v w ∨ y.adj v w,
  symm := λ v w h, by { cases h, left, exact x.symm h, right, exact y.symm h },
  loopless := λ v h, by { cases h, apply x.loopless _ h, apply y.loopless _ h } }

def inter (x y : simple_graph_on α) : simple_graph_on α :=
{ adj := λ (v w : α), x.adj v w ∧ y.adj v w,
  symm := λ v w h, ⟨x.symm h.1, y.symm h.2⟩,
  loopless := λ v h, x.loopless _ h.1 }

/--
The graph with no edges on a given vertex type.
-/
def empty_graph (V : Type u) : simple_graph_on V := { adj := λ i j, false }

/--
The complete graph on a type `α` is the simple graph with all pairs of distinct vertices adjacent.
-/
def complete_graph (α : Type u) : simple_graph_on α :=
{ adj := ne }

instance : bounded_lattice (simple_graph_on α) :=
{ le := is_spanning_subgraph,
  sup := union,
  inf := inter,
  bot := empty_graph α,
  top := complete_graph α,
  le_refl := by obviously,
  le_trans := by obviously,
  le_antisymm := by obviously,
  le_inf := by obviously,
  sup_le := by obviously,
  inf_le_left := by obviously,
  inf_le_right := by obviously,
  le_sup_left := λ G H, λ v w h, by { left, apply h, },
  le_sup_right := λ G H, λ v w h, by { right, apply h, },
  bot_le := by obviously,
  le_top := by { intro G, have h := G.loopless, obviously, }, }

/--
Erase an edge of a graph to get a smaller graph.
-/
def erase_edge (G : simple_graph_on α) {e : sym2 α} (h : e ∈ edge_set G) : simple_graph_on α :=
{ adj := λ v w, G.adj v w ∧ ¬ (v ∈ e ∧ w ∈ e),
  symm := λ v w h, ⟨G.symm h.1, by { rw and_comm, exact h.2, }⟩,
  loopless := λ v h, by { have h := G.loopless v, tidy } }

/--
A graph with a given vertex type and a single edge.
-/
def single_edge_graph {α : Type u} {v w : α} (hne : v ≠ w) : simple_graph_on α :=
{ adj := λ i j, (i = v ∧ j = w) ∨ (i = w ∧ j = v) }

/-- Add an edge between two distinct vertices. -/
def insert_edge (G : simple_graph_on α) {v w : α} (hne : v ≠ w) := G ⊔ single_edge_graph hne

end simple_graph_on

section graph_operations

variables {α : Type u}

def two_pt_quo {β : Type*} (v w : β) := @quot β (λ i j, i = j ∨ (i = v ∧ j = w) ∨ (i = w ∧ j = v))

def contract_edge (G : α) [simple_graph G] {v w : V G} (h : v ~g w) : simple_graph_on (two_pt_quo v w) :=
{ adj := λ i j, sorry
}

-- TODO

-- open sum

-- def subdivide_adj (G : α) [simple_graph G] {e : sym2 (V G)} (h : e ∈ edge_set G) : (V G ⊕ punit) → (V G ⊕ punit) → Prop
-- | (inl a) (inl b) := (erase_edge G h).adj a b
-- | (inl a) _ := a ∈ e
-- | _ (inl a) := a ∈ e
-- | _ _ := false

-- /-- Subdivides an edge by turning it into two edges, with a new vertex in between -/
-- def subdivide (G : simple_graph V) (e : G.E) : simple_graph (V ⊕ punit) :=
-- { adj := G.subdivide_adj e,
--   sym := λ v w h, by { cases v; cases w; unfold simple_graph.subdivide_adj at *,
--     {apply (G.erase_edge e).sym h}, repeat { assumption }, }, }

end graph_operations

end simple_graph

namespace simple_graph

section complete_graphs

instance from_rel_inhabited (α : Type u) : inhabited (simple_graph_on α) :=
⟨complete_graph α⟩

variables (α : Type u) [decidable_eq α]

instance complete_graph_adj_decidable :
  decidable_rel (complete_graph α).adj :=
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

section examples

@[simp]
lemma simple_graph_from_rel_adj {α : Type u} (r : α → α → Prop) (v w : V (simple_graph_from_rel r)) :
  v ~g w ↔ v ≠ w ∧ (r v w ∨ r w v) :=
by refl

/--
A path graph on n+1 vertices, which has n edges.
-/
def path_graph (n : ℕ) : simple_graph_on (fin (n + 1)) :=
simple_graph_from_rel (λ i j, (j = i - 1 ∧ i ≠ 0))

/--
A graph on `n` vertices with `n` edges in a cycle
-/
def cycle_graph (n : ℕ) (three_le : 3 ≤ n) : simple_graph_on (zmod n) :=
simple_graph_from_rel (λ i j, i = j + 1)

lemma cycle_graph_prop (n : ℕ) (three_le : 3 ≤ n) (i j : V (cycle_graph n three_le)) :
  i ~g j → i = j + 1 ∨ i + 1 = j :=
begin
  intro h,
  rw simple_graph_from_rel_adj at h,
  cases h.right,
  left, assumption, right, exact h_1.symm,
end

def complete_partite_graph {ι : Type u} (f : ι → Type v) : simple_graph_on (Σ i : ι, f i) :=
{ adj := λ v w, v.1 ≠ w.1 }

def complete_equiv_complete_partite (α : Type u) :
  complete_graph α ≃g complete_partite_graph (λ v : α, punit) :=
{ to_fun := λ v, ⟨v, punit.star⟩,
  inv_fun := λ v, v.1,
  left_inv := by tidy,
  right_inv := by tidy,
  map_rel_iff' := by tidy }

end examples

section coloring

variables {α : Type u} (G : α) [simple_graph G]

/--
A graph G is β-colorable if there is an assignment of elements of β to
vertices of G (allowing repetition) such that adjacent vertices have
distinct colors.
-/
@[ext]
structure coloring (β : Type v) :=
(color : V G → β)
(valid : ∀ (v w : V G), v ~g w → color v ≠ color w)

/--
A graph G is β-colorable if there is a β-coloring.
-/
def colorable (β : Type v) : Prop := nonempty (coloring G β)

lemma extend_coloring (β β' : Type*) (f : β ↪ β') : coloring G β ↪ coloring G β' :=
{ to_fun := λ F, { color := λ v, f (F.color v),
                   valid := begin
                     intros v w h hc, apply F.valid v w h, apply function.embedding.injective f, assumption,
                   end},
  inj' := begin intros F F' h, ext, apply function.embedding.injective f, simp at h, exact congr_fun h x, end
}

end coloring

section connectivity

variables {α : Type u} (G : α) [simple_graph G]

/-- Determines if two vertices are connected by a path -/
def exists_path : V G → V G → Prop := eqv_gen (adj_rel G)

/-- Quotient of the vertex type by connectivity -/
def connected_components := quotient (eqv_gen.setoid (exists_path G))

/-- Determines if a graph is connected -/
def is_connected : Prop := ∀ v w, exists_path G v w

/-- The graph does not contain a cycle -/
def is_acyclic : Prop := ∀ (n : ℕ) (h : 3 ≤ n), (cycle_graph n h ↪g G) → false

/-- A tree is an acyclic connected graph -/
def is_tree : Prop := is_connected G ∧ is_acyclic G

end connectivity

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
