/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov
-/
import data.sym2
import data.fintype.basic
import data.zmod.basic
import tactic

/-!
# Simple graphs

This module defines simple graphs as irreflexive symmetric relations.
Since graphs are terms rather than types, the usual mathlib techniques
for dealing with objects and subobjects in a uniform way is
implemented a bit differently.

A simple graph is a term of type `simple_graph`.  This bundles
together a vertex type `V` and a `simple_graph_on V` structure.  Types
whose terms have an interpretation as a simple graph should define an
instance of `has_coe_to_simple_graph`.  This modules provides the `↟`
coercion arrow to coerce terms to `simple_graph`.

Proofs that apply to graphs in general should use `G : simple_graph`
directly.  One should use the accessor functions in the
`accessor_functions` section.  For types with
`has_coe_to_simple_graph` instances, then one may give `simp` lemmas
to put these accessors into specialized forms.

There is a basic API for locally finite graphs and for graphs with
finitely many vertices.  We take the convention that a graph is finite at
a given vertex `v` if `[fintype (neighbor_set v)]`, and it has finitely many
vertices if `[fintype (V G)]`.

## Main definitions

* `simple_graph_on V` is the type for simple graphs on a given vertex type.
  It forms a bounded lattice.

* `simple_graph` is a bundled `simple_graph_on`.

* `subgraph G` is a type of subgraphs of a given graph `G`.  It forms a bounded lattice

* `neighbor_set` is the `set` of vertices adjacent to a given vertex

* `neighbor_finset` is the `finset` of vertices adjacent to a given vertex,
   if `neighbor_set` is finite

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
Basic constructor for a simple graph, using a symmetric irreflexive relation.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent edges;
see `simple_graph.edge_set` for the corresponding edge set.

When proving statements about simple graphs in general, one should use the
`simple_graph` type.
-/
@[ext]
structure simple_graph_on (V : Type u) :=
(adj : V → V → Prop)
(symm' : symmetric adj . obviously)
(loopless' : irreflexive adj . obviously)

/--
A generic simple graph, bundling a vertex type and a `simple_graph_on` structure.
Theorems about generic graphs should be in terms of this.
-/
structure simple_graph :=
(V : Type u)
(graph : simple_graph_on V)

/--
Type with graph interpretations (for example subgraphs) may implement
this to get access to the `↟` coercion arrow.  (Note: this is getting
around a problem with `has_coe` class resolution where universe
variables do not seem to be inferrable.)
-/
class has_coe_to_simple_graph (α : Type u) :=
(coe : α → simple_graph.{v})

/-
If only `has_coe` could infer the universe variables, this wouldn't be needed.
-/
notation `↟`:max x:max := has_coe_to_simple_graph.coe x

instance (V : Type u) : has_coe_to_simple_graph (simple_graph_on V) :=
⟨λ G, ⟨V, G⟩⟩

section accessor_functions
/-!
## Accessor functions

The way one talks about an arbitrary simple graph is by
```
variables {α : Type*} [simple_graphs α] (G : α)
```
That is, `α` is declared to be some "universe" of simple graph objects,
and then `G` is a simple graph from it.

To make the API simple to use, rather than needing to explicitly use
`to_simple_graph`, we define some accessor functions that obtain the
fields of the corresponding `simple_graph_on` object.  All definitions
and theorems should refer to these accessor functions.
-/


namespace simple_graph

/--
The adjacency relation for the simple graph.
-/
abbreviation adj (G : simple_graph) : V G → V G → Prop := G.graph.adj

/--
To get the infix adjacency relation `v ~g w` to work, it is useful to
have this abbreviation for `adj` with implicit `G`.
-/
abbreviation adj' {G : simple_graph} : V G → V G → Prop := G.adj

abbreviation symm (G : simple_graph) : symmetric (@adj' G) := G.graph.symm'

abbreviation loopless (G : simple_graph) : irreflexive (@adj' G) := G.graph.loopless'

infix ` ~g ` : 40 := adj'

@[simp] lemma adj_as_adj₁ {G : simple_graph} (v w : V G) : G.graph.adj v w ↔ v ~g w := by refl

@[simp] lemma adj_as_adj₂ {G : simple_graph} (v w : V G) : G.adj v w ↔ v ~g w := by refl

@[simp] lemma simple_graph_on.coe_v_eq {α : Type*} {G : simple_graph_on α} : V ↟G = α := rfl

@[simp] lemma simple_graph_on.adj {α : Type*} {G : simple_graph_on α} : (↟G).adj = G.adj := rfl

end simple_graph
end accessor_functions

/--
Construct the simple graph induced by the given relation.  It
symmetrizes the relation and makes it irreflexive.
-/
def simple_graph_from_rel {V : Type u} (r : V → V → Prop) : simple_graph_on V :=
{ adj := λ a b, (a ≠ b) ∧ (r a b ∨ r b a),
  symm' := by finish,
  loopless' := by finish }

namespace simple_graph

variables {G : simple_graph}

/-- `neighbor_set v` is the set of vertices adjacent to `v` in `G`. -/
def neighbor_set (v : V G) : set (V G) := set_of (adj' v)

lemma ne_of_adj {a b : V G} (hab : a ~g b) : a ≠ b :=
by { rintro rfl, exact G.loopless a hab }

variable (G)
/--
The edges of G consist of the unordered pairs of vertices related by `adj`.
-/
def edge_set : set (sym2 (V G)) := sym2.from_rel (symm G)

variable {G}

/--
The `incident_set` is the set of edges incident to a given vertex.
-/
def incident_set (v : V G) : set (sym2 (V G)) := {e ∈ G.edge_set | v ∈ e}

lemma incident_set_subset (v : V G) : incident_set v ⊆ G.edge_set :=
by tidy

@[simp]
lemma mem_edge_set {v w : V G} : ⟦(v, w)⟧ ∈ G.edge_set ↔ v ~g w :=
by refl

lemma adj_iff_exists_edge {v w : V G} :
  v ~g w ↔ v ≠ w ∧ ∃ (e ∈ G.edge_set), v ∈ e ∧ w ∈ e :=
begin
  split, { intro, use [ne_of_adj a, ⟦(v,w)⟧], simpa },
  { rintro ⟨hne, e, he, hv⟩,
    rw sym2.elems_iff_eq hne at hv,
    subst e,
    rwa mem_edge_set at he, }
end

lemma edge_other_ne {e : sym2 (V G)} (he : e ∈ G.edge_set) {v : V G} (h : v ∈ e) : h.other ≠ v :=
sym2.mem_from_rel_irrefl_other_ne (loopless G) he h

instance edge_set_fintype [decidable_eq (V G)] [fintype (V G)] [decidable_rel G.adj] :
  fintype G.edge_set :=
by { dunfold edge_set, exact subtype.fintype _ }

section edge_finset
variable (G)
variables [fintype G.edge_set]

/--
The `edge_set` of the graph as a `finset`.
-/
def edge_finset : finset (sym2 (V G)) :=
set.to_finset G.edge_set

variable {G}

@[simp] lemma mem_edge_finset (e : sym2 (V G)) :
  e ∈ G.edge_finset ↔ e ∈ G.edge_set :=
by { dunfold edge_finset, simp }

@[simp] lemma edge_set_univ_card : (univ : finset G.edge_set).card = G.edge_finset.card :=
fintype.card_of_subtype G.edge_finset mem_edge_finset

end edge_finset

@[simp] lemma irrefl {v : V G} : ¬(v ~g v) := G.loopless v

@[symm] lemma adj_symm (u v : V G) : u ~g v ↔ v ~g u := ⟨λ x, G.symm x, λ x, G.symm x⟩

@[simp] lemma mem_neighbor_set (v w : V G) : w ∈ neighbor_set v ↔ v ~g w :=
by tauto

@[simp] lemma mem_incident_set (v w : V G) : ⟦(v, w)⟧ ∈ incident_set v ↔ v ~g w :=
by { dsimp [incident_set], simp }

lemma neighbor_set_edge_prop {v w : V G} (h : w ∈ neighbor_set v) : ⟦(v, w)⟧ ∈ incident_set v :=
by { rw mem_neighbor_set at h, simpa }

lemma adj_incident_set_inter {v : V G} {e : sym2 (V G)} (he : e ∈ G.edge_set) (h : v ∈ e) :
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
by { cases h, rwa [←sym2.mem_other_spec' h_right, mem_edge_set] at h_left }

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

instance neighbor_set_fintype [decidable_rel G.adj] (v : V G) : fintype (neighbor_set v) :=
@subtype.fintype _ _ (by { simp_rw mem_neighbor_set, apply_instance }) _

lemma neighbor_finset_eq_filter {v : V G} [decidable_rel G.adj] :
  neighbor_finset v = univ.filter (G.adj v) :=
by { ext, simp }

/--
The minimal degree of all vertices
-/
def min_deg (G : simple_graph) [fintype (V G)] [nonempty (V G)] [decidable_rel G.adj] : ℕ :=
finset.min' (univ.image (λ (v : V G), degree v)) (nonempty.image univ_nonempty _)

/--
The maximal degree of all vertices
-/
def max_deg (G : simple_graph) [fintype (V G)] [h : nonempty (V G)] [decidable_rel G.adj]: ℕ :=
finset.max' (univ.image (λ (v : V G), degree v)) (nonempty.image univ_nonempty _)

end finite

section examples

/--
The graph with no edges on a given vertex type.
-/
def empty_graph (V : Type u) : simple_graph_on V :=
{ adj := λ i j, false }

/--
The complete graph on a type `α` is the simple graph with all pairs of distinct vertices adjacent.
-/
def complete_graph (V : Type u) : simple_graph_on V :=
{ adj := ne }

@[simp]
lemma simple_graph_from_rel_adj {α : Type u} (r : α → α → Prop) (v w : V ↟(simple_graph_from_rel r)) :
  v ~g w ↔ v ≠ w ∧ (r v w ∨ r w v) :=
by refl

@[simp]
lemma simple_graph_from_rel_adj' {α : Type u} (r : α → α → Prop) (v w : α) :
  @simple_graph.adj' ↟(simple_graph_from_rel r) v w ↔ v ≠ w ∧ (r v w ∨ r w v) :=
by refl

/--
A path graph on n+1 vertices, which has n edges.
-/
def path_graph (n : ℕ) : simple_graph_on (fin (n + 1)) :=
{ adj := λ i j, j.1 = i.1 + 1 ∨ i.1 = j.1 + 1,
  symm' := λ x y h, or.elim h or.inr or.inl,
  loopless' := by { intros x h, cases h; linarith } }

lemma path_graph_adj (n : ℕ) (a b : fin (n + 1)) :
  @adj' ↟(path_graph n) a b ↔ b.1 = a.1 + 1 ∨ a.1 = b.1 + 1 :=
by refl

/--
A graph on `n` vertices with `n` edges in a cycle
-/
def cycle_graph (n : ℕ) (three_le : 3 ≤ n) : simple_graph_on (zmod n) :=
{ adj := λ i j, i = j + (1 : ℕ) ∨ j = i + (1 : ℕ),
  symm' := λ x y h, or.elim h or.inr or.inl,
  loopless' := by { intros x h, rw or_self at h,
                    have h' := congr_arg (λ y, y - x) h,
                    simp only [add_sub_cancel', sub_self] at h',
                    have h'' := congr_arg zmod.val h',
                    change ((0 : ℕ) : zmod n).val = _ at h'',
                    repeat { rw zmod.val_cast_nat at h'' },
                    rw nat.zero_mod at h'',
                    rw nat.mod_eq_of_lt at h'',
                    cc, linarith, } }

def complete_partite_graph {ι : Type u} (f : ι → Type v) : simple_graph_on (Σ i : ι, f i) :=
{ adj := λ v w, v.1 ≠ w.1 }

end examples


section graph_operations

def two_pt_quo {β : Type*} (v w : β) := @quot β (λ i j, i = j ∨ (i = v ∧ j = w) ∨ (i = w ∧ j = v))

def contract_edge (G : simple_graph) {v w : V G} (h : v ~g w) : simple_graph_on (two_pt_quo v w) :=
{ adj := λ i j, quot.out i ~g quot.out j,
  symm' :=
    begin
      intros x y h,
      apply symm,
      exact h,
    end,
  loopless' :=
    begin
      intro x,
      simp,
    end,
}

def delete_edge (G : simple_graph) {v w : V G} (h : v ~g w) : simple_graph_on (G.V) :=
{ adj := λ i j, (¬ ((i = v ∧ j = w) ∨ (i = w ∧ j = v)) ∧ i ~g j),
  symm' :=
    begin
      intros x y h,
      push_neg,
      push_neg at h,
      rcases h with ⟨⟨h1, h2⟩, h3⟩,
      split,
      split,
      intro hvy,
      simp,
      by_contra,
      specialize h2 a,
      apply h2,
      exact hvy,

      intro hyw,
      simp,
      by_contra,
      specialize h1 a,
      apply h1,
      exact hyw,

      apply symm,
      exact h3,
    end,
  loopless' :=
    begin
      intros x,
      push_neg,
      intro h1,

      exact G.loopless x,
    end }

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

section complete_graphs

instance from_rel_inhabited (α : Type u) : inhabited (simple_graph_on α) :=
⟨complete_graph α⟩

variables (α : Type u) [decidable_eq α]

instance complete_graph_adj_decidable :
  decidable_rel (adj ↟(complete_graph α)) :=
by { dsimp [complete_graph], apply_instance }

variables [fintype α]

@[simp]
lemma complete_graph_degree (v : V ↟(complete_graph α)) :
  degree v = fintype.card α - 1 :=
begin
  convert univ.card.pred_eq_sub_one,
  erw [degree, neighbor_finset_eq_filter, filter_ne, card_erase_of_mem (mem_univ v)],
end

lemma complete_graph_is_regular :
  is_regular_of_degree ↟(complete_graph α) (fintype.card α - 1) :=
by { intro v, simp }

end complete_graphs


end simple_graph
