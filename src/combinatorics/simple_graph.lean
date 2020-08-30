/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov
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
Since graphs are terms rather than types, the usual mathlib techniques
for dealing with objects and subobjects in a uniform way is
implemented a bit differently.

The type of a simple graph on a given vertex type is `simple_graph V`,
and a type `α` whose terms have an interpretation as a simple graph
should define an instance `simple_graphs α`.

Proofs that apply to graphs in general should avoid using `G : simple_graph V`
directly, and instead one should prove statements about terms that have graph
interpretations.  As a `variables` declaration, this would be
```
variables {α : Type*} [simple_graphs α] (G : α)
```
This typeclass defines a `to_simple_graph` function to obtain the term's simple
graph.  One should use the accessor functions in the `accessor_functions`
section.  For example, `adj G` refers to `(simple_graphs.to_simple_graph G).adj`.

With this design in place, then for `G : α`, there is a type `subgraph G` whose
terms consist of all the subgraphs of `G`.  This type forms a bounded lattice.

There is a basic API for locally finite graphs and for graphs with
finitely many vertices.  We take the convention that a graph is finite at
a given vertex `v` if `[fintype (neighbor_set v)]`, and it has finitely many
vertices if `[fintype (V G)]`.

## Main definitions

* `simple_graph_on V` is the type for simple graphs on a given vertex type.
  It forms a bounded lattice.

* `simple_graphs` is a class for a type whose terms can be interpreted as
  simple graphs.

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
open_locale big_operators
universes u v

/--
Basic constructor for a simple graph, using a symmetric irreflexive relation.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent edges;
see `simple_graph.edge_set` for the corresponding edge set.

When proving statements about simple graphs in general, one should use the
`simple_graphs` typeclass.
-/
@[ext]
structure simple_graph_on (V : Type u) :=
(adj : V → V → Prop)
(symm : symmetric adj . obviously)
(loopless : irreflexive adj . obviously)


/--
This typeclass gives a simple graph interpretation of every term of a given type.
A simple graph is an irreflexive symmetric relation `adj` on a vertex type `V`,
using the `simple_graph_on V` structure.
-/
class simple_graphs (α : Type u) :=
(V : α → Type v)
(to_simple_graph : Π (G : α), simple_graph_on (V G))

/--
Every `simple_graph_on` tautologically has an interpretation as a simple graph.
-/
@[simps]
instance simple_graph_on.simple_graphs (V : Type u) : simple_graphs (simple_graph_on V) :=
{ V := λ _, V,
  to_simple_graph := id }

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
variables {α : Type*} [simple_graphs α]

/--
Get the simple graph's vertex type.
-/
@[reducible]
def V (G : α) := simple_graphs.V G

/--
The simple graph's adjacency relation.
-/
@[reducible]
def adj (G : α) : V G → V G → Prop := (simple_graphs.to_simple_graph G).adj

/--
For an infix adjacency relation to work, it is useful to have this abbreviation for `adj`.
-/
abbreviation adj' {G : α} : V G → V G → Prop := adj G

infix ` ~g ` : 40 := adj'

@[simp] lemma adj_as_adj' {G : α} (v w : V G) : adj G v w ↔ v ~g w := by refl

/--
The simple graph's axiom that the adjacency relation is symmetric.
-/
@[reducible]
lemma symm (G : α) : symmetric (adj G) := (simple_graphs.to_simple_graph G).symm

/--
The simple graph's axiom that the adjacency relation is irreflexive.
-/
@[reducible]
lemma loopless (G : α) : irreflexive (adj G) := (simple_graphs.to_simple_graph G).loopless

end simple_graph
end accessor_functions

/--
Construct the simple graph induced by the given relation.  It
symmetrizes the relation and makes it irreflexive.
-/
def simple_graph_from_rel {V : Type u} (r : V → V → Prop) : simple_graph_on V :=
{ adj := λ a b, (a ≠ b) ∧ (r a b ∨ r b a),
  symm := by finish,
  loopless := by finish }


namespace simple_graph

variables {α : Type u} [simple_graphs α] {G : α}

/-- `neighbor_set v` is the set of vertices adjacent to `v` in `G`. -/
def neighbor_set (v : V G) : set (V G) := set_of (adj G v)

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
lemma mem_edge_set {v w : V G} : ⟦(v, w)⟧ ∈ edge_set G ↔ v ~g w :=
by refl

lemma adj_iff_exists_edge {v w : V G} :
  v ~g w ↔ v ≠ w ∧ ∃ (e ∈ edge_set G), v ∈ e ∧ w ∈ e :=
begin
  split, { intro, use [ne_of_adj a, ⟦(v,w)⟧], simpa },
  { rintro ⟨hne, e, he, hv⟩,
    rw sym2.elems_iff_eq hne at hv,
    subst e,
    rwa mem_edge_set at he, }
end

lemma edge_other_ne {e : sym2 (V G)} (he : e ∈ edge_set G) {v : V G} (h : v ∈ e) : h.other ≠ v :=
sym2.mem_from_rel_irrefl_other_ne (loopless G) he h

instance edge_set_fintype [decidable_eq (V G)] [fintype (V G)] [decidable_rel (adj G)] :
  fintype (edge_set G) :=
by { dunfold edge_set, exact subtype.fintype _ }

section edge_finset
variable (G)
variables [fintype (edge_set G)]

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

instance neighbor_set_fintype [decidable_rel (adj G)] (v : V G) : fintype (neighbor_set v) :=
@subtype.fintype _ _ (by { simp_rw mem_neighbor_set, apply_instance }) _

lemma neighbor_finset_eq_filter {v : V G} [decidable_rel (adj G)] :
  neighbor_finset v = univ.filter (adj G v) :=
by { ext, simp }

@[simp]
lemma card_simple_graph_on_eq (α : Type u) (G : simple_graph_on α) [fintype α] :
fintype.card (V G) = fintype.card α := rfl

/--
The minimal degree of all vertices
-/
def min_deg (G : α) [fintype (V G)] [h : nonempty (V G)] [decidable_rel (adj G)]: ℕ :=
finset.min' ((univ : finset (V G)).image (λ v, degree v)) (match h with
| nonempty.intro v := begin use degree v, simp only [mem_image, mem_univ, exists_prop_of_true], use v, end
end)

/--
The maximal degree of all vertices
-/
def max_deg (G : α) [fintype (V G)] [h : nonempty (V G)] [decidable_rel (adj G)]: ℕ :=
finset.max' ((univ : finset (V G)).image (λ v, degree v)) (match h with
| nonempty.intro v := begin use degree v, simp only [mem_image, mem_univ, exists_prop_of_true], use v, end
end)


end finite

end simple_graph

namespace simple_graph

section maps

variables {α α' : Type*} [simple_graphs α] [simple_graphs α'] (G : α) (G' : α')

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

variables {G} {G'} (f : G →g G')

lemma map_adj {v w : V G} : v ~g w → f v ~g f w :=
by apply f.map_adj'

def map_edge_set : edge_set G → edge_set G' :=
λ e, ⟨sym2.map f e.val, begin
  rcases e with ⟨e, h⟩,
  refine quotient.rec_on_subsingleton e (λ e h, _) h,
  rcases e with ⟨v, w⟩,
  simp only [sym2.map_pair_eq, mem_edge_set],
  exact f.map_adj' (mem_edge_set.mp h),
end⟩

def map_neighbor_set (v : V G) : neighbor_set v → neighbor_set (f v) :=
λ w, ⟨f w.val, begin
  rcases w with ⟨w, h⟩,
  rw mem_neighbor_set at h ⊢,
  exact map_adj f h,
end⟩

variables {α'' : Type*} [simple_graphs α''] {G'' : α''}

/--
Composition of graph homomorphisms
-/
def comp (f' : G' →g G'') (f : G →g G') : G →g G'' :=
{ to_fun := ⇑f' ∘ ⇑f,
  map_adj' := by { intros v w h, repeat { rw function.comp_app }, exact f'.map_adj' (f.map_adj' h) } }

infixr ` ∘ ` := comp

@[simp] lemma comp_app (f' : G' →g G'') (f : G →g G') (v : V G) : (comp f' f) v = f' (f v) := rfl

end homomorphism

/--
A graph embedding is an embedding on vertex sets that respects the adjacency relations.
-/
@[ext]
structure embedding extends V G ↪ V G' :=
(map_adj' : ∀ {v w : V G}, v ~g w → to_fun v ~g to_fun w)

infix ` ↪g ` : 50 := embedding

namespace embedding

instance coe_to_fun : has_coe_to_fun (G ↪g G') :=
⟨_, λ f, f.to_fun⟩

variables {G} {G'} (f : G ↪g G')

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
def to_homomorphism (f : G ↪g G') : G →g G' :=
{ to_fun := f.to_fun,
  map_adj' := f.map_adj' }

instance : has_lift (G ↪g G') (G →g G') :=
{ lift := to_homomorphism }

lemma map_adj {v w : V G} : v ~g w → f v ~g f w :=
by apply f.map_adj'

def map_edge_set : edge_set G ↪ edge_set G' :=
{ to_fun := homomorphism.map_edge_set ↑f,
  inj' := begin
    rintros ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ h,
    dsimp [homomorphism.map_edge_set] at h,
    rw subtype.mk_eq_mk at h ⊢,
    refine quotient.rec_on_subsingleton e₁ (λ e₁ h₁ h, _) h₁ h,
    refine quotient.rec_on_subsingleton e₂ (λ e₂ h₂ h, _) h₂ h,
    rcases e₁ with ⟨x₁, y₁⟩, rcases e₂ with ⟨x₂, y₂⟩,
    repeat { rw sym2.map_pair_eq at h },
    rw sym2.eq_iff at h ⊢,
    cases h; rw [f.inj' h_1.1, f.inj' h_1.2]; simp,
  end }

def map_neighbor_set (v : V G) : neighbor_set v ↪ neighbor_set (f v) :=
{ to_fun := λ w, ⟨f w.val, begin
    rcases w with ⟨w, h⟩,
    rw mem_neighbor_set at h ⊢,
    exact map_adj f h,
  end⟩,
  inj' := begin
    rintros ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h,
    rw subtype.mk_eq_mk at h ⊢,
    exact f.inj' h,
  end }

variables {α'' : Type*} [simple_graphs α''] {G'' : α''}

/--
Composition of graph embeddings
-/
def comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' :=
{ to_fun := ⇑f' ∘ ⇑f,
  inj' := by { intros v w h, exact f.inj' (f'.inj' h) },
  map_adj' := by { intros v w h, repeat { rw function.comp_app }, exact f'.map_adj' (f.map_adj' h) } }

infixr ` ∘ ` := comp

@[simp] lemma comp_app (f' : G' ↪g G'') (f : G ↪g G') (v : V G) : (comp f' f) v = f' (f v) := rfl

end embedding

/--
A graph isomorphism is an equivalence on vertex sets that preserves the adjacency relations exactly.
-/
@[reducible]
def isomorphism := rel_iso (@adj' _ _ G) (adj G')

infix ` ≃g ` : 50 := isomorphism

namespace isomorphism

variables {G} {G'} (f : G ≃g G')

def to_embedding (f : G ≃g G') : G ↪g G' :=
{ to_fun := f.to_fun,
  inj' := f.injective,
  map_adj' := λ v w h, (rel_iso.map_rel_iff f).mp h }

instance : has_lift (G ≃g G') (G ↪g G') :=
{ lift := to_embedding }

lemma map_adj_iff {v w : V G} : v ~g w ↔ f v ~g f w :=
by apply f.map_rel_iff'

def map_edge_set : edge_set G ≃ edge_set G' :=
{ to_fun := homomorphism.map_edge_set ↑f,
  inv_fun := homomorphism.map_edge_set ↑f.symm,
  left_inv := begin
    rintro ⟨e, h⟩,
    refine quotient.rec_on_subsingleton e (λ e h, _) h,
    rcases e with ⟨v, w⟩,
    dsimp [homomorphism.map_edge_set],
    unfold_coes, dsimp [to_embedding, embedding.to_homomorphism],
    simp,
  end,
  right_inv := begin
    rintro ⟨e, h⟩,
    refine quotient.rec_on_subsingleton e (λ e h, _) h,
    rcases e with ⟨v, w⟩,
    dsimp [homomorphism.map_edge_set],
    unfold_coes, dsimp [to_embedding, embedding.to_homomorphism],
    simp,
  end }

variables {α'' : Type*} [simple_graphs α''] {G'' : α''}

/--
Composition of graph isomorphisms
-/
def comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' :=
{ to_fun := ⇑f' ∘ ⇑f,
  inv_fun := ⇑f.symm ∘ ⇑f'.symm,
  left_inv := by { intro v, simp },
  right_inv := by { intro v, simp },
  map_rel_iff' := by { intros v w, simp only [equiv.coe_fn_mk, function.comp_app, adj_as_adj'],
                       repeat { rw function.comp_app },
                       exact iff.trans (map_adj_iff f) (map_adj_iff f') } }

infixr ` ∘ ` := comp

@[simp] lemma comp_app (f' : G' ≃g G'') (f : G ≃g G') (v : V G) : (comp f' f) v = f' (f v) := rfl


lemma iso_has_eq_order [fintype (V G)] [fintype (V G')] (f : G ≃g G') : fintype.card (V G) = fintype.card (V G') :=
by { convert (fintype.of_equiv_card f.to_equiv).symm }

lemma iso_has_eq_size
[fintype (edge_set G)] [fintype (edge_set G')] (f : G ≃g G') :
  (edge_finset G).card = (edge_finset G').card :=
begin
  convert_to fintype.card (edge_set G) = fintype.card (edge_set G'); try { exact multiset.card_map subtype.val _ },
  convert (fintype.of_equiv_card (isomorphism.map_edge_set f)).symm,
end

end isomorphism


end maps

section examples

/--
The graph with no edges on a given vertex type.
-/
def empty_graph (V : Type u) : simple_graph_on V := { adj := λ i j, false }

/--
The complete graph on a type `α` is the simple graph with all pairs of distinct vertices adjacent.
-/
def complete_graph (α : Type u) : simple_graph_on α :=
{ adj := ne }

end examples

section subgraphs

/-!
## Subgraphs of a graph
-/

variables {α : Type u} [simple_graphs α] (G : α)

/--
A subgraph of a graph is a subset of vertices and a subset of edges
such that each endpoint of an edge is contained in the vertex set.

Subgraphs implement the `simple_graph` class.  They also form a bounded lattice.

Note: subgraphs could also have been defined as in `subgraph.of_edge_set'`.  We prove this alternative definition is equivalent.
-/
@[ext]
structure subgraph :=
(V' : set (V G))
(adj' : V G → V G → Prop)
(adj_sub : ∀ ⦃v w : V G⦄, adj' v w → v ~g w)
(edge_vert : ∀ ⦃v w : V G⦄, adj' v w → v ∈ V')
(symm' : symmetric adj')

namespace subgraph

variable {G}

def edge_set' (G' : subgraph G) : set (sym2 (V G)) := sym2.from_rel G'.symm'

@[simp]
lemma mem_edge_set' {G' : subgraph G} {v w : V G} : ⟦(v, w)⟧ ∈ edge_set' G' ↔ G'.adj' v w :=
by refl

lemma edge_sub (G' : subgraph G) : G'.edge_set' ⊆ edge_set G :=
begin
  intro e,
  refine quotient.rec_on_subsingleton e (λ e, _),
  cases e with v w,
  simp only [mem_edge_set', mem_edge_set],
  apply G'.adj_sub,
end

lemma has_verts (G' : subgraph G) : ∀ ⦃e : sym2 (V G)⦄ ⦃v : V G⦄, e ∈ G'.edge_set' → v ∈ e → v ∈ G'.V' :=
begin
  intro e,
  refine quotient.rec_on_subsingleton e (λ e, _),
  cases e with v w, intros u he hu,
  simp only [mem_edge_set'] at he,
  cases sym2.mem_iff.mp hu; subst u,
  exact G'.edge_vert he,
  exact G'.edge_vert (G'.symm' he),
end

lemma adj_symm' (G' : subgraph G) ⦃v w : V G⦄ : G'.adj' v w ↔ G'.adj' w v :=
by { split; apply G'.symm' }

@[simps]
instance subgraph.simple_graph : simple_graphs (subgraph G) :=
{ V := λ G', G'.V',
  to_simple_graph := λ G',
  { adj := λ v w, G'.adj' ↑v ↑w,
    symm := λ v w h, G'.symm' h,
    loopless := λ ⟨v, _⟩ h, loopless G v (G'.adj_sub h) } }

instance has_lift.subgraph_V (G' : subgraph G) : has_lift (V G') (V G) :=
{ lift := subtype.val }

/--
Give the vertex as an element of the subgraph's vertex type.
-/
@[reducible]
def vert (G' : subgraph G) (v : V G) (h : v ∈ G'.V') : V G' :=
subtype.mk v h

@[simp]
lemma adj_iff_adj' {G' : subgraph G} {v w : V G} (hv : v ∈ G'.V') (hw : w ∈ G'.V') :
  G'.vert v hv ~g G'.vert w hw ↔ G'.adj' v w :=
by tidy

/--
Given a subgraph, replace the vertex set with an equal set.
The resulting subgraph is equal (see `copy_eq`).
-/
def copy (G' : subgraph G)
(V'' : set (V G)) (hV : V'' = G'.V')
(adj'' : V G → V G → Prop) (hadj : adj'' = G'.adj') :
  subgraph G :=
{ V' := V'',
  adj' := adj'',
  adj_sub := hadj.symm ▸ G'.adj_sub,
  edge_vert := hV.symm ▸ hadj.symm ▸ G'.edge_vert,
  symm' := hadj.symm ▸ G'.symm' }

lemma copy_eq (G' : subgraph G)
(V'' : set (V G)) (hV : V'' = G'.V')
(adj'' : V G → V G → Prop) (hadj : adj'' = G'.adj') :
  G'.copy V'' hV adj'' hadj = G' :=
subgraph.ext _ _ hV hadj

section alternative_definition

/--
Another way to define a subgraph is using a vertex set and an edge subset,
subject to some compatibility relation.
-/
@[ext]
protected structure of_edge_set' (G : α) :=
(V' : set (V G))
(edge_set' : set (sym2 (V G)))
(edge_sub : edge_set' ⊆ edge_set G)
(has_verts : ∀ ⦃e : sym2 (V G)⦄ ⦃v : V G⦄, e ∈ edge_set' → v ∈ e → v ∈ V')

@[simps]
instance of_edge_set.simple_graph : simple_graphs (of_edge_set' G) :=
{ V := λ G', G'.V',
  to_simple_graph := λ G',
  { adj := λ v w, ⟦(↑v, ↑w)⟧ ∈ G'.edge_set',
    symm := λ v w h, by rwa sym2.eq_swap,
    loopless := λ ⟨v, _⟩ h, loopless G v (sym2.from_rel_prop.mp (G'.edge_sub h)) } }

/--
The type `of_edge_set' G` is equivalent to `subgraph G`.  See `iso_of_edge_set'`.
-/
protected
def equiv_of_edge_set' : subgraph G ≃ of_edge_set' G :=
{ to_fun := λ G', { V' := G'.V',
                    edge_set' := edge_set' G',
                    edge_sub := edge_sub G',
                    has_verts := has_verts G' },
  inv_fun := λ G', { V' := G'.V',
                     adj' := λ v w, ⟦(v, w)⟧ ∈ G'.edge_set',
                     adj_sub := λ v w h, mem_edge_set.mp (G'.edge_sub h),
                     edge_vert := λ v w h, G'.has_verts h (sym2.mk_has_mem _ _),
                     symm' := λ v w h, by rwa sym2.eq_swap },
  left_inv := by tidy,
  right_inv := by tidy }

/--
The equivalence from `equiv_of_edge_set'` sends graphs to isomorphic graphs.
-/
protected
def iso_of_edge_set' (G' : subgraph G) : G' ≃g subgraph.equiv_of_edge_set' G' :=
{ to_fun := id,
  inv_fun := id,
  left_inv := by tidy,
  right_inv := by tidy,
  map_rel_iff' := by tidy }

end alternative_definition

/--
The relation that one subgraph is a subgraph of another.
-/
def is_subgraph (x y : subgraph G) : Prop := x.V' ⊆ y.V' ∧ ∀ ⦃v w : V G⦄, x.adj' v w → y.adj' v w

/--
The union of two subgraphs.
-/
def union (x y : subgraph G) : subgraph G :=
{ V' := x.V' ∪ y.V',
  adj' := λ v w, x.adj' v w ∨ y.adj' v w,
  adj_sub := λ v w h, begin
    cases h,
    exact x.adj_sub h,
    exact y.adj_sub h,
  end,
  edge_vert := λ v w h, begin
    cases h,
    left, exact x.edge_vert h,
    right, exact y.edge_vert h,
  end,
  symm' := λ v w h, by rwa [x.adj_symm', y.adj_symm'] }

/--
The intersection of two subgraphs.
-/
def inter (x y : subgraph G) : subgraph G :=
{ V' := x.V' ∩ y.V',
  adj' := λ v w, x.adj' v w ∧ y.adj' v w,
  adj_sub := λ v w h, x.adj_sub h.1,
  edge_vert := λ v w h, ⟨x.edge_vert h.1, y.edge_vert h.2⟩,
  symm' := λ v w h, by rwa [x.adj_symm', y.adj_symm'] }

instance : has_union (subgraph G) := ⟨union⟩
instance : has_inter (subgraph G) := ⟨inter⟩

/--
The `top` subgraph is `G` as a subgraph of itself.
-/
def top : subgraph G :=
{ V' := set.univ,
  adj' := adj G,
  adj_sub := λ v w h, h,
  edge_vert := λ v w h, set.mem_univ v,
  symm' := symm G }

/--
The `bot` subgraph is the subgraph with no vertices or edges.
-/
def bot : subgraph G :=
{ V' := ∅,
  adj' := λ v w, false,
  adj_sub := λ v w h, false.rec _ h,
  edge_vert := λ v w h, false.rec _ h,
  symm' := by tidy }

instance subgraph_inhabited : inhabited (subgraph G) := ⟨bot⟩

instance : bounded_lattice (subgraph G) :=
{ le := is_subgraph,
  sup := union,
  inf := inter,
  top := top,
  bot := bot,
  le_refl := by tidy,
  le_trans := by tidy,
  le_antisymm := begin
    intros x y hxy hyx,
    cases x, cases y, congr,
    exact set.subset.antisymm hxy.1 hyx.1,
    ext v w, split, apply hxy.2, apply hyx.2,
  end,
  le_top := λ x, ⟨set.subset_univ _, (λ v w h, x.adj_sub h)⟩,
  bot_le := λ x, ⟨set.empty_subset _, (λ v w h, false.rec _ h)⟩,
  sup_le := by { intros x y z hxy hyz,
                 exact ⟨set.union_subset hxy.1 hyz.1,
                        (λ v w h, by { cases h, exact hxy.2 h, exact hyz.2 h })⟩, },
  le_sup_left := λ x y, ⟨set.subset_union_left x.V' y.V', (λ v w h, or.inl h)⟩,
  le_sup_right := λ x y, ⟨set.subset_union_right x.V' y.V', (λ v w h, or.inr h)⟩,
  le_inf := λ x y z hxy hyz, ⟨set.subset_inter hxy.1 hyz.1, (λ v w h, ⟨hxy.2 h, hyz.2 h⟩)⟩,
  inf_le_left := λ x y, ⟨set.inter_subset_left x.V' y.V', (λ v w h, h.1)⟩,
  inf_le_right := λ x y, ⟨set.inter_subset_right x.V' y.V', (λ v w h, h.2)⟩ }

/--
The top of the `subgraph G` lattice is equivalent to the graph itself.
-/
def top_equiv_graph : (⊤ : subgraph G) ≃g G :=
{ to_fun := λ v, ↑v,
  inv_fun := λ v, ⟨v, by tidy⟩,
  left_inv := by tidy,
  right_inv := by tidy,
  map_rel_iff' := by tidy }

def bot_equiv_empty : (⊥ : subgraph G) ≃g empty_graph empty :=
{ to_fun := λ v, false.elim v.property,
  inv_fun := λ v, begin cases v, end,
  left_inv := by tidy,
  right_inv := by tidy,
  map_rel_iff' := by tidy }

/--
Given two subgraphs, one a subgraph of the other, there is an induced embedding of the subgraphs as graphs.
-/
def map {x y : subgraph G} (h : x ≤ y) : x ↪g y :=
{ to_fun := λ v, ⟨↑v, and.left h v.property⟩,
  inj' := λ v w h, subtype.ext (subtype.mk_eq_mk.mp h),
  map_adj' := λ v w hvw, begin
    cases v with v hv, cases w with w hw,
    rw adj_iff_adj' at hvw ⊢,
    exact h.2 hvw,
  end }

/--
A subgraph of `G` embeds in `G`.
-/
def map_top (x : subgraph G) : x ↪g G :=
{ to_fun := λ v, ↑v,
  inj' := λ v w h, subtype.ext h,
  map_adj' := λ v w hvw, begin
    cases v with v hv, cases w with w hw,
    rw subgraph.adj_iff_adj' at hvw,
    exact x.adj_sub hvw,
  end }

@[simp]
lemma map_top_to_fun {x : subgraph G} (v : x.V') : x.map_top v = v.val := rfl

/--
The induced subgraph of a graph is the graph with a specified vertex
set along with all the edges whose endpoints lie in the set.

Note: `induced' V' = induced ⊤ V'`.  TODO decide whether to remove this function.
-/
def induced' (V' : set (V G)) : subgraph G :=
{ V' := V',
  adj' := λ v w, v ∈ V' ∧ w ∈ V' ∧ v ~g w,
  adj_sub := λ v w ⟨hv, hw, he⟩, he,
  edge_vert := λ v w ⟨hv, hw, he⟩, hv,
  symm' := λ v w ⟨hv, hw, he⟩, ⟨hw, hv, symm G he⟩ }

/--
Given a subgraph `G'` and a vertex set `V'`, produces another subgraph on `V'` whose edges consist
of all those edges in `G'` whose endpoints lie in `V'`.  Note that the vertex set
might have vertices outside `V G'`.
-/
def induced (G' : subgraph G) (V' : set (V G)) : subgraph G :=
{ V' := V',
  adj' := λ v w, v ∈ V' ∧ w ∈ V' ∧ G'.adj' v w,
  adj_sub := λ v w ⟨hv, hw, he⟩, G'.adj_sub he,
  edge_vert := λ v w ⟨hv, hw, he⟩, hv,
  symm' := λ v w ⟨hv, hw, he⟩, ⟨hw, hv, G'.symm' he⟩ }

/--
The subgraph obtained by deleting a set `W` of vertices along with all the incident edges.
-/
def delete (G' : subgraph G) (W : set (V G)) : subgraph G :=
{ V' := {v : V G | v ∈ G'.V' ∧ v ∉ W},
  adj' := λ v w, v ∉ W ∧ w ∉ W ∧ G'.adj' v w,
  adj_sub := λ v w ⟨hv, hw, he⟩, G'.adj_sub he,
  edge_vert := λ v w ⟨hv, hw, he⟩, ⟨G'.edge_vert he, hv⟩,
  symm' := λ v w ⟨hv, hw, he⟩, ⟨hw, hv, G'.symm' he⟩ }

/--
The subgraph obtained by adding an edge between vertices a and b.  If `a = b`, then this
results in the same subgraph.
-/
def join_verts (G' : subgraph G) {a b : V G} (hab : a ~g b) : subgraph G :=
{ V' := G'.V' ∪ {a, b},
  adj' := λ v w, (v = a ∧ w = b ∨ v = b ∧ w = a) ∨ G'.adj' v w,
  adj_sub := λ v w h, begin
    cases h, cases h; rwa [h.1, h.2], rwa adj_symm,
    exact G'.adj_sub h,
  end,
  edge_vert := λ v w h, by { cases h, swap, left, exact G'.edge_vert h, tidy },
  symm' := λ v w h, by { cases h, { left, tidy, }, { right, exact G'.symm' h, } } }

/--
A characterization of the neighbor set of a subgraph as a subset of the neighbor set of the graph.
-/
def subgraph_neighbor_set_in_graph (G' : subgraph G) (v : V G') :
  neighbor_set v ≃ {w : neighbor_set (G'.map_top v) | G'.adj' ↑v w} :=
{ to_fun := λ w, ⟨⟨↑w, G'.adj_sub w.2⟩, w.2⟩,
  inv_fun := λ w, ⟨⟨↑w.1, G'.edge_vert (G'.symm' w.2)⟩, w.2⟩,
  left_inv := λ w, by simp,
  right_inv := λ w, by simp }

def subgraph_neighbor_set_in_supergraph {G' G'' : subgraph G} (h : G' ≤ G'') (v : V G') :
  neighbor_set v ≃ {w : neighbor_set (map h v) | G'.adj' ↑v ↑w} :=
{ to_fun := λ w, ⟨⟨map h w, h.2 w.2⟩, w.2⟩,
  inv_fun := λ w, ⟨⟨↑w, G'.edge_vert (G'.symm' w.2)⟩, w.2⟩,
  left_inv := λ w, by tidy,
  right_inv := λ w, by tidy }

/--
This instance also provides finiteness of subgraphs when `[decidable_rel (adj G)]` and `[fintype (V G)]`.
-/
instance finite_at
  {G' : subgraph G} [decidable_rel G'.adj'] (v : V G') [fintype (neighbor_set (G'.map_top v))] :
  fintype (neighbor_set v) :=
fintype.of_equiv _ (subgraph_neighbor_set_in_graph G' v).symm

/--
Not an instance because it depends on `h`.
-/
def finite_at_subgraph {G' G'' : subgraph G} [decidable_rel G'.adj'] [decidable_rel G''.adj']
(h : G' ≤ G'') (v : V G') [hf : fintype (neighbor_set (map h v))] :
  fintype (neighbor_set v) :=
fintype.of_equiv _ (subgraph_neighbor_set_in_supergraph h v).symm


lemma degree_le_top
{G' : subgraph G} [decidable_rel G'.adj'] (v : V G') [fintype (neighbor_set (G'.map_top v))] :
  degree v ≤ degree (G'.map_top v) :=
begin
  repeat {rw ←card_neighbor_set_eq_degree},
  let f := embedding.map_neighbor_set G'.map_top v,
  exact fintype.card_le_of_injective f.to_fun f.inj',
end

lemma degree_le
{G' G'' : subgraph G} [decidable_rel G'.adj'] [decidable_rel G''.adj'] (h : G' ≤ G'')
(v : V G') [fintype (neighbor_set v)] [fintype (neighbor_set (map h v))] :
  degree v ≤ degree (map h v) :=
begin
  repeat {rw ←card_neighbor_set_eq_degree},
  let f := embedding.map_neighbor_set (map h) v,
  exact fintype.card_le_of_injective f.to_fun f.inj',
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

variables {α : Type u} [simple_graphs α]

def two_pt_quo {β : Type*} (v w : β) := @quot β (λ i j, i = j ∨ (i = v ∧ j = w) ∨ (i = w ∧ j = v))

def contract_edge (G : α) {v w : V G} (h : v ~g w) : simple_graph_on (two_pt_quo v w) :=
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
  decidable_rel (adj (complete_graph α)) :=
by { dsimp [complete_graph, adj], apply_instance }

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

/-- thinking of a `path_graph (n + m)` as being a path of length n
followed by a path of length m, includes the first path. --/
def path_graph.incl₁ (n m : ℕ) : path_graph n ↪g path_graph (n + m) :=
{ to_fun := λ v, v,
  inj' := sorry,
  map_adj' := sorry }

def path_graph.incl₂ (n m : ℕ) : path_graph m ↪g path_graph (n + m) :=
{ to_fun := λ v, n + v,
  inj' := sorry,
  map_adj' := sorry }

section walks
variables {α : Type*} [simple_graphs α] (G : α)

/-
The composition of paths, following `pn` first and then `pm`.
-/
def walk_join {n m : ℕ} (pn : path_graph n →g G) (pm : path_graph m →g G) : path_graph (n+m) →g G :=
{ to_fun := λ v, if h : ↑v < n
                 then pn ⟨v, by linarith [h]⟩
                 else pm (by { cases v with v hv, rw [nat.add_assoc, nat.add_comm] at hv,
                               apply fin.sub_nat n ⟨v, hv⟩, dsimp at h, push_neg at h, exact h }),
  map_adj' := begin
    rintros ⟨v, hv⟩ ⟨w, hw⟩ h,
    simp, --split_ifs,
--    {apply pn.map_adj',   },
    sorry,
  end }

end walks

/--
"Flip over" the elements of `fin (n + 1)`, reversing `0` and `n`.
-/
def fin.flip (n : ℕ) : fin (n + 1) → fin (n + 1) := λ v, ((n - (v : ℕ) : ℕ) : fin (n + 1))
lemma fin.flip.invol (n : ℕ) : function.involutive (fin.flip n) :=
begin
  intro v, dsimp [fin.flip],
  rw fin.coe_coe_of_lt, swap, exact nat.sub_lt_succ n ↑v,
  cases v,
  convert_to ↑v_val = _, dsimp,
  have h : n - (n - v_val) = v_val, { have : v_val ≤ n, linarith, omega, },
  rw h, apply fin.val_injective, dsimp,
  rwa fin.coe_val_of_lt,
end

/--
A path graph is isomorphic to itself where the endpoints are swapped.
-/
def path_graph.invol (n : ℕ) : path_graph n ≃g path_graph n :=
{ to_fun := fin.flip n,
  inv_fun := fin.flip n,
  left_inv := fin.flip.invol n,
  right_inv := fin.flip.invol n,
  map_rel_iff' := begin
    intros v w, simp,
    split, rintros ⟨h₁, h₂⟩,
    cases h₂, rw h₂.1 at h₁ ⊢, dunfold fin.flip, sorry, sorry, sorry,
  end }

lemma path_graph.invol.prop₁ (n : ℕ) : (path_graph.invol n) 0 = n := by tidy
lemma path_graph.invol.prop₂ (n : ℕ) : (path_graph.invol n) n = 0 :=
begin
  change fin.flip n n = 0,
  dunfold fin.flip,
  apply fin.val_injective, dsimp,
  rw fin.coe_val_of_lt, rw fin.coe_coe_of_lt; linarith, omega,
end

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

namespace subgraph
variables {α : Type*} [simple_graphs α]

def is_cycle {G : α} (G' : subgraph G) : Prop := nonempty (Σ n : {n // 3 ≤ n}, cycle_graph n.1 n.2 ↪g G)

def cycles (G : α) : set (subgraph G) := { G' | is_cycle G' }

end subgraph

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

variables {α : Type u} [simple_graphs α] (G : α)

/--
A graph G is β-colorable if there is an assignment of elements of β to
vertices of G (allowing repetition) such that adjacent vertices have
distinct colors.
-/
@[ext]
structure coloring (β : Type v) :=
(color : V G → β)
(valid : ∀ ⦃v w : V G⦄, v ~g w → color v ≠ color w)

/--
A graph G is β-colorable if there is a β-coloring.
-/
def colorable (β : Type v) : Prop := nonempty (coloring G β)

/--
Given a coloring and a larger set of colors, one can extend the coloring set.
-/
def extend_coloring {β β' : Type*} (f : β ↪ β') : coloring G β ↪ coloring G β' :=
{ to_fun := λ F, { color := λ v, f (F.color v),
                   valid := begin
                     intros v w h hc, apply F.valid h, apply function.embedding.injective f, assumption,
                   end},
  inj' := begin intros F F' h, ext, apply function.embedding.injective f, simp at h, exact congr_fun h x, end
}

/--
Given a coloring and an embedding of a graph, one may restrict the coloring of the graph.
-/
def restrict_coloring {α' : Type*} [simple_graphs α'] {G : α} {G' : α'} (f : G ↪g G') {β : Type*} : coloring G' β → coloring G β :=
λ F, { color := λ v, F.color (f v),
       valid := begin
         rintros v w h hF,
         exact F.valid (f.map_adj' h) hF,
       end }

/--
Given a coloring of a graph, one may restrict the coloring to a subgraph.
-/
def restrict_coloring_subgraph {β : Type*} (G' : subgraph G) : coloring G β → coloring G' β :=
restrict_coloring G'.map_top

/--
A complete graph is colorable by its own vertex type.  (This means that if its vertex type
has cardinality n, then it is n-colorable.)
-/
def complete_graph_coloring (V : Type u) : coloring (complete_graph V) V :=
{ color := id,
  valid := by tidy }

lemma complete_graph_coloring_inj {V : Type u} [decidable_eq V] {β : Type v} (c : coloring (complete_graph V) β) :
  function.injective c.color :=
begin
  intros v w h,
  cases c with color valid,
  dsimp at h,
  by_contra,
  apply valid a,
  exact h,
end

lemma complete_graph_min_colors {n m : ℕ} (c : coloring (complete_graph (fin n)) (fin m)) : n ≤ m :=
begin
  have h := fintype.card_le_of_injective c.color (complete_graph_coloring_inj _),
  simp only [fintype.card_fin, card_simple_graph_on_eq] at h,
  exact h,
end

def coloring_equiv_complete_graph_hom (β : Type v) : coloring G β ≃ (G →g complete_graph β) :=
{ to_fun := λ c,
  { to_fun := c.color,
    map_adj' := λ v w a, coloring.valid c a },
  inv_fun := λ c,
    { color := c,
    valid := λ v w a, homomorphism.map_adj' c a },
  left_inv := by tidy,
  right_inv := by tidy }


end coloring

section connectivity

variables {α : Type u} [simple_graphs.{u v} α] (G : α)

/--
A walk of length `n` in a graph between vertices `v` and `w` is a sequence of `n + 1` vertices,
each related to the next by adjacency -- the `n` counts the edges along the way.
We model a walk as a graph homomorphism from a length-`n` path graph.
-/
def walk (n : ℕ) (v w : V G) : Type v := { f : path_graph n →g G // v = f 0 ∧ w = f n }

/--
Reverse a walk.
-/
def walk.symm {n : ℕ} {v w : V G} (p : walk G n v w) : walk G n w v :=
⟨p.val ∘ ↑(path_graph.invol n), begin
  simp, erw [path_graph.invol.prop₁ n, path_graph.invol.prop₂ n],
  use [p.2.2, p.2.1],
end⟩

/--
A path of length `n` in a graph between vertices `v` and `w` is a sequence of `n + 1` *distinct* vertices,
each related to the next by adjacency -- the `n` counts the edges along the way.
We model a path as a graph embedding from a length-`n` path graph.
-/
def path (n : ℕ) (v w : V G) : Type v := { f : path_graph n ↪g G // v = f 0 ∧ w = f n }

/-- The relation that there exists a walk of any length between two vertices. -/
def exists_walk : V G → V G → Prop := λ v w, nonempty (Σ (n : ℕ), walk G n v w)

/-- The relation that there exists a path of any length between two vertices. -/
def exists_path : V G → V G → Prop := λ v w, nonempty (Σ (n : ℕ), path G n v w)

@[refl] lemma exists_walk.refl (v : V G) : exists_walk G v v :=
by { use [0, λ _, v], tidy }

@[symm] lemma exists_walk.symm ⦃v w : V G⦄ (hvw : exists_walk G v w) : exists_walk G w v :=
by { tactic.unfreeze_local_instances, cases hvw, rcases hvw with ⟨n, p⟩, use [n, walk.symm G p], }

@[trans] lemma exists_walk.trans ⦃u v w : V G⦄ (huv : exists_walk G u v) (hvw : exists_walk G v w) : exists_walk G u w :=
begin
  tactic.unfreeze_local_instances, cases hvw, rcases hvw with ⟨m, pv⟩,
  tactic.unfreeze_local_instances, cases huv, rcases huv with ⟨n, pu⟩,
  --rcases huv with ⟨n, ⟨pu⟩⟩, rcases hvw with ⟨m, ⟨pv⟩⟩,
  use n+m,
  -- now need to concatenate walks  probably better to define path concatenation elsewhere and then use it here!
  sorry
end

lemma exists_walk.is_equivalence : equivalence (exists_walk G) :=
mk_equivalence _ (exists_walk.refl G) (exists_walk.symm G) (exists_walk.trans G)

def exists_walk.setoid : setoid (V G) := setoid.mk _ (exists_walk.is_equivalence G)

lemma exists_path_eq_exists_walk : exists_path G = exists_walk G :=
begin
  ext v w,
  sorry,
end

/--
The equivalence relation generated by `adj G` is another way `exists_walk G` could be defined.
-/
lemma exists_walk_eq_eqv_gen : exists_walk G = eqv_gen (adj G) :=
begin
  sorry
end

/--
Quotient of the vertex type by existence of walks.
-/
def connected_components := quotient (exists_walk.setoid G)

/-- Determines if a graph is connected -/
def is_connected : Prop := ∀ v w, exists_walk G v w

/-- The graph does not contain a cycle -/
def is_acyclic : Prop := ∀ (n : ℕ) (h : 3 ≤ n), (cycle_graph n h ↪g G) → false

/-- A tree is an acyclic connected graph -/
def is_tree : Prop := is_connected G ∧ is_acyclic G

end connectivity

section degree_sum

variables {α : Type u} [simple_graphs.{_ v} α] (G : α) [fintype (V G)] [decidable_eq (V G)] [decidable_rel (adj G)]

/--
A dart is an ordered pair of adjacent vertices, thought of as a little arrow from the
first vertex along an edge. (It is `uncurry (adj G)` as a subtype.)
-/
def darts : Type v := {d : V G × V G // d.1 ~g d.2}

/--
Gives the dart's edge.
-/
def dart_to_edge : darts G → edge_set G := λ d, ⟨⟦d.val⟧, d.property⟩
/--
Gives the dart's vertex.  This is the first vertex of the pair.
-/
def dart_to_vert : darts G → V G := λ d, d.val.1
/--
Reverses the dart: the new vertex is the vertex across the edge.
-/
def dart_reverse : darts G → darts G := λ d, ⟨(d.val.2, d.val.1), symm G d.property⟩

@[simp]
lemma dart_to_edge_of_dart_reverse (d : darts G) : dart_to_edge G (dart_reverse G d) = dart_to_edge G d :=
by { rcases d with ⟨⟨x, y⟩, h⟩,
     dsimp [dart_to_edge, dart_reverse], rw [subtype.mk_eq_mk, sym2.eq_swap] }


lemma dart_reverse_invol : function.involutive (dart_reverse G) :=
by { rintro ⟨⟨x, y⟩, h⟩, dsimp [dart_reverse], rw subtype.mk_eq_mk }

lemma dart_reverse_no_fixedpoint (d : darts G) : d ≠ dart_reverse G d :=
begin
  rcases d with ⟨⟨x, y⟩, h⟩,
  dsimp [dart_reverse],
  rw subtype.mk_eq_mk,
  intro heq, rw prod.mk.inj_iff at heq,
  rw [heq.1] at h,
  exact loopless G _ h,
end

lemma dart_edge_preimage (d₁ d₂ : darts G) :
  dart_to_edge G d₁ = dart_to_edge G d₂ ↔ d₁ = d₂ ∨ d₁ = dart_reverse G d₂ :=
begin
  rcases d₁ with ⟨⟨x₁, y₁⟩, h₁⟩,
  rcases d₂ with ⟨⟨x₂, y₂⟩, h₂⟩,
  dsimp [dart_to_edge, dart_reverse],
  repeat { rw subtype.mk_eq_mk },
  repeat { rw prod.mk.inj_iff },
  exact sym2.eq_iff,
end

instance : fintype (darts G) :=
by { dunfold darts, apply_instance }

lemma dart_to_edge_prop (e : edge_set G) (d : darts G) (h : dart_to_edge G d = e) : dart_to_vert G d ∈ e.1 :=
by tidy

lemma dart_to_edge_surj : function.surjective (dart_to_edge G) :=
begin
  rintro ⟨e, he⟩,
  refine quotient.rec_on_subsingleton e (λ e he, _) he,
  rcases e with ⟨x, y⟩,
  rw mem_edge_set at he,
  exact ⟨⟨(x, y), he⟩, rfl⟩,
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
    rintros ⟨⟨x₁, y₁⟩, h₁⟩ hd₁ ⟨⟨x₂, y₂⟩, h₂⟩ hd₂ heq,
    dsimp [f, dart_reverse, dart_to_vert] at heq,
    rw [subtype.mk_eq_mk, prod.mk.inj_iff],
    simp only [dart_to_vert, true_and, mem_filter, mem_univ] at hd₁ hd₂,
    subst x₁, subst x₂, subst y₂, simp,
  },
  rw ←card_image_of_inj_on H,
  congr,
  ext w,
  simp only [mem_image, true_and, exists_prop, mem_filter, mem_univ, adj_as_adj'],
  split,
  { rintros ⟨⟨⟨x, y⟩, h⟩, hd, hw⟩,
    dsimp [dart_to_vert] at hd, subst v,
    dsimp [f, dart_reverse, dart_to_vert] at hw, subst w,
    exact h, },
  { intro a,
    use ⟨(v, w), a⟩, simp [dart_to_vert, f, dart_reverse], },
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
    use ⟨(v, w), hw⟩,
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

section bollobas

variables {α : Type*} [simple_graphs α] -- [∀ G : α, decidable_rel (adj G)]
open_locale classical

/-!
Some formalizations of statements from Bollobas, "Modern graph theory"
-/

/--
Veblen 1912 (theorem 1 in book). Every vertex has even degree iff there is a
partition of the graph into edge-disjoint cycles.
-/
theorem edge_partition_cycles (G : α) [fintype (V G)] :
  (∀ v : V G, degree v % 2 = 0) ↔ (∃ partition : set (subgraph G), (∀ G' ∈ partition, subgraph.is_cycle G') ∧
                                     ∀ (e ∈ edge_set G), !∃ (c : subgraph G), c ∈ partition ∧
                                       e ∈ c.edge_set') :=
sorry

/--
Mantel 1907 (theorem 2 in book). If a graph with n vertices and m edges satisfies
floor(n^2 /4) < m, then it contains a triangle.
-/
theorem has_triangle (G : α) [fintype (V G)] (h : (fintype.card (V G))^2 / 4 < (edge_finset G).card) :
  nonempty (cycle_graph 3 (by linarith) ↪g G) :=
sorry

end bollobas

end simple_graph
