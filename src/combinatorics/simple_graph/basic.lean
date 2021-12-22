/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov, Hunter Monroe
-/
import data.rel
import data.set.finite
import data.sym.sym2
import combinatorics.graph

/-!
# Simple graphs

This module defines simple graphs on a vertex type `V` as an
irreflexive symmetric relation.

There is a basic API for locally finite graphs and for graphs with
finitely many vertices.

## Main definitions

* `simple_graph` is a structure for symmetric, irreflexive relations

* `neighbor_set` is the `set` of vertices adjacent to a given vertex

* `common_neighbors` is the intersection of the neighbor sets of two given vertices

* `neighbor_finset` is the `finset` of vertices adjacent to a given vertex,
   if `neighbor_set` is finite

* `incidence_set` is the `set` of edges containing a given vertex

* `homo`, `embedding`, and `iso` for graph homomorphisms, graph embeddings, and
  graph isomorphisms. Note that a graph embedding is a stronger notion than an
  injective graph homomorphism, since its image is an induced subgraph.

* `boolean_algebra` instance: Under the subgraph relation, `simple_graph` forms a `boolean_algebra`.
  In other words, this is the lattice of spanning subgraphs of the complete graph.

## Notations

* `→g`, `↪g`, and `≃g` for graph homomorphisms, graph embeddings, and graph isomorphisms,
  respectively.

## Implementation notes

* A locally finite graph is one with instances `Π v, fintype (G.neighbor_set v)`.

* Given instances `decidable_rel G.adj` and `fintype V`, then the graph
  is locally finite, too.

* Morphisms of graphs are abbreviations for `rel_hom`, `rel_embedding`, and `rel_iso`.
  To make use of pre-existing simp lemmas, definitions involving morphisms are
  abbreviations as well.

## Naming Conventions

* If the vertex type of a graph is finite, we refer to its cardinality as `card_verts`.

## Todo

* Upgrade `simple_graph.boolean_algebra` to a `complete_boolean_algebra`.

* This is the simplest notion of an unoriented graph.  This should
  eventually fit into a more complete combinatorics hierarchy which
  includes multigraphs and directed graphs.  We begin with simple graphs
  in order to start learning what the combinatorics hierarchy should
  look like.
-/
open finset graph
universes u v w

/--
A simple graph is an irreflexive symmetric relation `adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent edges;
see `simple_graph.edge_set` for the corresponding edge set.
-/
@[ext]
structure simple_graph (V : Type u) :=
(adj' : V → V → Prop)
(symm : symmetric adj' . obviously)
(loopless : irreflexive adj' . obviously)

instance simple_graph.has_simple_undirected_edges {V} (G : simple_graph V) :
  has_simple_undirected_edges G V :=
graph.default_simple_undirected_edges G G.adj' G.symm

instance simple_graph.is_adj_symmetric {V} (G : simple_graph V) : is_adj_symmetric G V := ⟨G.symm⟩
instance simple_graph.is_adj_loopless {V} (G : simple_graph V) : is_adj_loopless G V := ⟨G.loopless⟩

/--
Construct the simple graph induced by the given relation. It
symmetrizes the relation and makes it irreflexive.
-/
def simple_graph.from_rel {V : Type u} (r : V → V → Prop) : simple_graph V :=
{ adj' := λ a b, (a ≠ b) ∧ (r a b ∨ r b a),
  symm := λ a b ⟨hn, hr⟩, ⟨hn.symm, hr.symm⟩,
  loopless := λ a ⟨hn, _⟩, hn rfl }

noncomputable instance {V : Type u} [fintype V] : fintype (simple_graph V) :=
by { classical, exact fintype.of_injective simple_graph.adj' simple_graph.ext }

@[simp]
lemma simple_graph.from_rel_adj {V : Type u} (r : V → V → Prop) (v w : V) :
  adj (simple_graph.from_rel r) v w ↔ v ≠ w ∧ (r v w ∨ r w v) :=
iff.rfl

/-- The complete graph on a type `V` is the simple graph with all pairs of distinct vertices
adjacent. In `mathlib`, this is usually referred to as `⊤`. -/
def complete_graph (V : Type u) : simple_graph V := { adj' := ne }

/-- The graph with no edges on a given vertex type `V`. `mathlib` prefers the notation `⊥`. -/
def empty_graph (V : Type u) : simple_graph V := { adj' := λ i j, false }

/--
Two vertices are adjacent in the complete bipartite graph on two vertex types
if and only if they are not from the same side.
Bipartite graphs in general may be regarded as being subgraphs of one of these.

TODO also introduce complete multi-partite graphs, where the vertex type is a sigma type of an
indexed family of vertex types
-/
@[simps]
def complete_bipartite_graph (V W : Type*) : simple_graph (V ⊕ W) :=
{ adj' := λ v w, (v.is_left ∧ w.is_right) ∨ (v.is_right ∧ w.is_left),
  symm := begin
    intros v w,
    cases v; cases w; simp,
  end,
  loopless := begin
    intro v,
    cases v; simp,
  end }

namespace simple_graph

variables {V : Type u} {W : Type v} {X : Type w} (G : simple_graph V) (G' : simple_graph W)
  {a b c u v w : V} {e : sym2 V}

section order

/-- The relation that one `simple_graph` is a subgraph of another.
Note that this should be spelled `≤`. -/
def is_subgraph (x y : simple_graph V) : Prop := ∀ ⦃v w : V⦄, adj x v w → adj y v w

instance : has_le (simple_graph V) := ⟨is_subgraph⟩

@[simp] lemma is_subgraph_eq_le : (is_subgraph : simple_graph V → simple_graph V → Prop) = (≤) :=
rfl

/-- The supremum of two graphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : has_sup (simple_graph V) := ⟨λ x y,
  { adj' := adj x ⊔ adj y,
    symm := λ v w h, by rwa [pi.sup_apply, pi.sup_apply, adj_comm x, adj_comm y] }⟩

@[simp] lemma sup_adj (x y : simple_graph V) (v w : V) : adj (x ⊔ y) v w ↔ adj x v w ∨ adj y v w :=
iff.rfl

/-- The infimum of two graphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : has_inf (simple_graph V) := ⟨λ x y,
  { adj' := adj x ⊓ adj y,
    symm := λ v w h, by rwa [pi.inf_apply, pi.inf_apply, adj_comm x, adj_comm y] }⟩

@[simp] lemma inf_adj (x y : simple_graph V) (v w : V) : adj (x ⊓ y) v w ↔ adj x v w ∧ adj y v w :=
iff.rfl

/--
We define `Gᶜ` to be the `simple_graph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent
(still ensuring that vertices are not adjacent to themselves).
-/
instance : has_compl (simple_graph V) := ⟨λ G,
  { adj' := λ v w, v ≠ w ∧ ¬adj G v w,
    symm := λ v w ⟨hne, _⟩, ⟨hne.symm, by rwa adj_comm⟩,
    loopless := λ v ⟨hne, _⟩, (hne rfl).elim }⟩

@[simp] lemma compl_adj (G : simple_graph V) (v w : V) : adj Gᶜ v w ↔ v ≠ w ∧ ¬adj G v w := iff.rfl

/-- The difference of two graphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
instance : has_sdiff (simple_graph V) := ⟨λ x y,
  { adj' := adj x \ adj y,
    symm := λ v w h, by change adj x w v ∧ ¬ adj y w v; rwa [adj_comm x, adj_comm y] }⟩

@[simp] lemma sdiff_adj (x y : simple_graph V) (v w : V) :
  adj (x \ y) v w ↔ (adj x v w ∧ ¬ adj y v w) := iff.rfl

instance : boolean_algebra (simple_graph V) :=
{ le := (≤),
  sup := (⊔),
  inf := (⊓),
  compl := has_compl.compl,
  sdiff := (\),
  top := complete_graph V,
  bot := empty_graph V,
  le_top := λ x v w h, ne_of_adj x h,
  bot_le := λ x v w h, h.elim,
  sup_le := λ x y z hxy hyz v w h, h.cases_on (λ h, hxy h) (λ h, hyz h),
  sdiff_eq := λ x y, by { ext v w, refine ⟨λ h, ⟨h.1, ⟨_, h.2⟩⟩, λ h, ⟨h.1, h.2.2⟩⟩,
                          rintro rfl, exact adj_irrefl x h.1 },
  sup_inf_sdiff := λ a b, by { ext v w, refine ⟨λ h, _, λ h', _⟩,
                               obtain ⟨ha, _⟩|⟨ha, _⟩ := h; exact ha,
                               by_cases adj b v w; exact or.inl ⟨h', h⟩ <|> exact or.inr ⟨h', h⟩ },
  inf_inf_sdiff := λ a b, by { ext v w, exact ⟨λ ⟨⟨_, hb⟩,⟨_, hb'⟩⟩, hb' hb, λ h, h.elim⟩ },
  le_sup_left := λ x y v w h, or.inl h,
  le_sup_right := λ x y v w h, or.inr h,
  le_inf := λ x y z hxy hyz v w h, ⟨hxy h, hyz h⟩,
  le_sup_inf := λ a b c v w h, or.dcases_on h.2 or.inl $
    or.dcases_on h.1 (λ h _, or.inl h) $ λ hb hc, or.inr ⟨hb, hc⟩,
  inf_compl_le_bot := λ a v w h, false.elim $ h.2.2 h.1,
  top_le_sup_compl := λ a v w ne, by { by_cases adj a v w, exact or.inl h, exact or.inr ⟨ne, h⟩ },
  inf_le_left := λ x y v w h, h.1,
  inf_le_right := λ x y v w h, h.2,
  .. partial_order.lift adj' ext }

@[simp] lemma top_adj (v w : V) : adj (⊤ : simple_graph V) v w ↔ v ≠ w := iff.rfl

@[simp] lemma bot_adj (v w : V) : adj (⊥ : simple_graph V) v w ↔ false := iff.rfl

@[simp] lemma complete_graph_eq_top (V : Type u) : complete_graph V = ⊤ := rfl

@[simp] lemma empty_graph_eq_bot (V : Type u) : empty_graph V = ⊥ := rfl

instance (V : Type u) : inhabited (simple_graph V) := ⟨⊤⟩

section decidable

variables (V) (H : simple_graph V) [hg : decidable_rel (adj G)] [hh : decidable_rel (adj H)]

instance bot.adj_decidable   : decidable_rel (adj (⊥ : simple_graph V)) := λ v w, decidable.false

instance sup.adj_decidable   : decidable_rel (adj (G ⊔ H)) :=
λ v w, @or.decidable _ _ (hg v w) (hh v w)

instance inf.adj_decidable   : decidable_rel (adj (G ⊓ H)) :=
λ v w, @and.decidable _ _ (hg v w) (hh v w)

instance sdiff.adj_decidable : decidable_rel (adj (G \ H)) :=
λ v w, @and.decidable _ _ (hg v w) (@not.decidable _ (hh v w))

variable [decidable_eq V]

instance top.adj_decidable   : decidable_rel (adj (⊤ : simple_graph V)) :=  λ v w, not.decidable

instance compl.adj_decidable : decidable_rel (adj Gᶜ) :=
λ v w, @and.decidable _ _ _ (@not.decidable _ (hg v w))

end decidable

end order

lemma support_mono {G G' : simple_graph V} (h : G ≤ G') : support G ⊆ support G' :=
rel.dom_mono h

/-! ### Incidence set -/


lemma mk_mem_incidence_set_iff : ⟦(b, c)⟧ ∈ incidence_set G a ↔ adj G b c ∧ (a = b ∨ a = c) :=
and_congr_right' sym2.mem_iff

lemma mk_mem_incidence_set_left_iff : ⟦(a, b)⟧ ∈ incidence_set G a ↔ adj G a b :=
and_iff_left $ sym2.mem_mk_left _ _

lemma mk_mem_incidence_set_right_iff : ⟦(a, b)⟧ ∈ incidence_set G b ↔ adj G a b :=
and_iff_left $ sym2.mem_mk_right _ _

lemma edge_mem_incidence_set_iff {e : edge_set G} :
  (e : sym2 V) ∈ incidence_set G a ↔ a ∈ (e : sym2 V) :=
and_iff_right e.2

lemma incidence_set_inter_incidence_set_subset (h : a ≠ b) :
  incidence_set G a ∩ incidence_set G b ⊆ {⟦(a, b)⟧} :=
λ e he, (sym2.mem_and_mem_iff h).1 ⟨he.1.2, he.2.2⟩

lemma incidence_set_inter_incidence_set (h : adj G a b) :
  incidence_set G a ∩ incidence_set G b = {⟦(a, b)⟧} :=
begin
  refine (G.incidence_set_inter_incidence_set_subset $ h.ne).antisymm _,
  rintro _ (rfl : _ = ⟦(a, b)⟧),
  exact ⟨G.mk_mem_incidence_set_left_iff.2 h, G.mk_mem_incidence_set_right_iff.2 h⟩,
end

lemma adj_of_mem_incidence_set (h : a ≠ b) (ha : e ∈ incidence_set G a)
  (hb : e ∈ incidence_set G b) :
  adj G a b :=
by rwa [←mk_mem_incidence_set_left_iff,
  ←set.mem_singleton_iff.1 $ G.incidence_set_inter_incidence_set_subset h ⟨ha, hb⟩]

@[simp] lemma mem_incidence_set (v w : V) : ⟦(v, w)⟧ ∈ incidence_set G v ↔ adj G v w :=
and_iff_left $ sym2.mem_mk_left _ _

lemma mem_incidence_iff_neighbor {v w : V} : ⟦(v, w)⟧ ∈ incidence_set G v ↔ w ∈ neighbor_set G v :=
by simp only [mem_incidence_set, mem_neighbor_set]

lemma adj_incidence_set_inter {v : V} {e : sym2 V} (he : e ∈ edge_set G) (h : v ∈ e) :
  incidence_set G v ∩ incidence_set G h.other = {e} :=
begin
  ext e',
  simp only [set.mem_sep_eq, set.mem_inter_eq, set.mem_singleton_iff],
  refine ⟨λ h', _, _⟩,
  { rw ←sym2.other_spec h,
    exact (sym2.mem_and_mem_iff (edge_other_ne G he h).symm).mp ⟨h'.1.2, h'.2.2⟩ },
  { rintro rfl,
    exact ⟨⟨he, h⟩, he, sym2.other_mem _⟩ }
end

lemma compl_neighbor_set_disjoint (G : simple_graph V) (v : V) :
  disjoint (neighbor_set G v) (neighbor_set Gᶜ v) :=
begin
  rw set.disjoint_iff,
  rintro w ⟨h, h'⟩,
  rw [mem_neighbor_set, compl_adj] at h',
  exact h'.2 h,
end

lemma neighbor_set_union_compl_neighbor_set_eq (G : simple_graph V) (v : V) :
  neighbor_set G v ∪ neighbor_set Gᶜ v = {v}ᶜ :=
begin
  ext w,
  have h := @ne_of_adj _ G,
  simp_rw [set.mem_union, mem_neighbor_set, compl_adj, set.mem_compl_eq, set.mem_singleton_iff],
  tauto,
end

section incidence
variable [decidable_eq V]

@[simp]
lemma incidence_other_neighbor_edge {v w : V} (h : w ∈ neighbor_set G v) :
  other_vertex_of_incident G (G.mem_incidence_iff_neighbor.mpr h) = w :=
sym2.congr_right.mp (sym2.other_spec' (G.mem_incidence_iff_neighbor.mpr h).right)

/--
There is an equivalence between the set of edges incident to a given
vertex and the set of vertices adjacent to the vertex.
-/
@[simps] def incidence_set_equiv_neighbor_set (v : V) : incidence_set G v ≃ neighbor_set G v :=
{ to_fun := λ e, ⟨other_vertex_of_incident G e.2, incidence_other_prop G e.2⟩,
  inv_fun := λ w, ⟨⟦(v, w.1)⟧, G.mem_incidence_iff_neighbor.mpr w.2⟩,
  left_inv := λ x, begin
    cases x,
    simp only [other_vertex_of_incident, sym2.other_spec', subtype.mk_eq_mk],
    refl,
  end,
  right_inv := λ ⟨w, hw⟩, by simp }

end incidence

section finite_at

variables (v) [fintype (neighbor_set G v)]

instance incidence_set_fintype [decidable_eq V] : fintype (incidence_set G v) :=
fintype.of_equiv (neighbor_set G v) (incidence_set_equiv_neighbor_set G v).symm

@[simp]
lemma card_incidence_set_eq_degree [decidable_eq V] :
  fintype.card (incidence_set G v) = degree G v :=
by { rw fintype.card_congr (G.incidence_set_equiv_neighbor_set v), simp }

end finite_at

section finite

variable [fintype V]

@[simp]
lemma complete_graph_degree [decidable_eq V] (v : V) :
  degree (⊤ : simple_graph V) v = fintype.card V - 1 :=
begin
  convert univ.card.pred_eq_sub_one,
  erw [degree, neighbor_finset_eq_filter, filter_ne, card_erase_of_mem (mem_univ v)],
end

lemma complete_graph_is_regular [decidable_eq V] :
  is_regular_of_degree (⊤ : simple_graph V) (fintype.card V - 1) :=
by { intro v, simp }

end finite

section maps

namespace hom
variables {G G'} (f : G →g G')

lemma map_mem_edge_set {e : sym2 V} (h : e ∈ edge_set G) : e.map f ∈ edge_set G' :=
quotient.ind (λ e h, sym2.from_rel_prop.mpr (f.map_rel' h)) e h

/-- The map between edge sets induced by a homomorphism.
The underlying map on edges is given by `sym2.map`. -/
@[simps] def map_edge_set (e : edge_set G) : edge_set G' :=
⟨sym2.map f e, map_mem_edge_set f e.property⟩

/-- The induced map for spanning subgraphs, which is the identity on vertices. -/
def map_spanning_subgraphs {G G' : simple_graph V} (h : G ≤ G') : G →g G' :=
{ to_fun := λ x, x,
  map_rel' := h }

lemma map_edge_set.injective (hinj : function.injective f) : function.injective (map_edge_set f) :=
begin
  rintros ⟨e₁, h₁⟩ ⟨e₂, h₂⟩,
  dsimp [hom.map_edge_set],
  repeat { rw subtype.mk_eq_mk },
  apply sym2.map.injective hinj,
end

end hom

namespace embedding
variables {G G'} (f : G ↪g G')

lemma map_mem_edge_set_iff {e : sym2 V} : e.map f ∈ edge_set G' ↔ e ∈ edge_set G :=
quotient.ind (λ ⟨v, w⟩, f.map_adj_iff) e


/-- A graph embedding induces an embedding of edge sets. -/
@[simps] def map_edge_set : edge_set G ↪ edge_set G' :=
{ to_fun := hom.map_edge_set f,
  inj' := hom.map_edge_set.injective f f.inj' }

/-- Embeddings of types induce embeddings of complete graphs on those types. -/
def complete_graph.of_embedding {α β : Type*} (f : α ↪ β) :
  (⊤ : simple_graph α) ↪g (⊤ : simple_graph β) :=
{ to_fun := f,
  inj' := f.inj',
  map_rel_iff' := by simp }

end embedding

namespace iso
variables {G G'} (f : G ≃g G')

lemma map_mem_edge_set_iff {e : sym2 V} : e.map f ∈ edge_set G' ↔ e ∈ edge_set G :=
quotient.ind (λ ⟨v, w⟩, f.map_adj_iff) e

/-- An isomorphism of graphs induces an equivalence of edge sets. -/
@[simps] def map_edge_set : edge_set G ≃ edge_set G' :=
{ to_fun := hom.map_edge_set f,
  inv_fun := hom.map_edge_set f.symm,
  left_inv := begin
    rintro ⟨e, h⟩,
    simp only [hom.map_edge_set, sym2.map_map, rel_iso.coe_coe_fn,
      rel_embedding.coe_coe_fn, subtype.mk_eq_mk, subtype.coe_mk, coe_coe],
    apply congr_fun,
    convert sym2.map_id,
    exact funext (λ _, rel_iso.symm_apply_apply _ _),
  end,
  right_inv := begin
    rintro ⟨e, h⟩,
    simp only [hom.map_edge_set, sym2.map_map, rel_iso.coe_coe_fn,
      rel_embedding.coe_coe_fn, subtype.mk_eq_mk, subtype.coe_mk, coe_coe],
    apply congr_fun,
    convert sym2.map_id,
    exact funext (λ _, rel_iso.apply_symm_apply _ _),
  end }

end iso

end maps

end simple_graph
