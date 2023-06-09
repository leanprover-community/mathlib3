/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov, Hunter Monroe
-/
import data.rel
import data.set.finite
import data.sym.sym2

/-!
# Simple graphs

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module defines simple graphs on a vertex type `V` as an
irreflexive symmetric relation.

There is a basic API for locally finite graphs and for graphs with
finitely many vertices.

## Main definitions

* `simple_graph` is a structure for symmetric, irreflexive relations

* `simple_graph.neighbor_set` is the `set` of vertices adjacent to a given vertex

* `simple_graph.common_neighbors` is the intersection of the neighbor sets of two given vertices

* `simple_graph.neighbor_finset` is the `finset` of vertices adjacent to a given vertex,
   if `neighbor_set` is finite

* `simple_graph.incidence_set` is the `set` of edges containing a given vertex

* `simple_graph.incidence_finset` is the `finset` of edges containing a given vertex,
   if `incidence_set` is finite

* `simple_graph.dart` is an ordered pair of adjacent vertices, thought of as being an
  orientated edge. These are also known as "half-edges" or "bonds."

* `simple_graph.hom`, `simple_graph.embedding`, and `simple_graph.iso` for graph
  homomorphisms, graph embeddings, and
  graph isomorphisms. Note that a graph embedding is a stronger notion than an
  injective graph homomorphism, since its image is an induced subgraph.

* `complete_boolean_algebra` instance: Under the subgraph relation, `simple_graph` forms a
  `complete_boolean_algebra`. In other words, this is the complete lattice of spanning subgraphs of
  the complete graph.

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

* This is the simplest notion of an unoriented graph.  This should
  eventually fit into a more complete combinatorics hierarchy which
  includes multigraphs and directed graphs.  We begin with simple graphs
  in order to start learning what the combinatorics hierarchy should
  look like.
-/

open finset function

universes u v w

/--
A simple graph is an irreflexive symmetric relation `adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `simple_graph.edge_set` for the corresponding edge set.
-/
@[ext]
structure simple_graph (V : Type u) :=
(adj : V → V → Prop)
(symm : symmetric adj . obviously)
(loopless : irreflexive adj . obviously)

noncomputable instance {V : Type u} [fintype V] : fintype (simple_graph V) :=
by { classical, exact fintype.of_injective simple_graph.adj simple_graph.ext }

/--
Construct the simple graph induced by the given relation. It
symmetrizes the relation and makes it irreflexive.
-/
def simple_graph.from_rel {V : Type u} (r : V → V → Prop) : simple_graph V :=
{ adj := λ a b, (a ≠ b) ∧ (r a b ∨ r b a),
  symm := λ a b ⟨hn, hr⟩, ⟨hn.symm, hr.symm⟩,
  loopless := λ a ⟨hn, _⟩, hn rfl }

@[simp]
lemma simple_graph.from_rel_adj {V : Type u} (r : V → V → Prop) (v w : V) :
  (simple_graph.from_rel r).adj v w ↔ v ≠ w ∧ (r v w ∨ r w v) :=
iff.rfl

/-- The complete graph on a type `V` is the simple graph with all pairs of distinct vertices
adjacent. In `mathlib`, this is usually referred to as `⊤`. -/
def complete_graph (V : Type u) : simple_graph V := { adj := ne }

/-- The graph with no edges on a given vertex type `V`. `mathlib` prefers the notation `⊥`. -/
def empty_graph (V : Type u) : simple_graph V := { adj := λ i j, false }

/--
Two vertices are adjacent in the complete bipartite graph on two vertex types
if and only if they are not from the same side.
Bipartite graphs in general may be regarded as being subgraphs of one of these.

TODO also introduce complete multi-partite graphs, where the vertex type is a sigma type of an
indexed family of vertex types
-/
@[simps]
def complete_bipartite_graph (V W : Type*) : simple_graph (V ⊕ W) :=
{ adj := λ v w, (v.is_left ∧ w.is_right) ∨ (v.is_right ∧ w.is_left),
  symm := begin
    intros v w,
    cases v; cases w; simp,
  end,
  loopless := begin
    intro v,
    cases v; simp,
  end }

namespace simple_graph
variables {ι : Sort*} {𝕜 : Type*} {V : Type u} {W : Type v} {X : Type w} (G : simple_graph V)
  (G' : simple_graph W) {a b c u v w : V} {e : sym2 V}

@[simp] protected lemma irrefl {v : V} : ¬G.adj v v := G.loopless v

lemma adj_comm (u v : V) : G.adj u v ↔ G.adj v u := ⟨λ x, G.symm x, λ x, G.symm x⟩

@[symm] lemma adj_symm (h : G.adj u v) : G.adj v u := G.symm h

lemma adj.symm {G : simple_graph V} {u v : V} (h : G.adj u v) : G.adj v u := G.symm h

lemma ne_of_adj (h : G.adj a b) : a ≠ b := by { rintro rfl, exact G.irrefl h }

protected lemma adj.ne {G : simple_graph V} {a b : V} (h : G.adj a b) : a ≠ b := G.ne_of_adj h

protected lemma adj.ne' {G : simple_graph V} {a b : V} (h : G.adj a b) : b ≠ a := h.ne.symm

lemma ne_of_adj_of_not_adj {v w x : V} (h : G.adj v x) (hn : ¬ G.adj w x) : v ≠ w :=
λ h', hn (h' ▸ h)

lemma adj_injective : injective (adj : simple_graph V → V → V → Prop) :=
λ G H h, by { cases G, cases H, congr' }

@[simp] lemma adj_inj {G H : simple_graph V} : G.adj = H.adj ↔ G = H := adj_injective.eq_iff

section order

/-- The relation that one `simple_graph` is a subgraph of another.
Note that this should be spelled `≤`. -/
def is_subgraph (x y : simple_graph V) : Prop := ∀ ⦃v w : V⦄, x.adj v w → y.adj v w

instance : has_le (simple_graph V) := ⟨is_subgraph⟩

@[simp] lemma is_subgraph_eq_le : (is_subgraph : simple_graph V → simple_graph V → Prop) = (≤) :=
rfl

/-- The supremum of two graphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : has_sup (simple_graph V) := ⟨λ x y,
  { adj := x.adj ⊔ y.adj,
    symm := λ v w h, by rwa [pi.sup_apply, pi.sup_apply, x.adj_comm, y.adj_comm] }⟩

@[simp] lemma sup_adj (x y : simple_graph V) (v w : V) : (x ⊔ y).adj v w ↔ x.adj v w ∨ y.adj v w :=
iff.rfl

/-- The infimum of two graphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : has_inf (simple_graph V) := ⟨λ x y,
  { adj := x.adj ⊓ y.adj,
    symm := λ v w h, by rwa [pi.inf_apply, pi.inf_apply, x.adj_comm, y.adj_comm] }⟩

@[simp] lemma inf_adj (x y : simple_graph V) (v w : V) : (x ⊓ y).adj v w ↔ x.adj v w ∧ y.adj v w :=
iff.rfl

/--
We define `Gᶜ` to be the `simple_graph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent
(still ensuring that vertices are not adjacent to themselves).
-/
instance : has_compl (simple_graph V) := ⟨λ G,
  { adj := λ v w, v ≠ w ∧ ¬G.adj v w,
    symm := λ v w ⟨hne, _⟩, ⟨hne.symm, by rwa adj_comm⟩,
    loopless := λ v ⟨hne, _⟩, (hne rfl).elim }⟩

@[simp] lemma compl_adj (G : simple_graph V) (v w : V) : Gᶜ.adj v w ↔ v ≠ w ∧ ¬G.adj v w := iff.rfl

/-- The difference of two graphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
instance : has_sdiff (simple_graph V) := ⟨λ x y,
  { adj := x.adj \ y.adj,
    symm := λ v w h, by change x.adj w v ∧ ¬ y.adj w v; rwa [x.adj_comm, y.adj_comm] }⟩

@[simp] lemma sdiff_adj (x y : simple_graph V) (v w : V) :
  (x \ y).adj v w ↔ (x.adj v w ∧ ¬ y.adj v w) := iff.rfl

instance : has_Sup (simple_graph V) :=
⟨λ s, { adj := λ a b, ∃ G ∈ s, adj G a b,
        symm := λ a b, Exists₂.imp $ λ _ _, adj.symm,
        loopless := by { rintro a ⟨G, hG, ha⟩, exact ha.ne rfl } }⟩

instance : has_Inf (simple_graph V) :=
⟨λ s, { adj := λ a b, (∀ ⦃G⦄, G ∈ s → adj G a b) ∧ a ≠ b,
        symm := λ _ _, and.imp (forall₂_imp $ λ _ _, adj.symm) ne.symm,
        loopless := λ a h, h.2 rfl }⟩

@[simp] lemma Sup_adj {s : set (simple_graph V)} {a b : V} : (Sup s).adj a b ↔ ∃ G ∈ s, adj G a b :=
iff.rfl

@[simp] lemma Inf_adj {s : set (simple_graph V)} : (Inf s).adj a b ↔ (∀ G ∈ s, adj G a b) ∧ a ≠ b :=
iff.rfl

@[simp] lemma supr_adj {f : ι → simple_graph V} : (⨆ i, f i).adj a b ↔ ∃ i, (f i).adj a b :=
by simp [supr]

@[simp] lemma infi_adj {f : ι → simple_graph V} :
  (⨅ i, f i).adj a b ↔ (∀ i, (f i).adj a b) ∧ a ≠ b :=
by simp [infi]

lemma Inf_adj_of_nonempty {s : set (simple_graph V)} (hs : s.nonempty) :
  (Inf s).adj a b ↔ ∀ G ∈ s, adj G a b :=
Inf_adj.trans $ and_iff_left_of_imp $ by { obtain ⟨G, hG⟩ := hs, exact λ h, (h _ hG).ne }

lemma infi_adj_of_nonempty [nonempty ι] {f : ι → simple_graph V} :
  (⨅ i, f i).adj a b ↔ ∀ i, (f i).adj a b :=
by simp [infi, Inf_adj_of_nonempty (set.range_nonempty _)]

/-- For graphs `G`, `H`, `G ≤ H` iff `∀ a b, G.adj a b → H.adj a b`. -/
instance : distrib_lattice (simple_graph V) :=
{ le := λ G H, ∀ ⦃a b⦄, G.adj a b → H.adj a b,
  ..show distrib_lattice (simple_graph V),
    from adj_injective.distrib_lattice _ (λ _ _, rfl) (λ _ _, rfl) }

instance : complete_boolean_algebra (simple_graph V) :=
{ le := (≤),
  sup := (⊔),
  inf := (⊓),
  compl := has_compl.compl,
  sdiff := (\),
  top := complete_graph V,
  bot := empty_graph V,
  le_top := λ x v w h, x.ne_of_adj h,
  bot_le := λ x v w h, h.elim,
  sdiff_eq := λ x y, by { ext v w, refine ⟨λ h, ⟨h.1, ⟨_, h.2⟩⟩, λ h, ⟨h.1, h.2.2⟩⟩,
                          rintro rfl, exact x.irrefl h.1 },
  inf_compl_le_bot := λ a v w h, false.elim $ h.2.2 h.1,
  top_le_sup_compl := λ a v w ne, by { by_cases a.adj v w, exact or.inl h, exact or.inr ⟨ne, h⟩ },
  Sup := Sup,
  le_Sup := λ s G hG a b hab, ⟨G, hG, hab⟩,
  Sup_le := λ s G hG a b, by { rintro ⟨H, hH, hab⟩, exact hG _ hH hab },
  Inf := Inf,
  Inf_le := λ s G hG a b hab, hab.1 hG,
  le_Inf := λ s G hG a b hab, ⟨λ H hH, hG _ hH hab, hab.ne⟩,
  inf_Sup_le_supr_inf := λ G s a b hab, by simpa only [exists_prop, Sup_adj, and_imp,
    forall_exists_index, Inf_adj, supr_adj, inf_adj, ←exists_and_distrib_right,
    exists_and_distrib_left, and_assoc, and_self_right] using hab,
  infi_sup_le_sup_Inf := λ G s a b hab, begin
    simp only [sup_adj, Inf_adj, infi_adj] at ⊢ hab,
    have : (∀ G' ∈ s, adj G a b ∨ adj G' a b) ∧ a ≠ b :=
      (and_congr_left $ λ h, forall_congr $ λ H, _).1 hab,
    simpa [forall_or_distrib_left, or_and_distrib_right, and_iff_left_of_imp adj.ne] using this,
    exact and_iff_left h,
  end,
  ..simple_graph.distrib_lattice }

@[simp] lemma top_adj (v w : V) : (⊤ : simple_graph V).adj v w ↔ v ≠ w := iff.rfl

@[simp] lemma bot_adj (v w : V) : (⊥ : simple_graph V).adj v w ↔ false := iff.rfl

@[simp] lemma complete_graph_eq_top (V : Type u) : complete_graph V = ⊤ := rfl

@[simp] lemma empty_graph_eq_bot (V : Type u) : empty_graph V = ⊥ := rfl

@[simps] instance (V : Type u) : inhabited (simple_graph V) := ⟨⊥⟩

section decidable

variables (V) (H : simple_graph V) [decidable_rel G.adj] [decidable_rel H.adj]

instance bot.adj_decidable   : decidable_rel (⊥ : simple_graph V).adj := λ v w, decidable.false

instance sup.adj_decidable   : decidable_rel (G ⊔ H).adj := λ v w, or.decidable

instance inf.adj_decidable   : decidable_rel (G ⊓ H).adj := λ v w, and.decidable

instance sdiff.adj_decidable : decidable_rel (G \ H).adj := λ v w, and.decidable

variable [decidable_eq V]

instance top.adj_decidable   : decidable_rel (⊤ : simple_graph V).adj :=  λ v w, not.decidable

instance compl.adj_decidable : decidable_rel Gᶜ.adj := λ v w, and.decidable

end decidable

end order

/-- `G.support` is the set of vertices that form edges in `G`. -/
def support : set V := rel.dom G.adj

lemma mem_support {v : V} : v ∈ G.support ↔ ∃ w, G.adj v w := iff.rfl

lemma support_mono {G G' : simple_graph V} (h : G ≤ G') : G.support ⊆ G'.support :=
rel.dom_mono h

/-- `G.neighbor_set v` is the set of vertices adjacent to `v` in `G`. -/
def neighbor_set (v : V) : set V := set_of (G.adj v)

instance neighbor_set.mem_decidable (v : V) [decidable_rel G.adj] :
  decidable_pred (∈ G.neighbor_set v) := by { unfold neighbor_set, apply_instance }

section edge_set
variables {G₁ G₂ : simple_graph V}

/--
The edges of G consist of the unordered pairs of vertices related by
`G.adj`.

The way `edge_set` is defined is such that `mem_edge_set` is proved by `refl`.
(That is, `⟦(v, w)⟧ ∈ G.edge_set` is definitionally equal to `G.adj v w`.)
-/
def edge_set : simple_graph V ↪o set (sym2 V) :=
order_embedding.of_map_le_iff (λ G, sym2.from_rel G.symm) $
  λ G G', ⟨λ h a b, @h ⟦(a, b)⟧, λ h e, sym2.ind @h e⟩

@[simp] lemma mem_edge_set : ⟦(v, w)⟧ ∈ G.edge_set ↔ G.adj v w := iff.rfl

lemma not_is_diag_of_mem_edge_set : e ∈ G.edge_set → ¬ e.is_diag := sym2.ind (λ v w, adj.ne) e

@[simp] lemma edge_set_inj : G₁.edge_set = G₂.edge_set ↔ G₁ = G₂ :=
(edge_set : simple_graph V ↪o set (sym2 V)).eq_iff_eq

@[simp] lemma edge_set_subset_edge_set : G₁.edge_set ⊆ G₂.edge_set ↔ G₁ ≤ G₂ :=
(edge_set : simple_graph V ↪o set (sym2 V)).le_iff_le

@[simp] lemma edge_set_ssubset_edge_set : G₁.edge_set ⊂ G₂.edge_set ↔ G₁ < G₂ :=
(edge_set : simple_graph V ↪o set (sym2 V)).lt_iff_lt

lemma edge_set_injective : injective (edge_set : simple_graph V → set (sym2 V)) :=
edge_set.injective

alias edge_set_subset_edge_set ↔ _ edge_set_mono
alias edge_set_ssubset_edge_set ↔ _ edge_set_strict_mono

attribute [mono] edge_set_mono edge_set_strict_mono

variables (G₁ G₂)

@[simp] lemma edge_set_bot : (⊥ : simple_graph V).edge_set = ∅ := sym2.from_rel_bot

@[simp] lemma edge_set_sup : (G₁ ⊔ G₂).edge_set = G₁.edge_set ∪ G₂.edge_set :=
by { ext ⟨x, y⟩, refl }

@[simp] lemma edge_set_inf : (G₁ ⊓ G₂).edge_set = G₁.edge_set ∩ G₂.edge_set :=
by { ext ⟨x, y⟩, refl }

@[simp] lemma edge_set_sdiff : (G₁ \ G₂).edge_set = G₁.edge_set \ G₂.edge_set :=
by { ext ⟨x, y⟩, refl }

/--
This lemma, combined with `edge_set_sdiff` and `edge_set_from_edge_set`,
allows proving `(G \ from_edge_set s).edge_set = G.edge_set \ s` by `simp`.
-/
@[simp] lemma edge_set_sdiff_sdiff_is_diag (G : simple_graph V) (s : set (sym2 V)) :
  G.edge_set \ (s \ {e | e.is_diag}) = G.edge_set \ s :=
begin
  ext e,
  simp only [set.mem_diff, set.mem_set_of_eq, not_and, not_not, and.congr_right_iff],
  intro h,
  simp only [G.not_is_diag_of_mem_edge_set h, imp_false],
end

/--
Two vertices are adjacent iff there is an edge between them. The
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
    rw sym2.mem_and_mem_iff hne at hv,
    subst e,
    rwa mem_edge_set at he }
end

lemma adj_iff_exists_edge_coe : G.adj a b ↔ ∃ (e : G.edge_set), ↑e = ⟦(a, b)⟧ :=
by simp only [mem_edge_set, exists_prop, set_coe.exists, exists_eq_right, subtype.coe_mk]

lemma edge_other_ne {e : sym2 V} (he : e ∈ G.edge_set) {v : V} (h : v ∈ e) : h.other ≠ v :=
begin
  erw [← sym2.other_spec h, sym2.eq_swap] at he,
  exact G.ne_of_adj he,
end

instance decidable_mem_edge_set [decidable_rel G.adj] :
  decidable_pred (∈ G.edge_set) := sym2.from_rel.decidable_pred _

instance fintype_edge_set [decidable_eq V] [fintype V] [decidable_rel G.adj] :
  fintype G.edge_set := subtype.fintype _

instance fintype_edge_set_bot : fintype (⊥ : simple_graph V).edge_set :=
by { rw edge_set_bot, apply_instance }

instance fintype_edge_set_sup [decidable_eq V] [fintype G₁.edge_set] [fintype G₂.edge_set] :
  fintype (G₁ ⊔ G₂).edge_set :=
by { rw edge_set_sup, apply_instance }

instance fintype_edge_set_inf [decidable_eq V] [fintype G₁.edge_set] [fintype G₂.edge_set] :
  fintype (G₁ ⊓ G₂).edge_set :=
by { rw edge_set_inf, exact set.fintype_inter _ _ }

instance fintype_edge_set_sdiff [decidable_eq V] [fintype G₁.edge_set] [fintype G₂.edge_set] :
  fintype (G₁ \ G₂).edge_set :=
by { rw edge_set_sdiff, exact set.fintype_diff _ _  }

end edge_set

section from_edge_set

variable (s : set (sym2 V))

/--
`from_edge_set` constructs a `simple_graph` from a set of edges, without loops.
-/
def from_edge_set : simple_graph V :=
{ adj := sym2.to_rel s ⊓ ne,
  symm := λ v w h, ⟨sym2.to_rel_symmetric s h.1, h.2.symm⟩}

@[simp] lemma from_edge_set_adj : (from_edge_set s).adj v w ↔ ⟦(v, w)⟧ ∈ s ∧ v ≠ w := iff.rfl

-- Note: we need to make sure `from_edge_set_adj` and this lemma are confluent.
-- In particular, both yield `⟦(u, v)⟧ ∈ (from_edge_set s).edge_set` ==> `⟦(v, w)⟧ ∈ s ∧ v ≠ w`.
@[simp] lemma edge_set_from_edge_set : (from_edge_set s).edge_set = s \ {e | e.is_diag} :=
by { ext e, exact sym2.ind (by simp) e }

@[simp] lemma from_edge_set_edge_set : from_edge_set G.edge_set = G :=
by { ext v w, exact ⟨λ h, h.1, λ h, ⟨h, G.ne_of_adj h⟩⟩ }

@[simp] lemma from_edge_set_empty : from_edge_set (∅ : set (sym2 V)) = ⊥ :=
by { ext v w, simp only [from_edge_set_adj, set.mem_empty_iff_false, false_and, bot_adj] }

@[simp] lemma from_edge_set_univ : from_edge_set (set.univ : set (sym2 V)) = ⊤ :=
by { ext v w, simp only [from_edge_set_adj, set.mem_univ, true_and, top_adj] }

@[simp] lemma from_edge_set_inf (s t : set (sym2 V)) :
  from_edge_set s ⊓ from_edge_set t = from_edge_set (s ∩ t) :=
by { ext v w, simp only [from_edge_set_adj, set.mem_inter_iff, ne.def, inf_adj], tauto, }

@[simp] lemma from_edge_set_sup (s t : set (sym2 V)) :
  from_edge_set s ⊔ from_edge_set t = from_edge_set (s ∪ t) :=
by { ext v w, simp [set.mem_union, or_and_distrib_right], }

@[simp] lemma from_edge_set_sdiff (s t : set (sym2 V)) :
  from_edge_set s \ from_edge_set t = from_edge_set (s \ t) :=
by { ext v w, split; simp { contextual := tt }, }

@[mono]
lemma from_edge_set_mono {s t : set (sym2 V)} (h : s ⊆ t) : from_edge_set s ≤ from_edge_set t :=
begin
  rintro v w,
  simp only [from_edge_set_adj, ne.def, not_false_iff, and_true, and_imp] {contextual := tt},
  exact λ vws _, h vws,
end

instance [decidable_eq V] [fintype s] : fintype (from_edge_set s).edge_set :=
by { rw edge_set_from_edge_set s, apply_instance }

end from_edge_set

/-! ## Darts -/

/-- A `dart` is an oriented edge, implemented as an ordered pair of adjacent vertices.
This terminology comes from combinatorial maps, and they are also known as "half-edges"
or "bonds." -/
@[ext, derive decidable_eq]
structure dart extends V × V :=
(is_adj : G.adj fst snd)

section darts
variables {G}

/-- The first vertex for the dart. -/
abbreviation dart.fst (d : G.dart) : V := d.fst

/-- The second vertex for the dart. -/
abbreviation dart.snd (d : G.dart) : V := d.snd

lemma dart.to_prod_injective : function.injective (dart.to_prod : G.dart → V × V) := dart.ext

instance dart.fintype [fintype V] [decidable_rel G.adj] : fintype G.dart :=
fintype.of_equiv (Σ v, G.neighbor_set v)
{ to_fun := λ s, ⟨(s.fst, s.snd), s.snd.property⟩,
  inv_fun := λ d, ⟨d.fst, d.snd, d.is_adj⟩,
  left_inv := λ s, by ext; simp,
  right_inv := λ d, by ext; simp }

/-- The edge associated to the dart. -/
def dart.edge (d : G.dart) : sym2 V := ⟦d.to_prod⟧

@[simp] lemma dart.edge_mk {p : V × V} (h : G.adj p.1 p.2) :
  (dart.mk p h).edge = ⟦p⟧ := rfl

@[simp] lemma dart.edge_mem (d : G.dart) : d.edge ∈ G.edge_set :=
d.is_adj

/-- The dart with reversed orientation from a given dart. -/
@[simps] def dart.symm (d : G.dart) : G.dart :=
⟨d.to_prod.swap, G.symm d.is_adj⟩

@[simp] lemma dart.symm_mk {p : V × V} (h : G.adj p.1 p.2) :
  (dart.mk p h).symm = dart.mk p.swap h.symm := rfl

@[simp] lemma dart.edge_symm (d : G.dart) : d.symm.edge = d.edge :=
sym2.mk_prod_swap_eq

@[simp] lemma dart.edge_comp_symm : dart.edge ∘ dart.symm = (dart.edge : G.dart → sym2 V) :=
funext dart.edge_symm

@[simp] lemma dart.symm_symm (d : G.dart) : d.symm.symm = d :=
dart.ext _ _ $ prod.swap_swap _

@[simp] lemma dart.symm_involutive : function.involutive (dart.symm : G.dart → G.dart) :=
dart.symm_symm

lemma dart.symm_ne (d : G.dart) : d.symm ≠ d :=
ne_of_apply_ne (prod.snd ∘ dart.to_prod) d.is_adj.ne

lemma dart_edge_eq_iff : Π (d₁ d₂ : G.dart),
  d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.symm :=
by { rintros ⟨p, hp⟩ ⟨q, hq⟩, simp [sym2.mk_eq_mk_iff] }

lemma dart_edge_eq_mk_iff : Π {d : G.dart} {p : V × V},
  d.edge = ⟦p⟧ ↔ d.to_prod = p ∨ d.to_prod = p.swap :=
by { rintro ⟨p, h⟩, apply sym2.mk_eq_mk_iff }

lemma dart_edge_eq_mk_iff' : Π {d : G.dart} {u v : V},
  d.edge = ⟦(u, v)⟧ ↔ d.fst = u ∧ d.snd = v ∨ d.fst = v ∧ d.snd = u :=
by { rintro ⟨⟨a, b⟩, h⟩ u v, rw dart_edge_eq_mk_iff, simp }

variables (G)

/-- Two darts are said to be adjacent if they could be consecutive
darts in a walk -- that is, the first dart's second vertex is equal to
the second dart's first vertex. -/
def dart_adj (d d' : G.dart) : Prop := d.snd = d'.fst

/-- For a given vertex `v`, this is the bijective map from the neighbor set at `v`
to the darts `d` with `d.fst = v`. -/
@[simps] def dart_of_neighbor_set (v : V) (w : G.neighbor_set v) : G.dart :=
⟨(v, w), w.property⟩

lemma dart_of_neighbor_set_injective (v : V) : function.injective (G.dart_of_neighbor_set v) :=
λ e₁ e₂ h, subtype.ext $ by { injection h with h', convert congr_arg prod.snd h' }

instance nonempty_dart_top [nontrivial V] : nonempty (⊤ : simple_graph V).dart :=
by { obtain ⟨v, w, h⟩ := exists_pair_ne V, exact ⟨⟨(v, w), h⟩⟩ }

end darts

/-! ### Incidence set -/

/-- Set of edges incident to a given vertex, aka incidence set. -/
def incidence_set (v : V) : set (sym2 V) := {e ∈ G.edge_set | v ∈ e}

lemma incidence_set_subset (v : V) : G.incidence_set v ⊆ G.edge_set := λ _ h, h.1

lemma mk_mem_incidence_set_iff : ⟦(b, c)⟧ ∈ G.incidence_set a ↔ G.adj b c ∧ (a = b ∨ a = c) :=
and_congr_right' sym2.mem_iff

lemma mk_mem_incidence_set_left_iff : ⟦(a, b)⟧ ∈ G.incidence_set a ↔ G.adj a b :=
and_iff_left $ sym2.mem_mk_left _ _

lemma mk_mem_incidence_set_right_iff : ⟦(a, b)⟧ ∈ G.incidence_set b ↔ G.adj a b :=
and_iff_left $ sym2.mem_mk_right _ _

lemma edge_mem_incidence_set_iff {e : G.edge_set} : ↑e ∈ G.incidence_set a ↔ a ∈ (e : sym2 V) :=
and_iff_right e.2

lemma incidence_set_inter_incidence_set_subset (h : a ≠ b) :
  G.incidence_set a ∩ G.incidence_set b ⊆ {⟦(a, b)⟧} :=
λ e he, (sym2.mem_and_mem_iff h).1 ⟨he.1.2, he.2.2⟩

lemma incidence_set_inter_incidence_set_of_adj (h : G.adj a b) :
  G.incidence_set a ∩ G.incidence_set b = {⟦(a, b)⟧} :=
begin
  refine (G.incidence_set_inter_incidence_set_subset $ h.ne).antisymm _,
  rintro _ (rfl : _ = ⟦(a, b)⟧),
  exact ⟨G.mk_mem_incidence_set_left_iff.2 h, G.mk_mem_incidence_set_right_iff.2 h⟩,
end

lemma adj_of_mem_incidence_set (h : a ≠ b) (ha : e ∈ G.incidence_set a)
  (hb : e ∈ G.incidence_set b) :
  G.adj a b :=
by rwa [←mk_mem_incidence_set_left_iff,
  ←set.mem_singleton_iff.1 $ G.incidence_set_inter_incidence_set_subset h ⟨ha, hb⟩]

lemma incidence_set_inter_incidence_set_of_not_adj (h : ¬ G.adj a b) (hn : a ≠ b) :
  G.incidence_set a ∩ G.incidence_set b = ∅ :=
begin
  simp_rw [set.eq_empty_iff_forall_not_mem, set.mem_inter_iff, not_and],
  intros u ha hb,
  exact h (G.adj_of_mem_incidence_set hn ha hb),
end

instance decidable_mem_incidence_set [decidable_eq V] [decidable_rel G.adj] (v : V) :
  decidable_pred (∈ G.incidence_set v) := λ e, and.decidable

section edge_finset
variables {G₁ G₂ : simple_graph V} [fintype G.edge_set] [fintype G₁.edge_set] [fintype G₂.edge_set]

/--
The `edge_set` of the graph as a `finset`.
-/
@[reducible] def edge_finset : finset (sym2 V) := set.to_finset G.edge_set

@[simp, norm_cast] lemma coe_edge_finset : (G.edge_finset : set (sym2 V)) = G.edge_set :=
set.coe_to_finset _

variables {G}

@[simp] lemma mem_edge_finset : e ∈ G.edge_finset ↔ e ∈ G.edge_set := set.mem_to_finset

lemma not_is_diag_of_mem_edge_finset : e ∈ G.edge_finset → ¬ e.is_diag :=
not_is_diag_of_mem_edge_set _ ∘ mem_edge_finset.1

@[simp] lemma edge_finset_inj : G₁.edge_finset = G₂.edge_finset ↔ G₁ = G₂ := by simp [edge_finset]

@[simp] lemma edge_finset_subset_edge_finset : G₁.edge_finset ⊆ G₂.edge_finset ↔ G₁ ≤ G₂ :=
by simp [edge_finset]

@[simp] lemma edge_finset_ssubset_edge_finset : G₁.edge_finset ⊂ G₂.edge_finset ↔ G₁ < G₂ :=
by simp [edge_finset]

alias edge_finset_subset_edge_finset ↔ _ edge_finset_mono
alias edge_finset_ssubset_edge_finset ↔ _ edge_finset_strict_mono

attribute [mono] edge_finset_mono edge_finset_strict_mono

@[simp] lemma edge_finset_bot : (⊥ : simple_graph V).edge_finset = ∅ := by simp [edge_finset]

@[simp] lemma edge_finset_sup [decidable_eq V] :
  (G₁ ⊔ G₂).edge_finset = G₁.edge_finset ∪ G₂.edge_finset :=
by simp [edge_finset]

@[simp] lemma edge_finset_inf [decidable_eq V] :
  (G₁ ⊓ G₂).edge_finset = G₁.edge_finset ∩ G₂.edge_finset :=
by simp [edge_finset]

@[simp] lemma edge_finset_sdiff [decidable_eq V] :
  (G₁ \ G₂).edge_finset = G₁.edge_finset \ G₂.edge_finset :=
by simp [edge_finset]

lemma edge_finset_card : G.edge_finset.card = fintype.card G.edge_set := set.to_finset_card _

@[simp] lemma edge_set_univ_card : (univ : finset G.edge_set).card = G.edge_finset.card :=
fintype.card_of_subtype G.edge_finset $ λ _, mem_edge_finset

end edge_finset

@[simp] lemma mem_neighbor_set (v w : V) : w ∈ G.neighbor_set v ↔ G.adj v w :=
iff.rfl

@[simp] lemma mem_incidence_set (v w : V) : ⟦(v, w)⟧ ∈ G.incidence_set v ↔ G.adj v w :=
by simp [incidence_set]

lemma mem_incidence_iff_neighbor {v w : V} : ⟦(v, w)⟧ ∈ G.incidence_set v ↔ w ∈ G.neighbor_set v :=
by simp only [mem_incidence_set, mem_neighbor_set]

lemma adj_incidence_set_inter {v : V} {e : sym2 V} (he : e ∈ G.edge_set) (h : v ∈ e) :
  G.incidence_set v ∩ G.incidence_set h.other = {e} :=
begin
  ext e',
  simp only [incidence_set, set.mem_sep_iff, set.mem_inter_iff, set.mem_singleton_iff],
  refine ⟨λ h', _, _⟩,
  { rw ←sym2.other_spec h,
    exact (sym2.mem_and_mem_iff (edge_other_ne G he h).symm).mp ⟨h'.1.2, h'.2.2⟩ },
  { rintro rfl,
    exact ⟨⟨he, h⟩, he, sym2.other_mem _⟩ }
end

lemma compl_neighbor_set_disjoint (G : simple_graph V) (v : V) :
  disjoint (G.neighbor_set v) (Gᶜ.neighbor_set v) :=
begin
  rw set.disjoint_iff,
  rintro w ⟨h, h'⟩,
  rw [mem_neighbor_set, compl_adj] at h',
  exact h'.2 h,
end

lemma neighbor_set_union_compl_neighbor_set_eq (G : simple_graph V) (v : V) :
  G.neighbor_set v ∪ Gᶜ.neighbor_set v = {v}ᶜ :=
begin
  ext w,
  have h := @ne_of_adj _ G,
  simp_rw [set.mem_union, mem_neighbor_set, compl_adj, set.mem_compl_iff, set.mem_singleton_iff],
  tauto,
end

-- TODO find out why TC inference has `h` failing a defeq check for `to_finset`
lemma card_neighbor_set_union_compl_neighbor_set [fintype V] (G : simple_graph V)
  (v : V) [h : fintype (G.neighbor_set v ∪ Gᶜ.neighbor_set v : set V)] :
  (@set.to_finset _ (G.neighbor_set v ∪ Gᶜ.neighbor_set v) h).card = fintype.card V - 1 :=
begin
  classical,
  simp_rw [neighbor_set_union_compl_neighbor_set_eq, set.to_finset_compl, finset.card_compl,
    set.to_finset_card, set.card_singleton],
end

lemma neighbor_set_compl (G : simple_graph V) (v : V) :
  Gᶜ.neighbor_set v = (G.neighbor_set v)ᶜ \ {v} :=
by { ext w, simp [and_comm, eq_comm] }

/--
The set of common neighbors between two vertices `v` and `w` in a graph `G` is the
intersection of the neighbor sets of `v` and `w`.
-/
def common_neighbors (v w : V) : set V := G.neighbor_set v ∩ G.neighbor_set w

lemma common_neighbors_eq (v w : V) :
  G.common_neighbors v w = G.neighbor_set v ∩ G.neighbor_set w := rfl

lemma mem_common_neighbors {u v w : V} : u ∈ G.common_neighbors v w ↔ G.adj v u ∧ G.adj w u :=
iff.rfl

lemma common_neighbors_symm (v w : V) : G.common_neighbors v w = G.common_neighbors w v :=
set.inter_comm _ _

lemma not_mem_common_neighbors_left (v w : V) : v ∉ G.common_neighbors v w :=
λ h, ne_of_adj G h.1 rfl

lemma not_mem_common_neighbors_right (v w : V) : w ∉ G.common_neighbors v w :=
λ h, ne_of_adj G h.2 rfl

lemma common_neighbors_subset_neighbor_set_left (v w : V) :
  G.common_neighbors v w ⊆ G.neighbor_set v :=
set.inter_subset_left _ _

lemma common_neighbors_subset_neighbor_set_right (v w : V) :
  G.common_neighbors v w ⊆ G.neighbor_set w :=
set.inter_subset_right _ _

instance decidable_mem_common_neighbors [decidable_rel G.adj] (v w : V) :
  decidable_pred (∈ G.common_neighbors v w) :=
λ a, and.decidable

lemma common_neighbors_top_eq {v w : V} :
  (⊤ : simple_graph V).common_neighbors v w = set.univ \ {v, w} :=
by { ext u, simp [common_neighbors, eq_comm, not_or_distrib.symm] }

section incidence
variable [decidable_eq V]

/--
Given an edge incident to a particular vertex, get the other vertex on the edge.
-/
def other_vertex_of_incident {v : V} {e : sym2 V} (h : e ∈ G.incidence_set v) : V := h.2.other'

lemma edge_other_incident_set {v : V} {e : sym2 V} (h : e ∈ G.incidence_set v) :
  e ∈ G.incidence_set (G.other_vertex_of_incident h) :=
by { use h.1, simp [other_vertex_of_incident, sym2.other_mem'] }

lemma incidence_other_prop {v : V} {e : sym2 V} (h : e ∈ G.incidence_set v) :
  G.other_vertex_of_incident h ∈ G.neighbor_set v :=
by { cases h with he hv, rwa [←sym2.other_spec' hv, mem_edge_set] at he }

@[simp]
lemma incidence_other_neighbor_edge {v w : V} (h : w ∈ G.neighbor_set v) :
  G.other_vertex_of_incident (G.mem_incidence_iff_neighbor.mpr h) = w :=
sym2.congr_right.mp (sym2.other_spec' (G.mem_incidence_iff_neighbor.mpr h).right)

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

/-! ## Edge deletion -/

/-- Given a set of vertex pairs, remove all of the corresponding edges from the
graph's edge set, if present.

See also: `simple_graph.subgraph.delete_edges`. -/
def delete_edges (s : set (sym2 V)) : simple_graph V :=
{ adj := G.adj \ sym2.to_rel s,
  symm := λ a b, by simp [adj_comm, sym2.eq_swap] }

@[simp] lemma delete_edges_adj (s : set (sym2 V)) (v w : V) :
  (G.delete_edges s).adj v w ↔ G.adj v w ∧ ¬ ⟦(v, w)⟧ ∈ s := iff.rfl

lemma sdiff_eq_delete_edges (G G' : simple_graph V) :
  G \ G' = G.delete_edges G'.edge_set :=
by { ext, simp }

lemma delete_edges_eq_sdiff_from_edge_set (s : set (sym2 V)) :
  G.delete_edges s = G \ from_edge_set s :=
by { ext, exact ⟨λ h, ⟨h.1, not_and_of_not_left _ h.2⟩, λ h, ⟨h.1, not_and'.mp h.2 h.ne⟩⟩ }

lemma compl_eq_delete_edges :
  Gᶜ = (⊤ : simple_graph V).delete_edges G.edge_set :=
by { ext, simp }

@[simp] lemma delete_edges_delete_edges (s s' : set (sym2 V)) :
  (G.delete_edges s).delete_edges s' = G.delete_edges (s ∪ s') :=
by { ext, simp [and_assoc, not_or_distrib] }

@[simp] lemma delete_edges_empty_eq : G.delete_edges ∅ = G :=
by { ext, simp }

@[simp] lemma delete_edges_univ_eq : G.delete_edges set.univ = ⊥ :=
by { ext, simp }

lemma delete_edges_le (s : set (sym2 V)) : G.delete_edges s ≤ G :=
by { intro, simp { contextual := tt } }

lemma delete_edges_le_of_le {s s' : set (sym2 V)} (h : s ⊆ s') :
  G.delete_edges s' ≤ G.delete_edges s :=
λ v w, begin
  simp only [delete_edges_adj, and_imp, true_and] { contextual := tt },
  exact λ ha hn hs, hn (h hs),
end

lemma delete_edges_eq_inter_edge_set (s : set (sym2 V)) :
  G.delete_edges s = G.delete_edges (s ∩ G.edge_set) :=
by { ext, simp [imp_false] { contextual := tt } }

lemma delete_edges_sdiff_eq_of_le {H : simple_graph V} (h : H ≤ G) :
  G.delete_edges (G.edge_set \ H.edge_set) = H :=
by { ext v w, split; simp [@h v w] { contextual := tt } }

lemma edge_set_delete_edges (s : set (sym2 V)) :
  (G.delete_edges s).edge_set = G.edge_set \ s :=
by { ext e, refine sym2.ind _ e, simp }

lemma edge_finset_delete_edges [fintype V] [decidable_eq V] [decidable_rel G.adj]
  (s : finset (sym2 V)) [decidable_rel (G.delete_edges s).adj] :
  (G.delete_edges s).edge_finset = G.edge_finset \ s :=
by { ext e, simp [edge_set_delete_edges] }

section delete_far
variables (G) [ordered_ring 𝕜] [fintype V] [decidable_eq V] [decidable_rel G.adj]
  {p : simple_graph V → Prop} {r r₁ r₂ : 𝕜}

/-- A graph is `r`-*delete-far* from a property `p` if we must delete at least `r` edges from it to
get a graph with the property `p`. -/
def delete_far (p : simple_graph V → Prop) (r : 𝕜) : Prop :=
∀ ⦃s⦄, s ⊆ G.edge_finset → p (G.delete_edges s) → r ≤ s.card

open_locale classical

variables {G}

lemma delete_far_iff :
  G.delete_far p r ↔ ∀ ⦃H⦄, H ≤ G → p H → r ≤ G.edge_finset.card - H.edge_finset.card :=
begin
  refine ⟨λ h H hHG hH, _, λ h s hs hG, _⟩,
  { have := h (sdiff_subset G.edge_finset H.edge_finset),
    simp only [delete_edges_sdiff_eq_of_le _ hHG, edge_finset_mono hHG, card_sdiff,
      card_le_of_subset, coe_sdiff, coe_edge_finset, nat.cast_sub] at this,
    exact this hH },
  { simpa [card_sdiff hs, edge_finset_delete_edges, -set.to_finset_card, nat.cast_sub,
      card_le_of_subset hs] using h (G.delete_edges_le s) hG }
end

alias delete_far_iff ↔ delete_far.le_card_sub_card _

lemma delete_far.mono (h : G.delete_far p r₂) (hr : r₁ ≤ r₂) : G.delete_far p r₁ :=
λ s hs hG, hr.trans $ h hs hG

end delete_far

/-! ## Map and comap -/

/-- Given an injective function, there is an covariant induced map on graphs by pushing forward
the adjacency relation.

This is injective (see `simple_graph.map_injective`). -/
protected def map (f : V ↪ W) (G : simple_graph V) : simple_graph W :=
{ adj := relation.map G.adj f f }

@[simp] lemma map_adj (f : V ↪ W) (G : simple_graph V) (u v : W) :
  (G.map f).adj u v ↔ ∃ (u' v' : V), G.adj u' v' ∧ f u' = u ∧ f v' = v := iff.rfl

lemma map_monotone (f : V ↪ W) : monotone (simple_graph.map f) :=
by { rintros G G' h _ _ ⟨u, v, ha, rfl, rfl⟩, exact ⟨_, _, h ha, rfl, rfl⟩ }

/-- Given a function, there is a contravariant induced map on graphs by pulling back the
adjacency relation.
This is one of the ways of creating induced graphs. See `simple_graph.induce` for a wrapper.

This is surjective when `f` is injective (see `simple_graph.comap_surjective`).-/
@[simps] protected def comap (f : V → W) (G : simple_graph W) : simple_graph V :=
{ adj := λ u v, G.adj (f u) (f v) }

lemma comap_monotone (f : V ↪ W) : monotone (simple_graph.comap f) :=
by { intros G G' h _ _ ha, exact h ha }

@[simp] lemma comap_map_eq (f : V ↪ W) (G : simple_graph V) : (G.map f).comap f = G :=
by { ext, simp }

lemma left_inverse_comap_map (f : V ↪ W) :
  function.left_inverse (simple_graph.comap f) (simple_graph.map f) := comap_map_eq f

lemma map_injective (f : V ↪ W) : function.injective (simple_graph.map f) :=
(left_inverse_comap_map f).injective

lemma comap_surjective (f : V ↪ W) : function.surjective (simple_graph.comap f) :=
(left_inverse_comap_map f).surjective

lemma map_le_iff_le_comap (f : V ↪ W) (G : simple_graph V) (G' : simple_graph W) :
  G.map f ≤ G' ↔ G ≤ G'.comap f :=
⟨λ h u v ha, h ⟨_, _, ha, rfl, rfl⟩, by { rintros h _ _ ⟨u, v, ha, rfl, rfl⟩, exact h ha, }⟩

lemma map_comap_le (f : V ↪ W) (G : simple_graph W) : (G.comap f).map f ≤ G :=
by { rw map_le_iff_le_comap, exact le_refl _ }

/-! ## Induced graphs -/

/- Given a set `s` of vertices, we can restrict a graph to those vertices by restricting its
adjacency relation. This gives a map between `simple_graph V` and `simple_graph s`.

There is also a notion of induced subgraphs (see `simple_graph.subgraph.induce`). -/

/-- Restrict a graph to the vertices in the set `s`, deleting all edges incident to vertices
outside the set. This is a wrapper around `simple_graph.comap`. -/
@[reducible] def induce (s : set V) (G : simple_graph V) : simple_graph s :=
G.comap (function.embedding.subtype _)

/-- Given a graph on a set of vertices, we can make it be a `simple_graph V` by
adding in the remaining vertices without adding in any additional edges.
This is a wrapper around `simple_graph.map`. -/
@[reducible] def spanning_coe {s : set V} (G : simple_graph s) : simple_graph V :=
G.map (function.embedding.subtype _)

lemma induce_spanning_coe {s : set V} {G : simple_graph s} : G.spanning_coe.induce s = G :=
comap_map_eq _ _

lemma spanning_coe_induce_le (s : set V) : (G.induce s).spanning_coe ≤ G :=
map_comap_le _ _

section finite_at

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote this condition by
`fintype (G.neighbor_set v)`.

We define `G.neighbor_finset v` to be the `finset` version of `G.neighbor_set v`.
Use `neighbor_finset_eq_filter` to rewrite this definition as a `filter`.
-/

variables (v) [fintype (G.neighbor_set v)]
/--
`G.neighbors v` is the `finset` version of `G.adj v` in case `G` is
locally finite at `v`.
-/
def neighbor_finset : finset V := (G.neighbor_set v).to_finset

lemma neighbor_finset_def : G.neighbor_finset v = (G.neighbor_set v).to_finset := rfl

@[simp] lemma mem_neighbor_finset (w : V) :
  w ∈ G.neighbor_finset v ↔ G.adj v w :=
set.mem_to_finset

@[simp] lemma not_mem_neighbor_finset_self : v ∉ G.neighbor_finset v :=
(mem_neighbor_finset _ _ _).not.mpr $ G.loopless _

lemma neighbor_finset_disjoint_singleton : disjoint (G.neighbor_finset v) {v} :=
finset.disjoint_singleton_right.mpr $ not_mem_neighbor_finset_self _ _

lemma singleton_disjoint_neighbor_finset : disjoint {v} (G.neighbor_finset v) :=
finset.disjoint_singleton_left.mpr $ not_mem_neighbor_finset_self _ _

/--
`G.degree v` is the number of vertices adjacent to `v`.
-/
def degree : ℕ := (G.neighbor_finset v).card

@[simp]
lemma card_neighbor_set_eq_degree : fintype.card (G.neighbor_set v) = G.degree v :=
(set.to_finset_card _).symm

lemma degree_pos_iff_exists_adj : 0 < G.degree v ↔ ∃ w, G.adj v w :=
by simp only [degree, card_pos, finset.nonempty, mem_neighbor_finset]

lemma degree_compl [fintype (Gᶜ.neighbor_set v)] [fintype V] :
  Gᶜ.degree v = fintype.card V - 1 - G.degree v :=
begin
  classical,
  rw [← card_neighbor_set_union_compl_neighbor_set G v, set.to_finset_union],
  simp [card_disjoint_union (set.disjoint_to_finset.mpr (compl_neighbor_set_disjoint G v))],
end

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
lemma card_incidence_finset_eq_degree [decidable_eq V] :
  (G.incidence_finset v).card = G.degree v :=
by { rw ← G.card_incidence_set_eq_degree, apply set.to_finset_card }

@[simp]
lemma mem_incidence_finset [decidable_eq V] (e : sym2 V) :
  e ∈ G.incidence_finset v ↔ e ∈ G.incidence_set v :=
set.mem_to_finset

lemma incidence_finset_eq_filter [decidable_eq V] [fintype G.edge_set] :
  G.incidence_finset v = G.edge_finset.filter (has_mem.mem v) :=
begin
  ext e,
  refine sym2.ind (λ x y, _) e,
  simp [mk_mem_incidence_set_iff],
end

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

variables {G}

lemma is_regular_of_degree.degree_eq {d : ℕ} (h : G.is_regular_of_degree d) (v : V) :
  G.degree v = d := h v

lemma is_regular_of_degree.compl [fintype V] [decidable_eq V]
  {G : simple_graph V} [decidable_rel G.adj]
  {k : ℕ} (h : G.is_regular_of_degree k) :
  Gᶜ.is_regular_of_degree (fintype.card V - 1 - k) :=
by { intro v, rw [degree_compl, h v] }

end locally_finite

section finite

variable [fintype V]

instance neighbor_set_fintype [decidable_rel G.adj] (v : V) : fintype (G.neighbor_set v) :=
@subtype.fintype _ _ (by { simp_rw mem_neighbor_set, apply_instance }) _

lemma neighbor_finset_eq_filter {v : V} [decidable_rel G.adj] :
  G.neighbor_finset v = finset.univ.filter (G.adj v) :=
by { ext, simp }

lemma neighbor_finset_compl [decidable_eq V] [decidable_rel G.adj] (v : V) :
  Gᶜ.neighbor_finset v = (G.neighbor_finset v)ᶜ \ {v} :=
by simp only [neighbor_finset, neighbor_set_compl, set.to_finset_diff, set.to_finset_compl,
    set.to_finset_singleton]

@[simp]
lemma complete_graph_degree [decidable_eq V] (v : V) :
  (⊤ : simple_graph V).degree v = fintype.card V - 1 :=
by erw [degree, neighbor_finset_eq_filter, filter_ne, card_erase_of_mem (mem_univ v), card_univ]

lemma bot_degree (v : V) : (⊥ : simple_graph V).degree v = 0 :=
begin
  erw [degree, neighbor_finset_eq_filter, filter_false],
  exact finset.card_empty,
end

lemma is_regular_of_degree.top [decidable_eq V] :
  (⊤ : simple_graph V).is_regular_of_degree (fintype.card V - 1) :=
by { intro v, simp }

/--
The minimum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_minimal_degree_vertex`, `min_degree_le_degree`
and `le_min_degree_of_forall_le_degree`.
-/
def min_degree [decidable_rel G.adj] : ℕ :=
with_top.untop' 0 (univ.image (λ v, G.degree v)).min

/--
There exists a vertex of minimal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex.
-/
lemma exists_minimal_degree_vertex [decidable_rel G.adj] [nonempty V] :
  ∃ v, G.min_degree = G.degree v :=
begin
  obtain ⟨t, ht : _ = _⟩ := min_of_nonempty (univ_nonempty.image (λ v, G.degree v)),
  obtain ⟨v, _, rfl⟩ := mem_image.mp (mem_of_min ht),
  refine ⟨v, by simp [min_degree, ht]⟩,
end

/-- The minimum degree in the graph is at most the degree of any particular vertex. -/
lemma min_degree_le_degree [decidable_rel G.adj] (v : V) : G.min_degree ≤ G.degree v :=
begin
  obtain ⟨t, ht⟩ := finset.min_of_mem (mem_image_of_mem (λ v, G.degree v) (mem_univ v)),
  have := finset.min_le_of_eq (mem_image_of_mem _ (mem_univ v)) ht,
  rwa [min_degree, ht]
end

/--
In a nonempty graph, if `k` is at most the degree of every vertex, it is at most the minimum
degree. Note the assumption that the graph is nonempty is necessary as long as `G.min_degree` is
defined to be a natural.
-/
lemma le_min_degree_of_forall_le_degree [decidable_rel G.adj] [nonempty V] (k : ℕ)
  (h : ∀ v, k ≤ G.degree v) :
  k ≤ G.min_degree :=
by { rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩, rw hv, apply h }

/--
The maximum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_maximal_degree_vertex`, `degree_le_max_degree`
and `max_degree_le_of_forall_degree_le`.
-/
def max_degree [decidable_rel G.adj] : ℕ :=
option.get_or_else (univ.image (λ v, G.degree v)).max 0

/--
There exists a vertex of maximal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex.
-/
lemma exists_maximal_degree_vertex [decidable_rel G.adj] [nonempty V] :
  ∃ v, G.max_degree = G.degree v :=
begin
  obtain ⟨t, ht⟩ := max_of_nonempty (univ_nonempty.image (λ v, G.degree v)),
  have ht₂ := mem_of_max ht,
  simp only [mem_image, mem_univ, exists_prop_of_true] at ht₂,
  rcases ht₂ with ⟨v, rfl⟩,
  refine ⟨v, _⟩,
  rw [max_degree, ht],
  refl
end

/-- The maximum degree in the graph is at least the degree of any particular vertex. -/
lemma degree_le_max_degree [decidable_rel G.adj] (v : V) : G.degree v ≤ G.max_degree :=
begin
  obtain ⟨t, ht : _ = _⟩ := finset.max_of_mem (mem_image_of_mem (λ v, G.degree v) (mem_univ v)),
  have := finset.le_max_of_eq (mem_image_of_mem _ (mem_univ v)) ht,
  rwa [max_degree, ht],
end

/--
In a graph, if `k` is at least the degree of every vertex, then it is at least the maximum
degree.
-/
lemma max_degree_le_of_forall_degree_le [decidable_rel G.adj] (k : ℕ)
  (h : ∀ v, G.degree v ≤ k) :
  G.max_degree ≤ k :=
begin
  by_cases hV : (univ : finset V).nonempty,
  { haveI : nonempty V := univ_nonempty_iff.mp hV,
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex,
    rw hv,
    apply h },
  { rw not_nonempty_iff_eq_empty at hV,
    rw [max_degree, hV, image_empty],
    exact zero_le k },
end

lemma degree_lt_card_verts [decidable_rel G.adj] (v : V) : G.degree v < fintype.card V :=
begin
  classical,
  apply finset.card_lt_card,
  rw finset.ssubset_iff,
  exact ⟨v, by simp, finset.subset_univ _⟩,
end

/--
The maximum degree of a nonempty graph is less than the number of vertices. Note that the assumption
that `V` is nonempty is necessary, as otherwise this would assert the existence of a
natural number less than zero.
-/
lemma max_degree_lt_card_verts [decidable_rel G.adj] [nonempty V] : G.max_degree < fintype.card V :=
begin
  cases G.exists_maximal_degree_vertex with v hv,
  rw hv,
  apply G.degree_lt_card_verts v,
end

lemma card_common_neighbors_le_degree_left [decidable_rel G.adj] (v w : V) :
  fintype.card (G.common_neighbors v w) ≤ G.degree v :=
begin
  rw [←card_neighbor_set_eq_degree],
  exact set.card_le_of_subset (set.inter_subset_left _ _),
end

lemma card_common_neighbors_le_degree_right [decidable_rel G.adj] (v w : V) :
  fintype.card (G.common_neighbors v w) ≤ G.degree w :=
by simp_rw [common_neighbors_symm _ v w, card_common_neighbors_le_degree_left]

lemma card_common_neighbors_lt_card_verts [decidable_rel G.adj] (v w : V) :
  fintype.card (G.common_neighbors v w) < fintype.card V :=
nat.lt_of_le_of_lt (G.card_common_neighbors_le_degree_left _ _) (G.degree_lt_card_verts v)

/--
If the condition `G.adj v w` fails, then `card_common_neighbors_le_degree` is
the best we can do in general.
-/
lemma adj.card_common_neighbors_lt_degree {G : simple_graph V} [decidable_rel G.adj]
  {v w : V} (h : G.adj v w) :
  fintype.card (G.common_neighbors v w) < G.degree v :=
begin
  classical,
  erw [←set.to_finset_card],
  apply finset.card_lt_card,
  rw finset.ssubset_iff,
  use w,
  split,
  { rw set.mem_to_finset,
    apply not_mem_common_neighbors_right },
  { rw finset.insert_subset,
    split,
    { simpa, },
    { rw [neighbor_finset, set.to_finset_subset_to_finset],
      exact G.common_neighbors_subset_neighbor_set_left _ _ } }
end

lemma card_common_neighbors_top [decidable_eq V] {v w : V} (h : v ≠ w) :
  fintype.card ((⊤ : simple_graph V).common_neighbors v w) = fintype.card V - 2 :=
begin
  simp only [common_neighbors_top_eq, ← set.to_finset_card, set.to_finset_diff],
  rw finset.card_sdiff,
  { simp [finset.card_univ, h], },
  { simp only [set.to_finset_subset_to_finset, set.subset_univ] },
end

end finite

section maps

/--
A graph homomorphism is a map on vertex sets that respects adjacency relations.

The notation `G →g G'` represents the type of graph homomorphisms.
-/
abbreviation hom := rel_hom G.adj G'.adj

/--
A graph embedding is an embedding `f` such that for vertices `v w : V`,
`G.adj f(v) f(w) ↔ G.adj v w `. Its image is an induced subgraph of G'.

The notation `G ↪g G'` represents the type of graph embeddings.
-/
abbreviation embedding := rel_embedding G.adj G'.adj

/--
A graph isomorphism is an bijective map on vertex sets that respects adjacency relations.

The notation `G ≃g G'` represents the type of graph isomorphisms.
-/
abbreviation iso := rel_iso G.adj G'.adj

infix ` →g ` : 50 := hom
infix ` ↪g ` : 50 := embedding
infix ` ≃g ` : 50 := iso

namespace hom
variables {G G'} (f : G →g G')

/-- The identity homomorphism from a graph to itself. -/
abbreviation id : G →g G := rel_hom.id _

lemma map_adj {v w : V} (h : G.adj v w) : G'.adj (f v) (f w) := f.map_rel' h

lemma map_mem_edge_set {e : sym2 V} (h : e ∈ G.edge_set) : e.map f ∈ G'.edge_set :=
quotient.ind (λ e h, sym2.from_rel_prop.mpr (f.map_rel' h)) e h

lemma apply_mem_neighbor_set {v w : V} (h : w ∈ G.neighbor_set v) : f w ∈ G'.neighbor_set (f v) :=
map_adj f h

/-- The map between edge sets induced by a homomorphism.
The underlying map on edges is given by `sym2.map`. -/
@[simps] def map_edge_set (e : G.edge_set) : G'.edge_set :=
⟨sym2.map f e, f.map_mem_edge_set e.property⟩

/-- The map between neighbor sets induced by a homomorphism. -/
@[simps] def map_neighbor_set (v : V) (w : G.neighbor_set v) : G'.neighbor_set (f v) :=
⟨f w, f.apply_mem_neighbor_set w.property⟩

/-- The map between darts induced by a homomorphism. -/
def map_dart (d : G.dart) : G'.dart := ⟨d.1.map f f, f.map_adj d.2⟩

@[simp] lemma map_dart_apply (d : G.dart) : f.map_dart d = ⟨d.1.map f f, f.map_adj d.2⟩ := rfl

/-- The induced map for spanning subgraphs, which is the identity on vertices. -/
@[simps]
def map_spanning_subgraphs {G G' : simple_graph V} (h : G ≤ G') : G →g G' :=
{ to_fun := λ x, x,
  map_rel' := h }

lemma map_edge_set.injective (hinj : function.injective f) : function.injective f.map_edge_set :=
begin
  rintros ⟨e₁, h₁⟩ ⟨e₂, h₂⟩,
  dsimp [hom.map_edge_set],
  repeat { rw subtype.mk_eq_mk },
  apply sym2.map.injective hinj,
end

/-- Every graph homomomorphism from a complete graph is injective. -/
lemma injective_of_top_hom (f : (⊤ : simple_graph V) →g G') : function.injective f :=
begin
  intros v w h,
  contrapose! h,
  exact G'.ne_of_adj (map_adj _ ((top_adj _ _).mpr h)),
end

/-- There is a homomorphism to a graph from a comapped graph.
When the function is injective, this is an embedding (see `simple_graph.embedding.comap`). -/
@[simps] protected def comap (f : V → W) (G : simple_graph W) : G.comap f →g G :=
{ to_fun := f,
  map_rel' := by simp }

variable {G'' : simple_graph X}

/-- Composition of graph homomorphisms. -/
abbreviation comp (f' : G' →g G'') (f : G →g G') : G →g G'' := f'.comp f

@[simp] lemma coe_comp (f' : G' →g G'') (f : G →g G') : ⇑(f'.comp f) = f' ∘ f := rfl

end hom

namespace embedding
variables {G G'} (f : G ↪g G')

/-- The identity embedding from a graph to itself. -/
abbreviation refl : G ↪g G := rel_embedding.refl _

/-- An embedding of graphs gives rise to a homomorphism of graphs. -/
abbreviation to_hom : G →g G' := f.to_rel_hom

lemma map_adj_iff {v w : V} : G'.adj (f v) (f w) ↔ G.adj v w := f.map_rel_iff

lemma map_mem_edge_set_iff {e : sym2 V} : e.map f ∈ G'.edge_set ↔ e ∈ G.edge_set :=
quotient.ind (λ ⟨v, w⟩, f.map_adj_iff) e

lemma apply_mem_neighbor_set_iff {v w : V} : f w ∈ G'.neighbor_set (f v) ↔ w ∈ G.neighbor_set v :=
map_adj_iff f

/-- A graph embedding induces an embedding of edge sets. -/
@[simps] def map_edge_set : G.edge_set ↪ G'.edge_set :=
{ to_fun := hom.map_edge_set f,
  inj' := hom.map_edge_set.injective f f.inj' }

/-- A graph embedding induces an embedding of neighbor sets. -/
@[simps] def map_neighbor_set (v : V) : G.neighbor_set v ↪ G'.neighbor_set (f v) :=
{ to_fun := λ w, ⟨f w, f.apply_mem_neighbor_set_iff.mpr w.2⟩,
  inj' := begin
    rintros ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h,
    rw subtype.mk_eq_mk at h ⊢,
    exact f.inj' h,
  end }

/-- Given an injective function, there is an embedding from the comapped graph into the original
graph. -/
@[simps]
protected def comap (f : V ↪ W) (G : simple_graph W) : G.comap f ↪g G :=
{ map_rel_iff' := by simp, ..f }

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
@[simps]
protected def map (f : V ↪ W) (G : simple_graph V) : G ↪g G.map f :=
{ map_rel_iff' := by simp, ..f }

/-- Induced graphs embed in the original graph.

Note that if `G.induce s = ⊤` (i.e., if `s` is a clique) then this gives the embedding of a
complete graph. -/
@[reducible] protected def induce (s : set V) : G.induce s ↪g G :=
simple_graph.embedding.comap (function.embedding.subtype _) G

/-- Graphs on a set of vertices embed in their `spanning_coe`. -/
@[reducible] protected def spanning_coe {s : set V} (G : simple_graph s) : G ↪g G.spanning_coe :=
simple_graph.embedding.map (function.embedding.subtype _) G

/-- Embeddings of types induce embeddings of complete graphs on those types. -/
protected def complete_graph {α β : Type*} (f : α ↪ β) :
  (⊤ : simple_graph α) ↪g (⊤ : simple_graph β) :=
{ map_rel_iff' := by simp, ..f }

variables {G'' : simple_graph X}

/-- Composition of graph embeddings. -/
abbreviation comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' := f.trans f'

@[simp] lemma coe_comp (f' : G' ↪g G'') (f : G ↪g G') : ⇑(f'.comp f) = f' ∘ f := rfl

end embedding

section induce_hom

variables {G G'} {G'' : simple_graph X} {s : set V} {t : set W} {r : set X}
          (φ : G →g G') (φst : set.maps_to φ s t) (ψ : G' →g G'') (ψtr : set.maps_to ψ t r)

/-- The restriction of a morphism of graphs to induced subgraphs. -/
def induce_hom : G.induce s →g G'.induce t :=
{ to_fun := set.maps_to.restrict φ s t φst,
  map_rel' := λ _ _,  φ.map_rel', }

@[simp, norm_cast] lemma coe_induce_hom : ⇑(induce_hom φ φst) = set.maps_to.restrict φ s t φst :=
rfl

@[simp] lemma induce_hom_id (G : simple_graph V) (s) :
  induce_hom (hom.id : G →g G) (set.maps_to_id s) = hom.id :=
by { ext x, refl }

@[simp] lemma induce_hom_comp :
  (induce_hom ψ ψtr).comp (induce_hom φ φst) = induce_hom (ψ.comp φ) (ψtr.comp φst) :=
by { ext x, refl }

end induce_hom

namespace iso
variables {G G'} (f : G ≃g G')

/-- The identity isomorphism of a graph with itself. -/
abbreviation refl : G ≃g G := rel_iso.refl _

/-- An isomorphism of graphs gives rise to an embedding of graphs. -/
abbreviation to_embedding : G ↪g G' := f.to_rel_embedding

/-- An isomorphism of graphs gives rise to a homomorphism of graphs. -/
abbreviation to_hom : G →g G' := f.to_embedding.to_hom

/-- The inverse of a graph isomorphism. -/
abbreviation symm : G' ≃g G := f.symm

lemma map_adj_iff {v w : V} : G'.adj (f v) (f w) ↔ G.adj v w := f.map_rel_iff

lemma map_mem_edge_set_iff {e : sym2 V} : e.map f ∈ G'.edge_set ↔ e ∈ G.edge_set :=
quotient.ind (λ ⟨v, w⟩, f.map_adj_iff) e

lemma apply_mem_neighbor_set_iff {v w : V} : f w ∈ G'.neighbor_set (f v) ↔ w ∈ G.neighbor_set v :=
map_adj_iff f

/-- An isomorphism of graphs induces an equivalence of edge sets. -/
@[simps] def map_edge_set : G.edge_set ≃ G'.edge_set :=
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

/-- A graph isomorphism induces an equivalence of neighbor sets. -/
@[simps] def map_neighbor_set (v : V) : G.neighbor_set v ≃ G'.neighbor_set (f v) :=
{ to_fun := λ w, ⟨f w, f.apply_mem_neighbor_set_iff.mpr w.2⟩,
  inv_fun := λ w, ⟨f.symm w, begin
    convert f.symm.apply_mem_neighbor_set_iff.mpr w.2,
    simp only [rel_iso.symm_apply_apply],
  end⟩,
  left_inv := λ w, by simp,
  right_inv := λ w, by simp }

lemma card_eq_of_iso [fintype V] [fintype W] (f : G ≃g G') : fintype.card V = fintype.card W :=
by convert (fintype.of_equiv_card f.to_equiv).symm

/-- Given a bijection, there is an embedding from the comapped graph into the original
graph. -/
@[simps] protected def comap (f : V ≃ W) (G : simple_graph W) : G.comap f.to_embedding ≃g G :=
{ map_rel_iff' := by simp, ..f }

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
@[simps] protected def map (f : V ≃ W) (G : simple_graph V) : G ≃g G.map f.to_embedding :=
{ map_rel_iff' := by simp, ..f }

/-- Equivalences of types induce isomorphisms of complete graphs on those types. -/
protected def complete_graph {α β : Type*} (f : α ≃ β) :
  (⊤ : simple_graph α) ≃g (⊤ : simple_graph β) :=
{ map_rel_iff' := by simp, ..f }

lemma to_embedding_complete_graph {α β : Type*} (f : α ≃ β) :
  (iso.complete_graph f).to_embedding = embedding.complete_graph f.to_embedding := rfl

variables {G'' : simple_graph X}

/-- Composition of graph isomorphisms. -/
abbreviation comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' := f.trans f'

@[simp] lemma coe_comp (f' : G' ≃g G'') (f : G ≃g G') : ⇑(f'.comp f) = f' ∘ f := rfl

end iso

end maps

end simple_graph
