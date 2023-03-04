/-
Copyright (c) 2021 Hunter Monroe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hunter Monroe, Kyle Miller, Alena Gusakov
-/
import combinatorics.simple_graph.basic

/-!
# Subgraphs of a simple graph

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A subgraph of a simple graph consists of subsets of the graph's vertices and edges such that the
endpoints of each edge are present in the vertex subset. The edge subset is formalized as a
sub-relation of the adjacency relation of the simple graph.

## Main definitions

* `subgraph G` is the type of subgraphs of a `G : simple_graph`

* `subgraph.neighbor_set`, `subgraph.incidence_set`, and `subgraph.degree` are like their
  `simple_graph` counterparts, but they refer to vertices from `G` to avoid subtype coercions.

* `subgraph.coe` is the coercion from a `G' : subgraph G` to a `simple_graph G'.verts`.
  (This cannot be a `has_coe` instance since the destination type depends on `G'`.)

* `subgraph.is_spanning` for whether a subgraph is a spanning subgraph and
  `subgraph.is_induced` for whether a subgraph is an induced subgraph.

* Instances for `lattice (subgraph G)` and `bounded_order (subgraph G)`.

* `simple_graph.to_subgraph`: If a `simple_graph` is a subgraph of another, then you can turn it
  into a member of the larger graph's `simple_graph.subgraph` type.

* Graph homomorphisms from a subgraph to a graph (`subgraph.map_top`) and between subgraphs
  (`subgraph.map`).

## Implementation notes

* Recall that subgraphs are not determined by their vertex sets, so `set_like` does not apply to
  this kind of subobject.

## Todo

* Images of graph homomorphisms as subgraphs.

-/

universes u v

namespace simple_graph

/-- A subgraph of a `simple_graph` is a subset of vertices along with a restriction of the adjacency
relation that is symmetric and is supported by the vertex subset.  They also form a bounded lattice.

Thinking of `V → V → Prop` as `set (V × V)`, a set of darts (i.e., half-edges), then
`subgraph.adj_sub` is that the darts of a subgraph are a subset of the darts of `G`. -/
@[ext]
structure subgraph {V : Type u} (G : simple_graph V) :=
(verts : set V)
(adj : V → V → Prop)
(adj_sub : ∀ {v w : V}, adj v w → G.adj v w)
(edge_vert : ∀ {v w : V}, adj v w → v ∈ verts)
(symm : symmetric adj . obviously)

variables {ι : Sort*} {V : Type u} {W : Type v}

/-- The one-vertex subgraph. -/
@[simps]
protected def singleton_subgraph (G : simple_graph V) (v : V) : G.subgraph :=
{ verts := {v},
  adj := ⊥,
  adj_sub := by simp [-set.bot_eq_empty],
  edge_vert := by simp [-set.bot_eq_empty] }

/-- The one-edge subgraph. -/
@[simps]
def subgraph_of_adj (G : simple_graph V) {v w : V} (hvw : G.adj v w) : G.subgraph :=
{ verts := {v, w},
  adj := λ a b, ⟦(v, w)⟧ = ⟦(a, b)⟧,
  adj_sub := λ a b h, by { rw [← G.mem_edge_set, ← h], exact hvw },
  edge_vert := λ a b h, by { apply_fun (λ e, a ∈ e) at h, simpa using h } }

namespace subgraph

variables {G : simple_graph V} {G₁ G₂ : G.subgraph} {a b : V}

protected lemma loopless (G' : subgraph G) : irreflexive G'.adj :=
λ v h, G.loopless v (G'.adj_sub h)

lemma adj_comm (G' : subgraph G) (v w : V) : G'.adj v w ↔ G'.adj w v :=
⟨λ x, G'.symm x, λ x, G'.symm x⟩

@[symm] lemma adj_symm (G' : subgraph G) {u v : V} (h : G'.adj u v) : G'.adj v u := G'.symm h

protected lemma adj.symm {G' : subgraph G} {u v : V} (h : G'.adj u v) : G'.adj v u := G'.symm h

protected lemma adj.adj_sub {H : G.subgraph} {u v : V} (h : H.adj u v) : G.adj u v := H.adj_sub h

protected lemma adj.fst_mem {H : G.subgraph} {u v : V} (h : H.adj u v) : u ∈ H.verts :=
H.edge_vert h

protected lemma adj.snd_mem {H : G.subgraph} {u v : V} (h : H.adj u v) : v ∈ H.verts :=
h.symm.fst_mem

protected lemma adj.ne {H : G.subgraph} {u v : V} (h : H.adj u v) : u ≠ v := h.adj_sub.ne

/-- Coercion from `G' : subgraph G` to a `simple_graph ↥G'.verts`. -/
@[simps] protected def coe (G' : subgraph G) : simple_graph G'.verts :=
{ adj := λ v w, G'.adj v w,
  symm := λ v w h, G'.symm h,
  loopless := λ v h, loopless G v (G'.adj_sub h) }

@[simp] lemma coe_adj_sub (G' : subgraph G) (u v : G'.verts) (h : G'.coe.adj u v) : G.adj u v :=
G'.adj_sub h

/- Given `h : H.adj u v`, then `h.coe : H.coe.adj ⟨u, _⟩ ⟨v, _⟩`. -/
protected lemma adj.coe {H : G.subgraph} {u v : V} (h : H.adj u v) :
  H.coe.adj ⟨u, H.edge_vert h⟩ ⟨v, H.edge_vert h.symm⟩ := h

/-- A subgraph is called a *spanning subgraph* if it contains all the vertices of `G`. -/
def is_spanning (G' : subgraph G) : Prop := ∀ (v : V), v ∈ G'.verts

lemma is_spanning_iff {G' : subgraph G} : G'.is_spanning ↔ G'.verts = set.univ :=
set.eq_univ_iff_forall.symm

/-- Coercion from `subgraph G` to `simple_graph V`.  If `G'` is a spanning
subgraph, then `G'.spanning_coe` yields an isomorphic graph.
In general, this adds in all vertices from `V` as isolated vertices. -/
@[simps] protected def spanning_coe (G' : subgraph G) : simple_graph V :=
{ adj := G'.adj,
  symm := G'.symm,
  loopless := λ v hv, G.loopless v (G'.adj_sub hv) }

@[simp] lemma adj.of_spanning_coe {G' : subgraph G} {u v : G'.verts}
  (h : G'.spanning_coe.adj u v) : G.adj u v := G'.adj_sub h

@[simp] lemma spanning_coe_inj : G₁.spanning_coe = G₂.spanning_coe ↔ G₁.adj = G₂.adj :=
by simp [subgraph.spanning_coe]

/-- `spanning_coe` is equivalent to `coe` for a subgraph that `is_spanning`.  -/
@[simps] def spanning_coe_equiv_coe_of_spanning (G' : subgraph G) (h : G'.is_spanning) :
  G'.spanning_coe ≃g G'.coe :=
{ to_fun := λ v, ⟨v, h v⟩,
  inv_fun := λ v, v,
  left_inv := λ v, rfl,
  right_inv := λ ⟨v, hv⟩, rfl,
  map_rel_iff' := λ v w, iff.rfl }

/-- A subgraph is called an *induced subgraph* if vertices of `G'` are adjacent if
they are adjacent in `G`. -/
def is_induced (G' : subgraph G) : Prop :=
∀ {v w : V}, v ∈ G'.verts → w ∈ G'.verts → G.adj v w → G'.adj v w

/-- `H.support` is the set of vertices that form edges in the subgraph `H`. -/
def support (H : subgraph G) : set V := rel.dom H.adj

lemma mem_support (H : subgraph G) {v : V} : v ∈ H.support ↔ ∃ w, H.adj v w := iff.rfl

lemma support_subset_verts (H : subgraph G) : H.support ⊆ H.verts := λ v ⟨w, h⟩, H.edge_vert h

/-- `G'.neighbor_set v` is the set of vertices adjacent to `v` in `G'`. -/
def neighbor_set (G' : subgraph G) (v : V) : set V := set_of (G'.adj v)

lemma neighbor_set_subset (G' : subgraph G) (v : V) : G'.neighbor_set v ⊆ G.neighbor_set v :=
λ w h, G'.adj_sub h

lemma neighbor_set_subset_verts (G' : subgraph G) (v : V) : G'.neighbor_set v ⊆ G'.verts :=
λ _ h, G'.edge_vert (adj_symm G' h)

@[simp] lemma mem_neighbor_set (G' : subgraph G) (v w : V) : w ∈ G'.neighbor_set v ↔ G'.adj v w :=
iff.rfl

/-- A subgraph as a graph has equivalent neighbor sets. -/
def coe_neighbor_set_equiv {G' : subgraph G} (v : G'.verts) :
  G'.coe.neighbor_set v ≃ G'.neighbor_set v :=
{ to_fun := λ w, ⟨w, by { obtain ⟨w', hw'⟩ := w, simpa using hw' }⟩,
  inv_fun := λ w, ⟨⟨w, G'.edge_vert (G'.adj_symm w.2)⟩, by simpa using w.2⟩,
  left_inv := λ w, by simp,
  right_inv := λ w, by simp }

/-- The edge set of `G'` consists of a subset of edges of `G`. -/
def edge_set (G' : subgraph G) : set (sym2 V) := sym2.from_rel G'.symm

lemma edge_set_subset (G' : subgraph G) : G'.edge_set ⊆ G.edge_set :=
λ e, quotient.ind (λ e h, G'.adj_sub h) e

@[simp]
lemma mem_edge_set {G' : subgraph G} {v w : V} : ⟦(v, w)⟧ ∈ G'.edge_set ↔ G'.adj v w := iff.rfl

lemma mem_verts_if_mem_edge {G' : subgraph G} {e : sym2 V} {v : V}
  (he : e ∈ G'.edge_set) (hv : v ∈ e) : v ∈ G'.verts :=
begin
  refine quotient.ind (λ e he hv, _) e he hv,
  cases e with v w,
  simp only [mem_edge_set] at he,
  cases sym2.mem_iff.mp hv with h h; subst h,
  { exact G'.edge_vert he, },
  { exact G'.edge_vert (G'.symm he), },
end

/-- The `incidence_set` is the set of edges incident to a given vertex. -/
def incidence_set (G' : subgraph G) (v : V) : set (sym2 V) := {e ∈ G'.edge_set | v ∈ e}

lemma incidence_set_subset_incidence_set (G' : subgraph G) (v : V) :
  G'.incidence_set v ⊆ G.incidence_set v :=
λ e h, ⟨G'.edge_set_subset h.1, h.2⟩

lemma incidence_set_subset (G' : subgraph G) (v : V) : G'.incidence_set v ⊆ G'.edge_set :=
λ _ h, h.1

/-- Give a vertex as an element of the subgraph's vertex type. -/
@[reducible]
def vert (G' : subgraph G) (v : V) (h : v ∈ G'.verts) : G'.verts := ⟨v, h⟩

/--
Create an equal copy of a subgraph (see `copy_eq`) with possibly different definitional equalities.
See Note [range copy pattern].
-/
def copy (G' : subgraph G)
  (V'' : set V) (hV : V'' = G'.verts)
  (adj' : V → V → Prop) (hadj : adj' = G'.adj) :
  subgraph G :=
{ verts := V'',
  adj := adj',
  adj_sub := λ _ _, hadj.symm ▸ G'.adj_sub,
  edge_vert := λ _ _, hV.symm ▸ hadj.symm ▸ G'.edge_vert,
  symm := hadj.symm ▸ G'.symm }

lemma copy_eq (G' : subgraph G)
  (V'' : set V) (hV : V'' = G'.verts)
  (adj' : V → V → Prop) (hadj : adj' = G'.adj) :
  G'.copy V'' hV adj' hadj = G' :=
subgraph.ext _ _ hV hadj

/-- The union of two subgraphs. -/
instance : has_sup G.subgraph :=
⟨λ G₁ G₂,
  { verts := G₁.verts ∪ G₂.verts,
    adj := G₁.adj ⊔ G₂.adj,
    adj_sub := λ a b hab, or.elim hab (λ h, G₁.adj_sub h) (λ h, G₂.adj_sub h),
    edge_vert := λ a b, or.imp (λ h, G₁.edge_vert h) (λ h, G₂.edge_vert h),
    symm := λ a b, or.imp G₁.adj_symm G₂.adj_symm }⟩

/-- The intersection of two subgraphs. -/
instance : has_inf G.subgraph :=
⟨λ G₁ G₂,
  { verts := G₁.verts ∩ G₂.verts,
    adj := G₁.adj ⊓ G₂.adj,
    adj_sub := λ a b hab, G₁.adj_sub hab.1,
    edge_vert := λ a b, and.imp (λ h, G₁.edge_vert h) (λ h, G₂.edge_vert h),
    symm := λ a b, and.imp G₁.adj_symm G₂.adj_symm }⟩

/-- The `top` subgraph is `G` as a subgraph of itself. -/
instance : has_top G.subgraph :=
⟨{ verts := set.univ,
  adj := G.adj,
  adj_sub := λ v w h, h,
  edge_vert := λ v w h, set.mem_univ v,
  symm := G.symm }⟩

/-- The `bot` subgraph is the subgraph with no vertices or edges. -/
instance : has_bot G.subgraph :=
⟨{ verts := ∅,
  adj := ⊥,
  adj_sub := λ v w h, false.rec _ h,
  edge_vert := λ v w h, false.rec _ h,
  symm := λ u v h, h }⟩

instance : has_Sup G.subgraph :=
⟨λ s, { verts := ⋃ G' ∈ s, verts G',
        adj := λ a b, ∃ G' ∈ s, adj G' a b,
        adj_sub := by { rintro a b ⟨G', -, hab⟩, exact G'.adj_sub hab },
        edge_vert :=
          by { rintro a b ⟨G', hG', hab⟩, exact set.mem_Union₂_of_mem hG' (G'.edge_vert hab) },
        symm := λ a b, Exists₂.imp $ λ _ _, adj.symm }⟩

instance : has_Inf G.subgraph :=
⟨λ s, { verts := ⋂ G' ∈ s, verts G',
        adj := λ a b, (∀ ⦃G'⦄, G' ∈ s → adj G' a b) ∧ G.adj a b,
        adj_sub := λ a b, and.right,
        edge_vert := λ a b hab, set.mem_Inter₂_of_mem $ λ G' hG', G'.edge_vert $ hab.1 hG',
        symm := λ _ _, and.imp (forall₂_imp $ λ _ _, adj.symm) G.adj_symm }⟩

@[simp] lemma sup_adj : (G₁ ⊔ G₂).adj a b ↔ G₁.adj a b ∨ G₂.adj a b := iff.rfl
@[simp] lemma inf_adj : (G₁ ⊓ G₂).adj a b ↔ G₁.adj a b ∧ G₂.adj a b := iff.rfl
@[simp] lemma top_adj : (⊤ : subgraph G).adj a b ↔ G.adj a b := iff.rfl
@[simp] lemma not_bot_adj : ¬ (⊥ : subgraph G).adj a b := not_false

@[simp] lemma verts_sup (G₁ G₂ : G.subgraph) : (G₁ ⊔ G₂).verts = G₁.verts ∪ G₂.verts := rfl
@[simp] lemma verts_inf (G₁ G₂ : G.subgraph) : (G₁ ⊓ G₂).verts = G₁.verts ∩ G₂.verts := rfl
@[simp] lemma verts_top : (⊤ : G.subgraph).verts = set.univ := rfl
@[simp] lemma verts_bot : (⊥ : G.subgraph).verts = ∅ := rfl

@[simp] lemma Sup_adj {s : set G.subgraph} : (Sup s).adj a b ↔ ∃ G ∈ s, adj G a b := iff.rfl

@[simp] lemma Inf_adj {s : set G.subgraph} : (Inf s).adj a b ↔ (∀ G' ∈ s, adj G' a b) ∧ G.adj a b :=
iff.rfl

@[simp] lemma supr_adj {f : ι → G.subgraph} : (⨆ i, f i).adj a b ↔ ∃ i, (f i).adj a b :=
by simp [supr]

@[simp] lemma infi_adj {f : ι → G.subgraph} :
  (⨅ i, f i).adj a b ↔ (∀ i, (f i).adj a b) ∧ G.adj a b :=
by simp [infi]

lemma Inf_adj_of_nonempty {s : set G.subgraph} (hs : s.nonempty) :
  (Inf s).adj a b ↔ ∀ G' ∈ s, adj G' a b :=
Inf_adj.trans $ and_iff_left_of_imp $ by { obtain ⟨G', hG'⟩ := hs, exact λ h, G'.adj_sub (h _ hG') }

lemma infi_adj_of_nonempty [nonempty ι] {f : ι → G.subgraph} :
  (⨅ i, f i).adj a b ↔ ∀ i, (f i).adj a b :=
by simp [infi, Inf_adj_of_nonempty (set.range_nonempty _)]

@[simp] lemma verts_Sup (s : set G.subgraph) : (Sup s).verts = ⋃ G' ∈ s, verts G' := rfl
@[simp] lemma verts_Inf (s : set G.subgraph) : (Inf s).verts = ⋂ G' ∈ s, verts G' := rfl

@[simp] lemma verts_supr {f : ι → G.subgraph} : (⨆ i, f i).verts = ⋃ i, (f i).verts :=
by simp [supr]

@[simp] lemma verts_infi {f : ι → G.subgraph} : (⨅ i, f i).verts = ⋂ i, (f i).verts :=
by simp [infi]

/-- For subgraphs `G₁`, `G₂`, `G₁ ≤ G₂` iff `G₁.verts ⊆ G₂.verts` and
`∀ a b, G₁.adj a b → G₂.adj a b`. -/
instance : distrib_lattice G.subgraph :=
{ le := λ x y, x.verts ⊆ y.verts ∧ ∀ ⦃v w : V⦄, x.adj v w → y.adj v w,
  ..show distrib_lattice G.subgraph, from function.injective.distrib_lattice
    (λ G', (G'.verts, G'.spanning_coe))
    (λ G₁ G₂ h, by { rw prod.ext_iff at h, exact ext _ _ h.1 (spanning_coe_inj.1 h.2) })
    (λ _ _, rfl) (λ _ _, rfl) }

instance : bounded_order (subgraph G) :=
{ top := ⊤,
  bot := ⊥,
  le_top := λ x, ⟨set.subset_univ _, (λ v w h, x.adj_sub h)⟩,
  bot_le := λ x, ⟨set.empty_subset _, (λ v w h, false.rec _ h)⟩ }

-- Note that subgraphs do not form a Boolean algebra, because of `verts`.
instance : complete_distrib_lattice G.subgraph :=
{ le := (≤),
  sup := (⊔),
  inf := (⊓),
  top := ⊤,
  bot := ⊥,
  le_top := λ G', ⟨set.subset_univ _, λ a b, G'.adj_sub⟩,
  bot_le := λ G', ⟨set.empty_subset _, λ a b, false.elim⟩,
  Sup := Sup,
  le_Sup := λ s G' hG', ⟨set.subset_Union₂ G' hG', λ a b hab, ⟨G', hG', hab⟩⟩,
  Sup_le := λ s G' hG', ⟨set.Union₂_subset $ λ H hH, (hG' _ hH).1,
    by { rintro a b ⟨H, hH, hab⟩, exact (hG' _ hH).2 hab }⟩,
  Inf := Inf,
  Inf_le := λ s G' hG', ⟨set.Inter₂_subset G' hG', λ a b hab, hab.1 hG'⟩,
  le_Inf := λ s G' hG', ⟨set.subset_Inter₂ $ λ H hH, (hG' _ hH).1,
    λ a b hab, ⟨λ H hH, (hG' _ hH).2 hab, G'.adj_sub hab⟩⟩,
  inf_Sup_le_supr_inf := λ G' s, begin
    refine ⟨_, λ a b hab, _⟩,
    { simp only [verts_inf, verts_Sup, verts_supr, set.le_eq_subset],
      exact (set.inter_Union₂ _ _).subset },
    { simpa only [spanning_coe_adj, exists_prop, Sup_adj, and_imp, forall_exists_index, supr_adj,
        inf_adj, ←exists_and_distrib_right, exists_and_distrib_left, and_assoc, and_self_right]
        using hab }
  end,
  infi_sup_le_sup_Inf := λ G' s, begin
    refine ⟨_, λ a b hab, _⟩,
    { simp only [set.le_eq_subset, verts_infi, verts_sup, verts_Inf],
      exact (set.union_Inter₂ _ _).superset },
    simp only [spanning_coe_adj, sup_adj, Inf_adj, sup_adj, Inf_adj, infi_adj] at ⊢ hab,
    have : (∀ G'' ∈ s, adj G' a b ∨ adj G'' a b) ∧ G.adj a b :=
      (and_congr_left $ λ h, forall_congr $ λ H, _).1 hab,
    simpa [forall_or_distrib_left, or_and_distrib_right, and_iff_left_of_imp G'.adj_sub] using this,
    exact and_iff_left h,
  end,
  ..subgraph.distrib_lattice }

@[simps] instance subgraph_inhabited : inhabited (subgraph G) := ⟨⊥⟩

@[simp] lemma neighbor_set_sup {H H' : G.subgraph} (v : V) :
  (H ⊔ H').neighbor_set v = H.neighbor_set v ∪ H'.neighbor_set v := rfl

@[simp] lemma neighbor_set_inf {H H' : G.subgraph} (v : V) :
  (H ⊓ H').neighbor_set v = H.neighbor_set v ∩ H'.neighbor_set v := rfl

@[simp] lemma neighbor_set_top (v : V) : (⊤ : G.subgraph).neighbor_set v = G.neighbor_set v := rfl
@[simp] lemma neighbor_set_bot (v : V) : (⊥ : G.subgraph).neighbor_set v = ∅ := rfl

@[simp] lemma neighbor_set_Sup (s : set G.subgraph) (v : V) :
  (Sup s).neighbor_set v = ⋃ G' ∈ s, neighbor_set G' v :=
by { ext, simp }

@[simp] lemma neighbor_set_Inf (s : set G.subgraph) (v : V) :
  (Inf s).neighbor_set v = (⋂ G' ∈ s, neighbor_set G' v) ∩ G.neighbor_set v :=
by { ext, simp }

@[simp] lemma neighbor_set_supr (f : ι → G.subgraph) (v : V) :
  (⨆ i, f i).neighbor_set v = ⋃ i, (f i).neighbor_set v :=
by simp [supr]

@[simp] lemma neighbor_set_infi (f : ι → G.subgraph) (v : V) :
  (⨅ i, f i).neighbor_set v = (⋂ i, (f i).neighbor_set v) ∩ G.neighbor_set v :=
by simp [infi]

@[simp] lemma edge_set_top : (⊤ : subgraph G).edge_set = G.edge_set := rfl

@[simp] lemma edge_set_bot : (⊥ : subgraph G).edge_set = ∅ :=
set.ext $ sym2.ind (by simp)

@[simp] lemma edge_set_inf {H₁ H₂ : subgraph G} : (H₁ ⊓ H₂).edge_set = H₁.edge_set ∩ H₂.edge_set :=
set.ext $ sym2.ind (by simp)

@[simp] lemma edge_set_sup {H₁ H₂ : subgraph G} : (H₁ ⊔ H₂).edge_set = H₁.edge_set ∪ H₂.edge_set :=
set.ext $ sym2.ind (by simp)

@[simp] lemma edge_set_Sup (s : set G.subgraph) : (Sup s).edge_set = ⋃ G' ∈ s, edge_set G' :=
by { ext e, induction e using sym2.ind, simp }

@[simp] lemma edge_set_Inf (s : set G.subgraph) :
  (Inf s).edge_set = (⋂ G' ∈ s, edge_set G') ∩ G.edge_set :=
by { ext e, induction e using sym2.ind, simp }

@[simp] lemma edge_set_supr (f : ι → G.subgraph) : (⨆ i, f i).edge_set = ⋃ i, (f i).edge_set :=
by simp [supr]

@[simp] lemma edge_set_infi (f : ι → G.subgraph) :
  (⨅ i, f i).edge_set = (⋂ i, (f i).edge_set) ∩ G.edge_set :=
by simp [infi]

@[simp] lemma spanning_coe_top : (⊤ : subgraph G).spanning_coe = G :=
by { ext, refl }

@[simp] lemma spanning_coe_bot : (⊥ : subgraph G).spanning_coe = ⊥ := rfl

/-- Turn a subgraph of a `simple_graph` into a member of its subgraph type. -/
@[simps] def _root_.simple_graph.to_subgraph (H : simple_graph V) (h : H ≤ G) : G.subgraph :=
{ verts := set.univ,
  adj := H.adj,
  adj_sub := h,
  edge_vert := λ v w h, set.mem_univ v,
  symm := H.symm }

lemma support_mono {H H' : subgraph G} (h : H ≤ H') : H.support ⊆ H'.support :=
rel.dom_mono h.2

lemma _root_.simple_graph.to_subgraph.is_spanning (H : simple_graph V) (h : H ≤ G) :
  (H.to_subgraph h).is_spanning := set.mem_univ

lemma spanning_coe_le_of_le {H H' : subgraph G} (h : H ≤ H') :
  H.spanning_coe ≤ H'.spanning_coe := h.2

/-- The top of the `subgraph G` lattice is equivalent to the graph itself. -/
def top_equiv : (⊤ : subgraph G).coe ≃g G :=
{ to_fun := λ v, ↑v,
  inv_fun := λ v, ⟨v, trivial⟩,
  left_inv := λ ⟨v, _⟩, rfl,
  right_inv := λ v, rfl,
  map_rel_iff' := λ a b, iff.rfl }

/-- The bottom of the `subgraph G` lattice is equivalent to the empty graph on the empty
vertex type. -/
def bot_equiv : (⊥ : subgraph G).coe ≃g (⊥ : simple_graph empty) :=
{ to_fun := λ v, v.property.elim,
  inv_fun := λ v, v.elim,
  left_inv := λ ⟨_, h⟩, h.elim,
  right_inv := λ v, v.elim,
  map_rel_iff' := λ a b, iff.rfl }

lemma edge_set_mono {H₁ H₂ : subgraph G} (h : H₁ ≤ H₂) : H₁.edge_set ≤ H₂.edge_set :=
λ e, sym2.ind h.2 e

lemma _root_.disjoint.edge_set {H₁ H₂ : subgraph G}
  (h : disjoint H₁ H₂) : disjoint H₁.edge_set H₂.edge_set :=
disjoint_iff_inf_le.mpr $ by simpa using edge_set_mono h.le_bot

/-- Graph homomorphisms induce a covariant function on subgraphs. -/
@[simps]
protected def map {G' : simple_graph W} (f : G →g G') (H : G.subgraph) : G'.subgraph :=
{ verts := f '' H.verts,
  adj := relation.map H.adj f f,
  adj_sub := by { rintro _ _ ⟨u, v, h, rfl, rfl⟩, exact f.map_rel (H.adj_sub h) },
  edge_vert := by { rintro _ _ ⟨u, v, h, rfl, rfl⟩, exact set.mem_image_of_mem _ (H.edge_vert h) },
  symm := by { rintro _ _ ⟨u, v, h, rfl, rfl⟩, exact ⟨v, u, H.symm h, rfl, rfl⟩ } }

lemma map_monotone {G' : simple_graph W} (f : G →g G') : monotone (subgraph.map f) :=
begin
  intros H H' h,
  split,
  { intro,
    simp only [map_verts, set.mem_image, forall_exists_index, and_imp],
    rintro v hv rfl,
    exact ⟨_, h.1 hv, rfl⟩ },
  { rintros _ _ ⟨u, v, ha, rfl, rfl⟩,
    exact ⟨_, _, h.2 ha, rfl, rfl⟩ }
end

lemma map_sup {G : simple_graph V} {G' : simple_graph W} (f : G →g G')
  {H H' : G.subgraph} :
  (H ⊔ H').map f = H.map f ⊔ H'.map f :=
begin
  ext1,
  { simp only [set.image_union, map_verts, verts_sup]},
  { ext,
    simp only [relation.map, map_adj, sup_adj],
    split,
    { rintro ⟨a, b, h|h, rfl, rfl⟩,
      { exact or.inl ⟨_, _, h, rfl, rfl⟩ },
      { exact or.inr ⟨_, _, h, rfl, rfl⟩ } },
    { rintro (⟨a, b, h, rfl, rfl⟩|⟨a, b, h, rfl, rfl⟩),
      { exact ⟨_, _, or.inl h, rfl, rfl⟩ },
      { exact ⟨_, _, or.inr h, rfl, rfl⟩ } } },
end

/-- Graph homomorphisms induce a contravariant function on subgraphs. -/
@[simps]
protected def comap {G' : simple_graph W} (f : G →g G') (H : G'.subgraph) : G.subgraph :=
{ verts := f ⁻¹' H.verts,
  adj := λ u v, G.adj u v ∧ H.adj (f u) (f v),
  adj_sub := by { rintros v w ⟨ga, ha⟩, exact ga },
  edge_vert := by { rintros v w ⟨ga, ha⟩, simp [H.edge_vert ha] } }

lemma comap_monotone {G' : simple_graph W} (f : G →g G') : monotone (subgraph.comap f) :=
begin
  intros H H' h,
  split,
  { intro,
    simp only [comap_verts, set.mem_preimage],
    apply h.1, },
  { intros v w,
    simp only [comap_adj, and_imp, true_and] { contextual := tt },
    intro,
    apply h.2, }
end

lemma map_le_iff_le_comap {G' : simple_graph W} (f : G →g G') (H : G.subgraph) (H' : G'.subgraph) :
  H.map f ≤ H' ↔ H ≤ H'.comap f :=
begin
  refine ⟨λ h, ⟨λ v hv, _, λ v w hvw, _⟩, λ h, ⟨λ v, _, λ v w, _⟩⟩,
  { simp only [comap_verts, set.mem_preimage],
    exact h.1 ⟨v, hv, rfl⟩, },
  { simp only [H.adj_sub hvw, comap_adj, true_and],
    exact h.2 ⟨v, w, hvw, rfl, rfl⟩, },
  { simp only [map_verts, set.mem_image, forall_exists_index, and_imp],
    rintro w hw rfl,
    exact h.1 hw, },
  { simp only [relation.map, map_adj, forall_exists_index, and_imp],
    rintros u u' hu rfl rfl,
    have := h.2 hu,
    simp only [comap_adj] at this,
    exact this.2, }
end

/-- Given two subgraphs, one a subgraph of the other, there is an induced injective homomorphism of
the subgraphs as graphs. -/
@[simps]
def inclusion {x y : subgraph G} (h : x ≤ y) : x.coe →g y.coe :=
{ to_fun := λ v, ⟨↑v, and.left h v.property⟩,
  map_rel' := λ v w hvw, h.2 hvw }

lemma inclusion.injective {x y : subgraph G} (h : x ≤ y) : function.injective (inclusion h) :=
λ v w h, by { simp only [inclusion, rel_hom.coe_fn_mk, subtype.mk_eq_mk] at h, exact subtype.ext h }

/-- There is an induced injective homomorphism of a subgraph of `G` into `G`. -/
@[simps]
protected def hom (x : subgraph G) : x.coe →g G :=
{ to_fun := λ v, v,
  map_rel' := λ v w hvw, x.adj_sub hvw }

lemma hom.injective {x : subgraph G} : function.injective x.hom :=
λ v w h, subtype.ext h

/-- There is an induced injective homomorphism of a subgraph of `G` as
a spanning subgraph into `G`. -/
@[simps] def spanning_hom (x : subgraph G) : x.spanning_coe →g G :=
{ to_fun := id,
  map_rel' := λ v w hvw, x.adj_sub hvw }

lemma spanning_hom.injective {x : subgraph G} : function.injective x.spanning_hom :=
λ v w h, h

lemma neighbor_set_subset_of_subgraph {x y : subgraph G} (h : x ≤ y) (v : V) :
  x.neighbor_set v ⊆ y.neighbor_set v :=
λ w h', h.2 h'

instance neighbor_set.decidable_pred (G' : subgraph G) [h : decidable_rel G'.adj] (v : V) :
  decidable_pred (∈ G'.neighbor_set v) := h v

/-- If a graph is locally finite at a vertex, then so is a subgraph of that graph. -/
instance finite_at {G' : subgraph G} (v : G'.verts) [decidable_rel G'.adj]
   [fintype (G.neighbor_set v)] : fintype (G'.neighbor_set v) :=
set.fintype_subset (G.neighbor_set v) (G'.neighbor_set_subset v)

/-- If a subgraph is locally finite at a vertex, then so are subgraphs of that subgraph.

This is not an instance because `G''` cannot be inferred. -/
def finite_at_of_subgraph {G' G'' : subgraph G} [decidable_rel G'.adj]
   (h : G' ≤ G'') (v : G'.verts) [hf : fintype (G''.neighbor_set v)] :
   fintype (G'.neighbor_set v) :=
set.fintype_subset (G''.neighbor_set v) (neighbor_set_subset_of_subgraph h v)

instance (G' : subgraph G) [fintype G'.verts]
  (v : V) [decidable_pred (∈ G'.neighbor_set v)] : fintype (G'.neighbor_set v) :=
set.fintype_subset G'.verts (neighbor_set_subset_verts G' v)

instance coe_finite_at {G' : subgraph G} (v : G'.verts) [fintype (G'.neighbor_set v)] :
  fintype (G'.coe.neighbor_set v) :=
fintype.of_equiv _ (coe_neighbor_set_equiv v).symm

lemma is_spanning.card_verts [fintype V] {G' : subgraph G} [fintype G'.verts]
  (h : G'.is_spanning) : G'.verts.to_finset.card = fintype.card V :=
by { rw is_spanning_iff at h, simpa [h] }

/-- The degree of a vertex in a subgraph. It's zero for vertices outside the subgraph. -/
def degree (G' : subgraph G) (v : V) [fintype (G'.neighbor_set v)] : ℕ :=
fintype.card (G'.neighbor_set v)

lemma finset_card_neighbor_set_eq_degree {G' : subgraph G} {v : V} [fintype (G'.neighbor_set v)] :
  (G'.neighbor_set v).to_finset.card = G'.degree v := by rw [degree, set.to_finset_card]

lemma degree_le (G' : subgraph G) (v : V)
  [fintype (G'.neighbor_set v)] [fintype (G.neighbor_set v)] :
  G'.degree v ≤ G.degree v :=
begin
  rw ←card_neighbor_set_eq_degree,
  exact set.card_le_of_subset (G'.neighbor_set_subset v),
end

lemma degree_le' (G' G'' : subgraph G) (h : G' ≤ G'') (v : V)
  [fintype (G'.neighbor_set v)] [fintype (G''.neighbor_set v)] :
  G'.degree v ≤ G''.degree v :=
set.card_le_of_subset (neighbor_set_subset_of_subgraph h v)

@[simp] lemma coe_degree (G' : subgraph G) (v : G'.verts)
  [fintype (G'.coe.neighbor_set v)] [fintype (G'.neighbor_set v)] :
  G'.coe.degree v = G'.degree v :=
begin
  rw ←card_neighbor_set_eq_degree,
  exact fintype.card_congr (coe_neighbor_set_equiv v),
end

@[simp] lemma degree_spanning_coe {G' : G.subgraph} (v : V) [fintype (G'.neighbor_set v)]
  [fintype (G'.spanning_coe.neighbor_set v)] :
  G'.spanning_coe.degree v = G'.degree v :=
by { rw [← card_neighbor_set_eq_degree, subgraph.degree], congr }

lemma degree_eq_one_iff_unique_adj {G' : subgraph G} {v : V} [fintype (G'.neighbor_set v)] :
  G'.degree v = 1 ↔ ∃! (w : V), G'.adj v w :=
begin
  rw [← finset_card_neighbor_set_eq_degree, finset.card_eq_one, finset.singleton_iff_unique_mem],
  simp only [set.mem_to_finset, mem_neighbor_set],
end

end subgraph

section mk_properties
/-! ### Properties of `singleton_subgraph` and `subgraph_of_adj` -/

variables {G : simple_graph V} {G' : simple_graph W}

instance nonempty_singleton_subgraph_verts (v : V) : nonempty (G.singleton_subgraph v).verts :=
⟨⟨v, set.mem_singleton v⟩⟩

@[simp] lemma singleton_subgraph_le_iff (v : V) (H : G.subgraph) :
  G.singleton_subgraph v ≤ H ↔ v ∈ H.verts :=
begin
  refine ⟨λ h, h.1 (set.mem_singleton v), _⟩,
  intro h,
  split,
  { simp [h] },
  { simp [-set.bot_eq_empty] }
end

@[simp] lemma map_singleton_subgraph (f : G →g G') {v : V} :
  subgraph.map f (G.singleton_subgraph v) = G'.singleton_subgraph (f v) :=
by ext; simp only [relation.map, subgraph.map_adj, singleton_subgraph_adj, pi.bot_apply,
  exists_and_distrib_left, and_iff_left_iff_imp, is_empty.forall_iff, subgraph.map_verts,
  singleton_subgraph_verts, set.image_singleton]

@[simp] lemma neighbor_set_singleton_subgraph (v w : V) :
  (G.singleton_subgraph v).neighbor_set w = ∅ :=
by { ext u, refl }

@[simp] lemma edge_set_singleton_subgraph (v : V) :
  (G.singleton_subgraph v).edge_set = ∅ :=
sym2.from_rel_bot

lemma eq_singleton_subgraph_iff_verts_eq (H : G.subgraph) {v : V} :
  H = G.singleton_subgraph v ↔ H.verts = {v} :=
begin
  refine ⟨λ h, by simp [h], λ h, _⟩,
  ext,
  { rw [h, singleton_subgraph_verts] },
  { simp only [Prop.bot_eq_false, singleton_subgraph_adj, pi.bot_apply, iff_false],
    intro ha,
    have ha1 := ha.fst_mem,
    have ha2 := ha.snd_mem,
    rw [h, set.mem_singleton_iff] at ha1 ha2,
    subst_vars,
    exact ha.ne rfl },
end

instance nonempty_subgraph_of_adj_verts {v w : V} (hvw : G.adj v w) :
  nonempty (G.subgraph_of_adj hvw).verts := ⟨⟨v, by simp⟩⟩

@[simp] lemma edge_set_subgraph_of_adj {v w : V} (hvw : G.adj v w) :
  (G.subgraph_of_adj hvw).edge_set = {⟦(v, w)⟧} :=
begin
  ext e,
  refine e.ind _,
  simp only [eq_comm, set.mem_singleton_iff, subgraph.mem_edge_set, subgraph_of_adj_adj,
    iff_self, forall_2_true_iff],
end

lemma subgraph_of_adj_symm {v w : V} (hvw : G.adj v w) :
  G.subgraph_of_adj hvw.symm = G.subgraph_of_adj hvw :=
by ext; simp [or_comm, and_comm]

@[simp] lemma map_subgraph_of_adj (f : G →g G')
  {v w : V} (hvw : G.adj v w) :
  subgraph.map f (G.subgraph_of_adj hvw) = G'.subgraph_of_adj (f.map_adj hvw) :=
begin
  ext,
  { simp only [subgraph.map_verts, subgraph_of_adj_verts, set.mem_image,
      set.mem_insert_iff, set.mem_singleton_iff],
    split,
    { rintro ⟨u, rfl|rfl, rfl⟩; simp },
    { rintro (rfl|rfl),
      { use v, simp },
      { use w, simp } } },
  { simp only [relation.map, subgraph.map_adj, subgraph_of_adj_adj, quotient.eq, sym2.rel_iff],
    split,
    { rintro ⟨a, b, (⟨rfl,rfl⟩|⟨rfl,rfl⟩), rfl, rfl⟩; simp },
    { rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩),
      { use [v, w], simp },
      { use [w, v], simp } } }
end

lemma neighbor_set_subgraph_of_adj_subset {u v w : V} (hvw : G.adj v w) :
  (G.subgraph_of_adj hvw).neighbor_set u ⊆ {v, w} :=
(G.subgraph_of_adj hvw).neighbor_set_subset_verts _

@[simp] lemma neighbor_set_fst_subgraph_of_adj {v w : V} (hvw : G.adj v w) :
  (G.subgraph_of_adj hvw).neighbor_set v = {w} :=
begin
  ext u,
  suffices : w = u ↔ u = w, by simpa [hvw.ne.symm] using this,
  rw eq_comm,
end

@[simp] lemma neighbor_set_snd_subgraph_of_adj {v w : V} (hvw : G.adj v w) :
  (G.subgraph_of_adj hvw).neighbor_set w = {v} :=
begin
  rw subgraph_of_adj_symm hvw.symm,
  exact neighbor_set_fst_subgraph_of_adj hvw.symm,
end

@[simp] lemma neighbor_set_subgraph_of_adj_of_ne_of_ne {u v w : V} (hvw : G.adj v w)
  (hv : u ≠ v) (hw : u ≠ w) :
  (G.subgraph_of_adj hvw).neighbor_set u = ∅ :=
by { ext, simp [hv.symm, hw.symm] }

lemma neighbor_set_subgraph_of_adj [decidable_eq V] {u v w : V} (hvw : G.adj v w) :
  (G.subgraph_of_adj hvw).neighbor_set u =
  (if u = v then {w} else ∅) ∪ (if u = w then {v} else ∅) :=
by split_ifs; subst_vars; simp [*]

lemma singleton_subgraph_fst_le_subgraph_of_adj {u v : V} {h : G.adj u v} :
  G.singleton_subgraph u ≤ G.subgraph_of_adj h :=
by split; simp [-set.bot_eq_empty]

lemma singleton_subgraph_snd_le_subgraph_of_adj {u v : V} {h : G.adj u v} :
  G.singleton_subgraph v ≤ G.subgraph_of_adj h :=
by split; simp [-set.bot_eq_empty]

end mk_properties

namespace subgraph

variables {G : simple_graph V}

/-! ### Subgraphs of subgraphs -/

/-- Given a subgraph of a subgraph of `G`, construct a subgraph of `G`. -/
@[reducible]
protected def coe_subgraph {G' : G.subgraph} : G'.coe.subgraph → G.subgraph := subgraph.map G'.hom

/-- Given a subgraph of `G`, restrict it to being a subgraph of another subgraph `G'` by
taking the portion of `G` that intersects `G'`. -/
@[reducible]
protected def restrict {G' : G.subgraph} : G.subgraph → G'.coe.subgraph := subgraph.comap G'.hom

lemma restrict_coe_subgraph {G' : G.subgraph} (G'' : G'.coe.subgraph) :
  G''.coe_subgraph.restrict = G'' :=
begin
  ext,
  { simp },
  { simp only [relation.map, comap_adj, coe_adj, subtype.coe_prop, hom_apply, map_adj,
      set_coe.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right_right,
      subtype.coe_eta, exists_true_left, exists_eq_right, and_iff_right_iff_imp],
    apply G''.adj_sub, }
end

lemma coe_subgraph_injective (G' : G.subgraph) :
  function.injective (subgraph.coe_subgraph : G'.coe.subgraph → G.subgraph) :=
function.left_inverse.injective restrict_coe_subgraph

/-! ### Edge deletion -/

/-- Given a subgraph `G'` and a set of vertex pairs, remove all of the corresponding edges
from its edge set, if present.

See also: `simple_graph.delete_edges`. -/
def delete_edges (G' : G.subgraph) (s : set (sym2 V)) : G.subgraph :=
{ verts := G'.verts,
  adj := G'.adj \ sym2.to_rel s,
  adj_sub := λ a b h', G'.adj_sub h'.1,
  edge_vert := λ a b h', G'.edge_vert h'.1,
  symm := λ a b, by simp [G'.adj_comm, sym2.eq_swap] }

section delete_edges
variables {G' : G.subgraph} (s : set (sym2 V))

@[simp] lemma delete_edges_verts : (G'.delete_edges s).verts = G'.verts := rfl

@[simp] lemma delete_edges_adj (v w : V) :
  (G'.delete_edges s).adj v w ↔ G'.adj v w ∧ ¬ ⟦(v, w)⟧ ∈ s := iff.rfl

@[simp] lemma delete_edges_delete_edges (s s' : set (sym2 V)) :
  (G'.delete_edges s).delete_edges s' = G'.delete_edges (s ∪ s') :=
by ext; simp [and_assoc, not_or_distrib]

@[simp] lemma delete_edges_empty_eq : G'.delete_edges ∅ = G' :=
by ext; simp

@[simp] lemma delete_edges_spanning_coe_eq :
  G'.spanning_coe.delete_edges s = (G'.delete_edges s).spanning_coe :=
by { ext, simp }

lemma delete_edges_coe_eq (s : set (sym2 G'.verts)) :
  G'.coe.delete_edges s = (G'.delete_edges (sym2.map coe '' s)).coe :=
begin
  ext ⟨v, hv⟩ ⟨w, hw⟩,
  simp only [simple_graph.delete_edges_adj, coe_adj, subtype.coe_mk, delete_edges_adj,
    set.mem_image, not_exists, not_and, and.congr_right_iff],
  intro h,
  split,
  { intros hs,
    refine sym2.ind _,
    rintro ⟨v', hv'⟩ ⟨w', hw'⟩,
    simp only [sym2.map_pair_eq, subtype.coe_mk, quotient.eq],
    contrapose!,
    rintro (_ | _); simpa [sym2.eq_swap], },
  { intros h' hs,
    exact h' _ hs rfl, },
end

lemma coe_delete_edges_eq (s : set (sym2 V)) :
  (G'.delete_edges s).coe = G'.coe.delete_edges (sym2.map coe ⁻¹' s) :=
by { ext ⟨v, hv⟩ ⟨w, hw⟩, simp }

lemma delete_edges_le : G'.delete_edges s ≤ G' :=
by split; simp { contextual := tt }

lemma delete_edges_le_of_le {s s' : set (sym2 V)} (h : s ⊆ s') :
  G'.delete_edges s' ≤ G'.delete_edges s :=
begin
  split;
  simp only [delete_edges_verts, delete_edges_adj, true_and, and_imp] {contextual := tt},
  exact λ v w hvw hs' hs, hs' (h hs),
end

@[simp] lemma delete_edges_inter_edge_set_left_eq :
  G'.delete_edges (G'.edge_set ∩ s) = G'.delete_edges s :=
by ext; simp [imp_false] { contextual := tt }

@[simp] lemma delete_edges_inter_edge_set_right_eq :
  G'.delete_edges (s ∩ G'.edge_set) = G'.delete_edges s :=
by ext; simp [imp_false] { contextual := tt }

lemma coe_delete_edges_le :
  (G'.delete_edges s).coe ≤ (G'.coe : simple_graph G'.verts) :=
λ v w, by simp { contextual := tt }

lemma spanning_coe_delete_edges_le (G' : G.subgraph) (s : set (sym2 V)) :
  (G'.delete_edges s).spanning_coe ≤ G'.spanning_coe :=
spanning_coe_le_of_le (delete_edges_le s)

end delete_edges

/-! ### Induced subgraphs -/

/- Given a subgraph, we can change its vertex set while removing any invalid edges, which
gives induced subgraphs. See also `simple_graph.induce` for the `simple_graph` version, which,
unlike for subgraphs, results in a graph with a different vertex type. -/

/-- The induced subgraph of a subgraph. The expectation is that `s ⊆ G'.verts` for the usual
notion of an induced subgraph, but, in general, `s` is taken to be the new vertex set and edges
are induced from the subgraph `G'`. -/
@[simps]
def induce (G' : G.subgraph) (s : set V) : G.subgraph :=
{ verts := s,
  adj := λ u v, u ∈ s ∧ v ∈ s ∧ G'.adj u v,
  adj_sub := λ u v, by { rintro ⟨-, -, ha⟩, exact G'.adj_sub ha },
  edge_vert := λ u v, by { rintro ⟨h, -, -⟩, exact h } }

lemma _root_.simple_graph.induce_eq_coe_induce_top (s : set V) :
  G.induce s = ((⊤ : G.subgraph).induce s).coe :=
by { ext v w, simp }

section induce
variables {G' G'' : G.subgraph} {s s' : set V}

lemma induce_mono (hg : G' ≤ G'') (hs : s ⊆ s') : G'.induce s ≤ G''.induce s' :=
begin
  split,
  { simp [hs], },
  { simp only [induce_adj, true_and, and_imp] { contextual := tt },
    intros v w hv hw ha,
    exact ⟨hs hv, hs hw, hg.2 ha⟩, },
end

@[mono]
lemma induce_mono_left (hg : G' ≤ G'') : G'.induce s ≤ G''.induce s := induce_mono hg (by refl)

@[mono]
lemma induce_mono_right (hs : s ⊆ s') : G'.induce s ≤ G'.induce s' := induce_mono (by refl) hs

@[simp] lemma induce_empty : G'.induce ∅ = ⊥ :=
by ext; simp

@[simp] lemma induce_self_verts : G'.induce G'.verts = G' :=
begin
  ext,
  { simp },
  { split;
    simp only [induce_adj, implies_true_iff, and_true] {contextual := tt},
    exact λ ha, ⟨G'.edge_vert ha, G'.edge_vert ha.symm⟩ }
end

lemma singleton_subgraph_eq_induce {v : V} :
  G.singleton_subgraph v = (⊤ : G.subgraph).induce {v} :=
by ext; simp [-set.bot_eq_empty, Prop.bot_eq_false] { contextual := tt }

lemma subgraph_of_adj_eq_induce {v w : V} (hvw : G.adj v w) :
  G.subgraph_of_adj hvw = (⊤ : G.subgraph).induce {v, w} :=
begin
  ext,
  { simp },
  { split,
    { intro h,
      simp only [subgraph_of_adj_adj, quotient.eq, sym2.rel_iff] at h,
      obtain ⟨rfl, rfl⟩|⟨rfl, rfl⟩ := h; simp [hvw, hvw.symm], },
    { intro h,
      simp only [induce_adj, set.mem_insert_iff, set.mem_singleton_iff, top_adj] at h,
      obtain ⟨rfl|rfl, rfl|rfl, ha⟩ := h;
        exact (ha.ne rfl).elim <|> simp } }
end

end induce

/-- Given a subgraph and a set of vertices, delete all the vertices from the subgraph,
if present. Any edges indicent to the deleted vertices are deleted as well. -/
@[reducible] def delete_verts (G' : G.subgraph) (s : set V) : G.subgraph := G'.induce (G'.verts \ s)

section delete_verts
variables {G' : G.subgraph} {s : set V}

lemma delete_verts_verts : (G'.delete_verts s).verts = G'.verts \ s := rfl

lemma delete_verts_adj {u v : V} :
  (G'.delete_verts s).adj u v ↔
  u ∈ G'.verts ∧ ¬ u ∈ s ∧ v ∈ G'.verts ∧ ¬ v ∈ s ∧ G'.adj u v :=
by simp [and_assoc]

@[simp] lemma delete_verts_delete_verts (s s' : set V) :
  (G'.delete_verts s).delete_verts s' = G'.delete_verts (s ∪ s') :=
by ext; simp [not_or_distrib, and_assoc] { contextual := tt }

@[simp] lemma delete_verts_empty : G'.delete_verts ∅ = G' :=
by simp [delete_verts]

lemma delete_verts_le : G'.delete_verts s ≤ G' :=
by split; simp [set.diff_subset]

@[mono]
lemma delete_verts_mono {G' G'' : G.subgraph} (h : G' ≤ G'') :
  G'.delete_verts s ≤ G''.delete_verts s :=
induce_mono h (set.diff_subset_diff_left h.1)

@[mono]
lemma delete_verts_anti {s s' : set V} (h : s ⊆ s') :
  G'.delete_verts s' ≤ G'.delete_verts s :=
induce_mono (le_refl _) (set.diff_subset_diff_right h)

@[simp] lemma delete_verts_inter_verts_left_eq :
  G'.delete_verts (G'.verts ∩ s) = G'.delete_verts s :=
by ext; simp [imp_false] { contextual := tt }

@[simp] lemma delete_verts_inter_verts_set_right_eq :
  G'.delete_verts (s ∩ G'.verts) = G'.delete_verts s :=
by ext; simp [imp_false] { contextual := tt }

end delete_verts

end subgraph

end simple_graph
