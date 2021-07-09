/-
Copyright (c) 2021 Hunter Monroe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hunter Monroe, Kyle Miller, Alena Gusakov
-/
import combinatorics.simple_graph.basic
import data.set.finite

/-!
# Subgraphs of a simple graph

A subgraph of a simple graph consists of subsets of the graph's vertices and edges such that the
endpoints of each edge are present in the vertex subset.  The edge subset is formalized as a
sub-relation of the adjacency relation of the simple graph.

## Todo

* The injective homomorphism from a subgraph of `G` as a simple graph to `G`.

* The complete lattice instance on subgraphs.
-/

universe u

namespace simple_graph

/--
A subgraph of a `simple_graph` is a subset of vertices along with a restriction of the adjacency
relation that is symmetric and is supported by the vertex subset.  They also form a bounded lattice.

Thinking of `V → V → Prop` as `set (V × V)`, a set of darts, then `subgraph.adj_sub` is that the
darts of a subgraph are a subset of the darts of `G`.
-/
@[ext]
structure subgraph {V : Type u} (G : simple_graph V) :=
(verts : set V)
(adj : V → V → Prop)
(adj_sub : ∀ ⦃v w : V⦄, adj v w → G.adj v w)
(edge_vert : ∀ ⦃v w : V⦄, adj v w → v ∈ verts)
(sym : symmetric adj . obviously)

/-- Given a graph defined on a subset of vertices of a simple graph whose adjacency relation is
a restriction, then it can be regarded as a subgraph. -/
@[simps]
def subgraph_of {V : Type u} (G : simple_graph V) {V' : set V} (G' : simple_graph V')
  (h : ∀ (u v : V'), G'.adj u v → G.adj u v) : subgraph G :=
{ verts := V',
  adj := λ a b, ∃ (ha : a ∈ V') (hb : b ∈ V'), G'.adj ⟨a, ha⟩ ⟨b, hb⟩,
  adj_sub := λ v w ⟨hv, hw, hvw⟩, h _ _ hvw,
  edge_vert := λ v w ⟨hv, hw, hvw⟩, hv,
  sym := λ a b ⟨ha, hb, hadj⟩, ⟨hb, ha, G'.sym hadj⟩ }

namespace subgraph

variables {V : Type u} {G : simple_graph V}

/-- Coercion from `subgraph G` to `simple_graph G.V`. -/
@[simps]
def coe (G' : subgraph G) : simple_graph G'.verts :=
{ adj := λ v w, G'.adj v w,
  sym := λ v w h, G'.sym h,
  loopless := λ v h, loopless G v (G'.adj_sub h) }

lemma coe_adj_sub (G' : subgraph G) (u v : G'.verts) (h : G'.coe.adj u v) : G.adj u v :=
G'.adj_sub h

/-- `G.'neighbor_set v` is the set of vertices adjacent to `v` in `G'`. -/
def neighbor_set (G' : subgraph G) (v : V) : set V := set_of (G'.adj v)

lemma neighbor_set_subset (G' : subgraph G) (v : V) : G'.neighbor_set v ⊆ G.neighbor_set v :=
λ w h, G'.adj_sub h

@[simp] lemma mem_neighbor_set (G' : subgraph G) (v w : V) : w ∈ G'.neighbor_set v ↔ G'.adj v w :=
by tauto

/-- The edge set of `G'` consists of a subset of edges of `G`. -/
def edge_set (G' : subgraph G) : set (sym2 V) := sym2.from_rel G'.sym

lemma edge_set_subset (G' : subgraph G) : G'.edge_set ⊆ G.edge_set :=
λ e, quotient.ind (λ e h, G'.adj_sub h) e

/-- The `incidence_set` is the set of edges incident to a given vertex. -/
def incidence_set (G' : subgraph G) (v : V) : set (sym2 V) := {e ∈ G'.edge_set | v ∈ e}

lemma incidence_set_subset_incidence_set (G' : subgraph G) (v : V) :
  G'.incidence_set v ⊆ G.incidence_set v :=
λ e h, ⟨G'.edge_set_subset h.1, h.2⟩

lemma incidence_set_subset (G' : subgraph G) (v : V) : G'.incidence_set v ⊆ G'.edge_set :=
λ _ h, h.1

@[simp]
lemma mem_edge_set {G' : subgraph G} {v w : V} : ⟦(v, w)⟧ ∈ G'.edge_set ↔ G'.adj v w :=
by refl

lemma edge_vert_mem {G' : subgraph G} {e : sym2 V} {v : V} (he : e ∈ G'.edge_set) (hv : v ∈ e) :
  v ∈ G'.verts :=
begin
  refine quotient.ind (λ e he hv, _) e he hv,
  cases e with v w,
  simp only [mem_edge_set] at he,
  cases sym2.mem_iff.mp hv with h h; subst h,
  { exact G'.edge_vert he, },
  { exact G'.edge_vert (G'.sym he), },
end

lemma adj_symm (G' : subgraph G) ⦃v w : V⦄ : G'.adj v w ↔ G'.adj w v :=
by split; apply G'.sym

@[simp]
lemma subgraph_of_coe_eq (G' : subgraph G) : G.subgraph_of G'.coe G'.coe_adj_sub  = G' :=
begin
  ext,
  { refl },
  { exact ⟨λ ⟨xel, yel, h⟩, h, λ h, ⟨G'.edge_vert h, G'.edge_vert (G'.sym h), h⟩⟩, },
end

@[simp]
lemma coe_subgraph_of_eq {V' : set V} (G' : simple_graph V')
  (h : ∀ (u v : V'), G'.adj u v → G.adj u v) :
  (G.subgraph_of G' h).coe = G' :=
begin
  ext u v,
  simp only [exists_prop, coe_adj, simple_graph.subgraph_of_adj, subtype.coe_eta],
  exact ⟨λ ⟨xel, yel, ha⟩, ha, λ ha, ⟨u.property, v.property, ha⟩⟩,
end

--instance (G' : subgraph G) : has_lift G'.V' V :=
--{ lift := λ v, v.val }



example : ∃ {V : Type u} {G : simple_graph V} {G' : subgraph G} (v w : G'.verts),
  ¬(G.adj v w ↔ G'.adj ↑v ↑w) :=
begin
  refine ⟨ulift bool, complete_graph _, ⟨set.univ, λ _ _, false, _, _, _⟩, _, _, _⟩,
  { simp },
  { simp },
  { tauto },
  { exact ⟨ulift.up tt, ⟨⟩⟩ },
  { exact ⟨ulift.up ff, ⟨⟩⟩ },
  { simp only [complete_graph, not_not, subtype.coe_mk, iff_false],
    intro a,
    cases ulift.up.inj a }
end

-- lemma is false, see counterexample ^
-- @[simp]
-- lemma adj_iff {G : simple_graph V} {G' : subgraph G} (v w : G'.V') : G.adj v w ↔ G'.adj' ↑v ↑w :=
-- sorry

/--
Give the vertex as an element of the subgraph's vertex type.
-/
@[reducible]
def vert (G' : subgraph G) (v : V) (h : v ∈ G'.verts) : G'.verts :=
subtype.mk v h

/--
Given a subgraph, replace the vertex set with an equal set.
The resulting subgraph is equal (see `copy_eq`).
-/
def copy (G' : subgraph G)
  (V'' : set V) (hV : V'' = G'.verts)
  (adj' : V → V → Prop) (hadj : adj' = G'.adj) :
  subgraph G :=
{ verts := V'',
  adj := adj',
  adj_sub := hadj.symm ▸ G'.adj_sub,
  edge_vert := hV.symm ▸ hadj.symm ▸ G'.edge_vert,
  sym := hadj.symm ▸ G'.sym }

lemma copy_eq (G' : subgraph G)
  (V'' : set V) (hV : V'' = G'.verts)
  (adj' : V → V → Prop) (hadj : adj' = G'.adj) :
  G'.copy V'' hV adj' hadj = G' :=
subgraph.ext _ _ hV hadj

/-- The union of two subgraphs. -/
def union (x y : subgraph G) : subgraph G :=
{ verts := x.verts ∪ y.verts,
  adj := λ v w, x.adj v w ∨ y.adj v w,
  adj_sub := λ v w h, or.cases_on h (λ h, x.adj_sub h) (λ h, y.adj_sub h),
  edge_vert := λ v w h, or.cases_on h (λ h, or.inl (x.edge_vert h)) (λ h, or.inr (y.edge_vert h)),
  sym := λ v w h, by rwa [x.adj_symm, y.adj_symm] }

/-- The intersection of two subgraphs. -/
def inter (x y : subgraph G) : subgraph G :=
{ verts := x.verts ∩ y.verts,
  adj := λ v w, x.adj v w ∧ y.adj v w,
  adj_sub := λ v w h, x.adj_sub h.1,
  edge_vert := λ v w h, ⟨x.edge_vert h.1, y.edge_vert h.2⟩,
  sym := λ v w h, by rwa [x.adj_symm, y.adj_symm] }

instance : has_union (subgraph G) := ⟨union⟩
instance : has_inter (subgraph G) := ⟨inter⟩

/-- The `top` subgraph is `G` as a subgraph of itself. -/
def top : subgraph G :=
{ verts := set.univ,
  adj := G.adj,
  adj_sub := λ v w h, h,
  edge_vert := λ v w h, set.mem_univ v,
  sym := G.sym }

/-- The `bot` subgraph is the subgraph with no vertices or edges. -/
def bot : subgraph G :=
{ verts := ∅,
  adj := λ v w, false,
  adj_sub := λ v w h, false.rec _ h,
  edge_vert := λ v w h, false.rec _ h,
  sym := λ u v h, h }

instance subgraph_inhabited : inhabited (subgraph G) := ⟨bot⟩

/-- The relation that one subgraph is a subgraph of another. -/
def is_subgraph (x y : subgraph G) : Prop := x.verts ⊆ y.verts ∧ ∀ ⦃v w : V⦄, x.adj v w → y.adj v w

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
  sup_le := λ x y z hxy hyz,
            ⟨set.union_subset hxy.1 hyz.1,
              (λ v w h, by { cases h, exact hxy.2 h, exact hyz.2 h })⟩,
  le_sup_left := λ x y, ⟨set.subset_union_left x.verts y.verts, (λ v w h, or.inl h)⟩,
  le_sup_right := λ x y, ⟨set.subset_union_right x.verts y.verts, (λ v w h, or.inr h)⟩,
  le_inf := λ x y z hxy hyz, ⟨set.subset_inter hxy.1 hyz.1, (λ v w h, ⟨hxy.2 h, hyz.2 h⟩)⟩,
  inf_le_left := λ x y, ⟨set.inter_subset_left x.verts y.verts, (λ v w h, h.1)⟩,
  inf_le_right := λ x y, ⟨set.inter_subset_right x.verts y.verts, (λ v w h, h.2)⟩ }

/-- The top of the `subgraph G` lattice is equivalent to the graph itself. -/
def top_equiv : (⊤ : subgraph G).coe ≃g G :=
{ to_fun := λ v, ↑v,
  inv_fun := λ v, ⟨v, by tidy⟩,
  left_inv := by tidy,
  right_inv := by tidy,
  map_rel_iff' := by tidy }

/-- The bottom of the `subgraph G` lattice is equivalent to the empty graph on the empty
vertex type. -/
def bot_equiv : (⊥ : subgraph G).coe ≃g (empty_graph empty) :=
{ to_fun := λ v, false.elim v.property,
  inv_fun := λ v, begin cases v, end,
  left_inv := by tidy,
  right_inv := by tidy,
  map_rel_iff' := by tidy }

/-- Given two subgraphs, one a subgraph of the other, there is an induced embedding of the
subgraphs as graphs. -/
def map {x y : subgraph G} (h : x ≤ y) : x.coe →g y.coe :=
{ to_fun := λ v, ⟨↑v, and.left h v.property⟩,
  map_rel' := λ v w hvw, h.2 hvw }

instance map.mono {x y : subgraph G} (h : x ≤ y) : hom.mono (map h) :=
⟨λ v w h, by { simp only [map, rel_hom.coe_fn_mk, subtype.mk_eq_mk] at h, exact subtype.ext h }⟩

/-- A subgraph of `G` embeds in `G`. -/
def map_top (x : subgraph G) : x.coe →g G :=
{ to_fun := λ v, v,
  map_rel' := λ v w hvw, x.adj_sub hvw }

instance map_top.mono {x : subgraph G} : hom.mono x.map_top :=
⟨λ v w h, subtype.ext h⟩

@[simp]
lemma map_top_to_fun {x : subgraph G} (v : x.verts) : x.map_top v = ↑v := rfl

lemma neighbor_set_subset_of_subgraph {x y : subgraph G} (h : x ≤ y) (v : V) :
  x.neighbor_set v ⊆ y.neighbor_set v :=
λ w h', h.2 h'

/--
The induced subgraph of a graph is the graph with a specified vertex
set along with all the edges whose endpoints lie in the set.
Note: `induced' V' = induced ⊤ V'`.  TODO decide whether to remove this function.
-/
def induced' (V' : set V) : subgraph G :=
{ verts := V',
  adj := λ v w, v ∈ V' ∧ w ∈ V' ∧ G.adj v w,
  adj_sub := λ v w ⟨hv, hw, he⟩, he,
  edge_vert := λ v w ⟨hv, hw, he⟩, hv,
  sym := λ v w ⟨hv, hw, he⟩, ⟨hw, hv, G.sym he⟩ }

def induced.map (V' : set V) : (induced' V').coe ↪g G :=
{ to_fun := λ v, ↑v,
  inj' := subtype.coe_injective,
  map_rel_iff' :=
  begin
    simp only [induced', coe_adj, function.embedding.coe_fn_mk, set_coe.forall],
    intros a ha,
    simp only [set_coe.forall, subtype.coe_mk],
    intros b hb,
    simp only [subtype.coe_mk],
    simp [induced'] at ha hb,
    split,
    { rintros ⟨ha2, hb2, hab⟩,
      apply hab, },
    { exact λ h, ⟨ha, hb, h⟩, },
  end }

/--
Given a subgraph `G'` and a vertex set `V'`, produces another subgraph on `V'` whose edges consist
of all those edges in `G'` whose endpoints lie in `V'`.  Note that the vertex set
might have vertices outside `V G'`.
-/
def induced (G' : subgraph G) (V' : set V) : subgraph G :=
{ verts := V',
  adj := λ v w, v ∈ V' ∧ w ∈ V' ∧ G'.adj v w,
  adj_sub := λ v w ⟨hv, hw, he⟩, G'.adj_sub he,
  edge_vert := λ v w ⟨hv, hw, he⟩, hv,
  sym := λ v w ⟨hv, hw, he⟩, ⟨hw, hv, G'.sym he⟩ }

lemma induced_is_subgraph (G' : subgraph G) (V' : set V) (h : V' ⊆ G'.verts) :
  G'.induced V' ≤ G' :=
by tidy

/--
The subgraph obtained by deleting a set `W` of vertices along with all the incident edges.
-/
def delete (G' : subgraph G) (W : set V) : subgraph G :=
{ verts := {v : V | v ∈ G'.verts ∧ v ∉ W},
  adj := λ v w, v ∉ W ∧ w ∉ W ∧ G'.adj v w,
  adj_sub := λ v w ⟨hv, hw, he⟩, G'.adj_sub he,
  edge_vert := λ v w ⟨hv, hw, he⟩, ⟨G'.edge_vert he, hv⟩,
  sym := λ v w ⟨hv, hw, he⟩, ⟨hw, hv, G'.sym he⟩ }

/--
The subgraph obtained by adding an edge between vertices a and b.  If `a = b`, then this
results in the same subgraph.
-/
def join_verts (G' : subgraph G) {a b : V} (hab : G.adj a b) : subgraph G :=
{ verts := G'.verts ∪ {a, b},
  adj := λ v w, (v = a ∧ w = b ∨ v = b ∧ w = a) ∨ G'.adj v w,
  adj_sub := λ v w h,
  begin
    cases h, cases h; rwa [h.1, h.2],
    exact (G.edge_symm a b).1 hab,
    exact G'.adj_sub h,
  end,
  edge_vert := λ v w h, by { cases h, swap, left, exact G'.edge_vert h, tidy },
  sym := λ v w h, by { cases h, { left, tidy, }, { right, exact G'.sym h, } } }

/--
A characterization of the neighbor set of a subgraph as a subset of the neighbor set of the graph.
-/
def subgraph_neighbor_set_in_graph (G' : subgraph G) (v : G'.verts) :
  G'.coe.neighbor_set v ≃ {w : G.neighbor_set (G'.map_top v) | G'.adj ↑v w} :=
{ to_fun := λ w, ⟨⟨↑w.1, G'.adj_sub w.2⟩, w.2⟩,
  inv_fun := λ w, ⟨⟨↑w.1, G'.edge_vert (G'.sym w.2)⟩, w.2⟩,
  left_inv := λ w, by simp,
  right_inv := λ w, by simp }

def subgraph_neighbor_set_in_supergraph {G' G'' : subgraph G} (h : G' ≤ G'') (v : G'.verts) :
  G'.coe.neighbor_set v ≃
  {w : G''.coe.neighbor_set (map h v) | G'.adj ↑v ↑w.val} :=
{ to_fun := λ w, ⟨⟨map h w, h.2 w.2⟩, w.2⟩,
  inv_fun := λ w, ⟨⟨↑w.1.1, G'.edge_vert (G'.sym w.2)⟩, w.2⟩,
  left_inv := λ w, by tidy,
  right_inv := λ w, by tidy }

instance neighbor_set.decidable_pred (G' : subgraph G) [h : decidable_rel G'.adj] (v : V) :
  decidable_pred (G'.neighbor_set v) :=
h v

instance finite_at {G' : subgraph G} (v : G'.verts) [decidable_rel G'.adj]
   [fintype (G.neighbor_set v)] : fintype (G'.neighbor_set v) :=
set.fintype_subset (G.neighbor_set v) (G'.neighbor_set_subset v)


/-- Not an instance because it depends on `h`. -/
def finite_at_subgraph {G' G'' : subgraph G} [decidable_rel G'.adj]
   (h : G' ≤ G'') (v : G'.verts) [hf : fintype (G''.neighbor_set v)] :
   fintype (G'.neighbor_set v) :=
set.fintype_subset (G''.neighbor_set v) (neighbor_set_subset_of_subgraph h v)

/-- The degree of a vertex in a subgraph.  Is 0 for vertices outside the subgraph. -/
def degree (G' : subgraph G) (v : V) [fintype (G'.neighbor_set v)] : ℕ :=
fintype.card (G'.neighbor_set v)

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

end subgraph

end simple_graph
