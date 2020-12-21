import combinatorics.simple_graph.basic
import combinatorics.simple_graph.hom

open simple_graph

/-!
# Subgraphs of a simple graph
-/

universe u
variables {V : Type u} (G : simple_graph V)

/--
A subgraph of a graph is a subset of vertices and a subset of edges
such that each endpoint of an edge is contained in the vertex set.
Subgraphs implement the `simple_graph` class.  They also form a bounded lattice.
Note: subgraphs could also have been defined as in `subgraph.of_edge_set'`.
We prove this alternative definition is equivalent.
-/
@[ext]
structure subgraph :=
(V' : set V)
(adj' : V → V → Prop)
(adj_sub : ∀ ⦃v w : V⦄, adj' v w → G.adj v w)
(edge_vert : ∀ ⦃v w : V⦄, adj' v w → v ∈ V')
(sym' : symmetric adj')

/--
The relation that one subgraph is a subgraph of another.
-/
def is_subgraph {V' : set V} (H : simple_graph V') : Prop := ∀ ⦃v w : V'⦄, H.adj v w → G.adj v w

-- hom instead of coercion?
/-def simple_graph.to_subgraph (G H : simple_graph V) [is_subgraph G H] : subgraph G :=
{ V' := V.to_set,
  adj' := _,
  adj_sub := _,
  edge_vert := _,
  sym' := _ }-/

namespace subgraph

variable {G}

/--
The edges of `G'` consist of a subset of edges of `G`.
-/
def edge_set' (G' : subgraph G) : set (sym2 V) := sym2.from_rel G'.sym'

@[simp]
lemma mem_edge_set' {G' : subgraph G} {v w : V} : ⟦(v, w)⟧ ∈ edge_set' G' ↔ G'.adj' v w :=
by refl

lemma edge_sub (G' : subgraph G) : G'.edge_set' ⊆ G.edge_set :=
begin
  intro e,
  refine quotient.rec_on_subsingleton e (λ e, _),
  cases e with v w,
  simp only [mem_edge_set', mem_edge_set],
  apply G'.adj_sub,
end

lemma has_verts (G' : subgraph G) : ∀ ⦃e : sym2 V⦄ ⦃v : V⦄, e ∈ G'.edge_set' → v ∈ e → v ∈ G'.V' :=
begin
  intro e,
  refine quotient.rec_on_subsingleton e (λ e, _),
  cases e with v w, intros u he hu,
  simp only [mem_edge_set'] at he,
  cases sym2.mem_iff.mp hu; subst u,
  exact G'.edge_vert he,
  exact G'.edge_vert (G'.sym' he),
end

lemma adj_symm' (G' : subgraph G) ⦃v w : V⦄ : G'.adj' v w ↔ G'.adj' w v :=
by { split; apply G'.sym' }

/--
Function lifting `G' : subgraph G` to `G' : simple_graph G.V`
-/
def to_simple_graph {G : simple_graph V} (G' : subgraph G) : simple_graph G'.V' :=
{ adj := λ v w, G'.adj' ↑v ↑w,
  sym := λ v w h, G'.sym' h,
  loopless := λ v h, loopless G v (G'.adj_sub h) }

/--
Coercion from `G' : subgraph G` to `G' : simple_graph G.V`
-/
def coe {V : Type*} {G : simple_graph V} (G' : subgraph G) : simple_graph G'.V' :=
{ adj := λ v w, G'.adj' ↑v ↑w,
  sym := λ v w h, G'.sym' h,
  loopless := λ v h, loopless G v (G'.adj_sub h) }

instance (G' : subgraph G) : has_lift G'.V' V :=
{ lift := λ v, v.val }

def to_subgraph {V' : set V} {G : simple_graph V} {G' : simple_graph V'} (h : is_subgraph G G') :
  subgraph G :=
{ V' := V',
  adj' := λ a b, ∃ (ha : a ∈ V') (hb : b ∈ V'), G'.adj ⟨a, ha⟩ ⟨b, hb⟩,
  adj_sub := λ v w ⟨hv, hw, hvw⟩, h hvw,
  edge_vert := λ v w ⟨hv, hw, hvw⟩, hv,
  sym' := λ a b ⟨ha, hb, hadj⟩, ⟨hb, ha, G'.sym hadj⟩ }

@[simp]
lemma adj_iff {G : simple_graph V} {G' : subgraph G} (v w : G'.V') : G.adj v w ↔ G'.adj' ↑v ↑w :=
sorry

/--
Give the vertex as an element of the subgraph's vertex type.
-/
@[reducible]
def vert (G' : subgraph G) (v : V) (h : v ∈ G'.V') : G'.V' :=
subtype.mk v h

@[simp]
lemma adj_iff_adj' {G' : subgraph G} {v w : V} (hv : v ∈ G'.V') (hw : w ∈ G'.V') :
  G.adj (G'.vert v hv) (G'.vert w hw) ↔ G'.adj' v w :=
begin
  split,
  intro h,
  rw adj_iff at h,
  simp at h,
  exact h,
  intro h,
  rw adj_iff,
  simp,
  exact h
end

/--
Given a subgraph, replace the vertex set with an equal set.
The resulting subgraph is equal (see `copy_eq`).
-/
def copy (G' : subgraph G)
(V'' : set V) (hV : V'' = G'.V')
(adj'' : V → V → Prop) (hadj : adj'' = G'.adj') :
  subgraph G :=
{ V' := V'',
  adj' := adj'',
  adj_sub := hadj.symm ▸ G'.adj_sub,
  edge_vert := hV.symm ▸ hadj.symm ▸ G'.edge_vert,
  sym' := hadj.symm ▸ G'.sym' }

lemma copy_eq (G' : subgraph G)
(V'' : set V) (hV : V'' = G'.V')
(adj'' : V → V → Prop) (hadj : adj'' = G'.adj') :
  G'.copy V'' hV adj'' hadj = G' :=
subgraph.ext _ _ hV hadj

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
  sym' := λ v w h, by rwa [x.adj_symm', y.adj_symm'] }

/--
The intersection of two subgraphs.
-/
def inter (x y : subgraph G) : subgraph G :=
{ V' := x.V' ∩ y.V',
  adj' := λ v w, x.adj' v w ∧ y.adj' v w,
  adj_sub := λ v w h, x.adj_sub h.1,
  edge_vert := λ v w h, ⟨x.edge_vert h.1, y.edge_vert h.2⟩,
  sym' := λ v w h, by rwa [x.adj_symm', y.adj_symm'] }

instance : has_union (subgraph G) := ⟨union⟩
instance : has_inter (subgraph G) := ⟨inter⟩

/--
The `top` subgraph is `G` as a subgraph of itself.
-/
def top : subgraph G :=
{ V' := set.univ,
  adj' := G.adj,
  adj_sub := λ v w h, h,
  edge_vert := λ v w h, set.mem_univ v,
  sym' := sym G }

/--
The `bot` subgraph is the subgraph with no vertices or edges.
-/
def bot : subgraph G :=
{ V' := ∅,
  adj' := λ v w, false,
  adj_sub := λ v w h, false.rec _ h,
  edge_vert := λ v w h, false.rec _ h,
  sym' := by tidy }

instance subgraph_inhabited : inhabited (subgraph G) := ⟨bot⟩

/--
The relation that one subgraph is a subgraph of another.
-/
def subgraph_is_subgraph (x y : subgraph G) : Prop := x.V' ⊆ y.V' ∧ ∀ ⦃v w : V⦄, x.adj' v w → y.adj' v w

instance : bounded_lattice (subgraph G) :=
{ le := subgraph_is_subgraph,
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
def top_equiv_graph : (⊤ : subgraph G).to_simple_graph ≃g G :=
{ to_fun := λ v, ↑v,
  inv_fun := λ v, ⟨v, by tidy⟩,
  left_inv := by tidy,
  right_inv := by tidy,
  map_rel_iff' := by tidy }

def bot_equiv_empty : (⊥ : subgraph G).to_simple_graph ≃g (empty_graph empty) :=
{ to_fun := λ v, false.elim v.property,
  inv_fun := λ v, begin cases v, end,
  left_inv := by tidy,
  right_inv := by tidy,
  map_rel_iff' := by tidy }

/--
Given two subgraphs, one a subgraph of the other, there is an induced embedding of the subgraphs as graphs.
-/
def map {x y : subgraph G} (h : x ≤ y) : x.to_simple_graph →g y.to_simple_graph :=
{ to_fun := λ v, ⟨↑v, and.left h v.property⟩,
  map_rel' :=
  begin
    rintros ⟨v, hv⟩ ⟨w, hw⟩ hvw,
    exact h.2 hvw,
  end }


/--
A subgraph of `G` embeds in `G`.
-/
def map_top (x : subgraph G) : x.to_simple_graph →g G :=
{ to_fun := λ v, v,
  map_rel' :=
  begin
    rintros ⟨v, hv⟩ ⟨w, hw⟩ hvw,
    rw subgraph.adj_iff_adj',
    exact hvw,
  end }

def map_top.injective {x : subgraph G} : function.injective x.map_top :=
λ v w h, subtype.ext h

instance map_top.mono {x : subgraph G} : hom.mono x.map_top :=
⟨map_top.injective⟩

@[simp]
lemma map_top_to_fun {x : subgraph G} (v : x.V') : x.map_top v = ↑v := rfl

/--
The induced subgraph of a graph is the graph with a specified vertex
set along with all the edges whose endpoints lie in the set.
Note: `induced' V' = induced ⊤ V'`.  TODO decide whether to remove this function.
-/
def induced' (V' : set V) : subgraph G :=
{ V' := V',
  adj' := λ v w, v ∈ V' ∧ w ∈ V' ∧ G.adj v w,
  adj_sub := λ v w ⟨hv, hw, he⟩, he,
  edge_vert := λ v w ⟨hv, hw, he⟩, hv,
  sym' := λ v w ⟨hv, hw, he⟩, ⟨hw, hv, sym G he⟩ }

def induced.map (V' : set V) : (induced' V').to_simple_graph ↪g G :=
{ to_fun := λ v, ↑v,
  inj' := subtype.coe_injective,
  map_rel_iff' :=
  begin
    simp [induced'],
    intros a ha,
    simp,
    intros b hb,
    simp,
    simp [induced'] at ha hb,
    split,
    intros h,
    rcases h with ⟨ha2, hb2, hab⟩,
    apply hab,

    intros h,
    refine ⟨_, _, _⟩,
    exact ha,
    exact hb,
    exact h,
  end }

/--
Given a subgraph `G'` and a vertex set `V'`, produces another subgraph on `V'` whose edges consist
of all those edges in `G'` whose endpoints lie in `V'`.  Note that the vertex set
might have vertices outside `V G'`.
-/
def induced (G' : subgraph G) (V' : set V) : subgraph G :=
{ V' := V',
  adj' := λ v w, v ∈ V' ∧ w ∈ V' ∧ G'.adj' v w,
  adj_sub := λ v w ⟨hv, hw, he⟩, G'.adj_sub he,
  edge_vert := λ v w ⟨hv, hw, he⟩, hv,
  sym' := λ v w ⟨hv, hw, he⟩, ⟨hw, hv, G'.sym' he⟩ }

lemma induced_is_subgraph (G' : subgraph G) (V' : set V) (h : V' ⊆ G'.V') :
  G'.induced V' ≤ G' :=
by tidy

/--
The subgraph obtained by deleting a set `W` of vertices along with all the incident edges.
-/
def delete (G' : subgraph G) (W : set V) : subgraph G :=
{ V' := {v : V | v ∈ G'.V' ∧ v ∉ W},
  adj' := λ v w, v ∉ W ∧ w ∉ W ∧ G'.adj' v w,
  adj_sub := λ v w ⟨hv, hw, he⟩, G'.adj_sub he,
  edge_vert := λ v w ⟨hv, hw, he⟩, ⟨G'.edge_vert he, hv⟩,
  sym' := λ v w ⟨hv, hw, he⟩, ⟨hw, hv, G'.sym' he⟩ }

/--
The subgraph obtained by adding an edge between vertices a and b.  If `a = b`, then this
results in the same subgraph.
-/
def join_verts (G' : subgraph G) {a b : V} (hab : G.adj a b) : subgraph G :=
{ V' := G'.V' ∪ {a, b},
  adj' := λ v w, (v = a ∧ w = b ∨ v = b ∧ w = a) ∨ G'.adj' v w,
  adj_sub := λ v w h,
  begin
    cases h, cases h; rwa [h.1, h.2],
    exact (G.edge_symm a b).1 hab,
    exact G'.adj_sub h,
  end,
  edge_vert := λ v w h, by { cases h, swap, left, exact G'.edge_vert h, tidy },
  sym' := λ v w h, by { cases h, { left, tidy, }, { right, exact G'.sym' h, } } }

/--
A characterization of the neighbor set of a subgraph as a subset of the neighbor set of the graph.
-/
def subgraph_neighbor_set_in_graph (G' : subgraph G) (v : G'.V') :
  (G'.to_simple_graph).neighbor_set v ≃ {w : G.neighbor_set (G'.map_top v) | G'.adj' ↑v w} :=
{ to_fun := λ w, ⟨⟨↑w.1, G'.adj_sub w.2⟩, w.2⟩,
  inv_fun := λ w, ⟨⟨↑w.1, G'.edge_vert (G'.sym' w.2)⟩, w.2⟩,
  left_inv := λ w, by simp,
  right_inv := λ w, by simp }

def subgraph_neighbor_set_in_supergraph {G' G'' : subgraph G} (h : G' ≤ G'') (v : G'.V') :
  (G'.to_simple_graph).neighbor_set v ≃
  {w : (G''.to_simple_graph).neighbor_set (map h v) | G'.adj' ↑v ↑w.val} :=
{ to_fun := λ w, ⟨⟨map h w, h.2 w.2⟩, w.2⟩,
  inv_fun := λ w, ⟨⟨↑w.1.1, G'.edge_vert (G'.sym' w.2)⟩, w.2⟩,
  left_inv := λ w, by tidy,
  right_inv := λ w, by tidy }

/--
This instance also provides finiteness of subgraphs when `[decidable_rel (adj G)]` and `[fintype (V G)]`.
-/
instance finite_at
  {G' : subgraph G} [decidable_rel G'.adj'] (v : G'.V') [fintype ((G'.to_simple_graph).neighbor_set v)] :
  fintype (G.neighbor_set v) :=
fintype.of_equiv _ (subgraph_neighbor_set_in_graph G' v).symm

/--
Not an instance because it depends on `h`.
-/
def finite_at_subgraph {G' G'' : subgraph G} [decidable_rel G'.adj'] [decidable_rel G''.adj']
  (h : G' ≤ G'') (v : G'.V') [hf : fintype (G.neighbor_set (map h v))] :
  fintype (G.neighbor_set v) :=
fintype.of_equiv _ (subgraph_neighbor_set_in_supergraph h v).symm






end subgraph
