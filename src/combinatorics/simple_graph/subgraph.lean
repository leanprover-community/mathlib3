import combinatorics.simple_graph.basic
import combinatorics.simple_graph.hom
open simple_graph

/-!
# Subgraphs of a simple graph
-/

variables (G : simple_graph)

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

lemma edge_sub (G' : subgraph G) : G'.edge_set' ⊆ G.edge_set :=
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

def to_simple_graph {G : simple_graph} (G' : subgraph G) : simple_graph_on G'.V' :=
{ adj := λ v w, G'.adj' ↑v ↑w,
  symm' := λ v w h, G'.symm' h,
  loopless' := λ ⟨v, _⟩ h, loopless G v (G'.adj_sub h) }

instance : has_coe_to_simple_graph (subgraph G) :=
⟨λ G', { V := G'.V', graph := G'.to_simple_graph }⟩

instance (G' : subgraph G) : has_lift (V ↟G') (V G) :=
{ lift := λ v, v.val }

@[simp]
lemma adj_iff {G : simple_graph} {G' : subgraph G} (v w : V ↟G') : v ~g w ↔ G'.adj' ↑v ↑w :=
by tidy

/--
Give the vertex as an element of the subgraph's vertex type.
-/
@[reducible]
def vert (G' : subgraph G) (v : V G) (h : v ∈ G'.V') : V ↟G' :=
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
protected structure of_edge_set' (G : simple_graph) :=
(V' : set (V G))
(edge_set' : set (sym2 (V G)))
(edge_sub : edge_set' ⊆ G.edge_set)
(has_verts : ∀ ⦃e : sym2 (V G)⦄ ⦃v : V G⦄, e ∈ edge_set' → v ∈ e → v ∈ V')

protected
def of_edge_set'.to_simple_graph (G' : of_edge_set' G) : simple_graph_on G'.V' :=
{ adj := λ v w, ⟦(↑v, ↑w)⟧ ∈ G'.edge_set',
  symm' := λ v w h, by rwa sym2.eq_swap,
  loopless' := λ ⟨v, _⟩ h, loopless G v (sym2.from_rel_prop.mp (G'.edge_sub h)) }

instance of_edge_set'.coe : has_coe_to_simple_graph (of_edge_set' G) :=
{ coe := λ G', ⟨G'.V', G'.to_simple_graph⟩ }

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
def iso_of_edge_set' (G' : subgraph G) : ↟G' ≃g ↟(subgraph.equiv_of_edge_set' G') :=
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
  adj' := G.adj,
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
def top_equiv_graph : ↟(⊤ : subgraph G) ≃g G :=
{ to_fun := λ v, ↑v,
  inv_fun := λ v, ⟨v, by tidy⟩,
  left_inv := by tidy,
  right_inv := by tidy,
  map_rel_iff' := by tidy }

def bot_equiv_empty : ↟(⊥ : subgraph G) ≃g ↟(empty_graph empty) :=
{ to_fun := λ v, false.elim v.property,
  inv_fun := λ v, begin cases v, end,
  left_inv := by tidy,
  right_inv := by tidy,
  map_rel_iff' := by tidy }

/--
Given two subgraphs, one a subgraph of the other, there is an induced embedding of the subgraphs as graphs.
-/
def map {x y : subgraph G} (h : x ≤ y) : ↟x →g ↟y :=
{ to_fun := λ v, ⟨↑v, and.left h v.property⟩,
  map_rel' := λ v w hvw, begin
    cases v with v hv, cases w with w hw,
    change _ ~g _,
    apply (adj_iff_adj' _ _).mpr, 
    apply h.2,
    exact (adj_iff_adj' _ _).mp hvw,
  end }

def map.injective {x y : subgraph G} (h : x ≤ y) : function.injective (map h) :=
λ v w h, subtype.ext (subtype.mk_eq_mk.mp h)

instance map.mono {x y : subgraph G} (h : x ≤ y) : hom.mono (map h) :=
⟨map.injective h⟩

/--
A subgraph of `G` embeds in `G`.
-/
def map_top (x : subgraph G) : ↟x →g G :=
{ to_fun := λ v, ↑v,
  map_rel' := λ v w hvw, begin
    cases v with v hv, cases w with w hw,
    rw subgraph.adj_iff_adj' at hvw,
    exact x.adj_sub hvw,
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
def induced' (V' : set (V G)) : subgraph G :=
{ V' := V',
  adj' := λ v w, v ∈ V' ∧ w ∈ V' ∧ v ~g w,
  adj_sub := λ v w ⟨hv, hw, he⟩, he,
  edge_vert := λ v w ⟨hv, hw, he⟩, hv,
  symm' := λ v w ⟨hv, hw, he⟩, ⟨hw, hv, symm G he⟩ }

def induced.map (V' : set (V G)) : ↟(induced' V') ↪g G :=
{ to_fun := λ v, ↑v,
  inj' := subtype.coe_injective,
  map_rel_iff' := begin
    simp [induced'],
    rintros ⟨a, ha⟩ ⟨b, hb⟩, simp,
    simp [induced'] at ha hb, cc,
  end }

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

lemma induced_is_subgraph (G' : subgraph G) (V' : set (V G)) (h : V' ⊆ G'.V') :
  G'.induced V' ≤ G' :=
by tidy

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
def subgraph_neighbor_set_in_graph (G' : subgraph G) (v : V ↟G') :
  neighbor_set v ≃ {w : neighbor_set (G'.map_top v) | G'.adj' ↑v w} :=
{ to_fun := λ w, ⟨⟨↑w.1, G'.adj_sub w.2⟩, w.2⟩,
  inv_fun := λ w, ⟨⟨↑w.1, G'.edge_vert (G'.symm' w.2)⟩, w.2⟩,
  left_inv := λ w, by simp,
  right_inv := λ w, by simp }

def subgraph_neighbor_set_in_supergraph {G' G'' : subgraph G} (h : G' ≤ G'') (v : V ↟G') :
  neighbor_set v ≃ {w : neighbor_set (map h v) | G'.adj' ↑v ↑w.val} :=
{ to_fun := λ w, ⟨⟨map h w, h.2 w.2⟩, w.2⟩,
  inv_fun := λ w, ⟨⟨↑w.1.1, G'.edge_vert (G'.symm' w.2)⟩, w.2⟩,
  left_inv := λ w, by tidy,
  right_inv := λ w, by tidy }

/--
This instance also provides finiteness of subgraphs when `[decidable_rel (adj G)]` and `[fintype (V G)]`.
-/
instance finite_at
  {G' : subgraph G} [decidable_rel G'.adj'] (v : V ↟G') [fintype (neighbor_set (G'.map_top v))] :
  fintype (neighbor_set v) :=
fintype.of_equiv _ (subgraph_neighbor_set_in_graph G' v).symm

/--
Not an instance because it depends on `h`.
-/
def finite_at_subgraph {G' G'' : subgraph G} [decidable_rel G'.adj'] [decidable_rel G''.adj']
  (h : G' ≤ G'') (v : V ↟G') [hf : fintype (neighbor_set (map h v))] :
  fintype (neighbor_set v) :=
fintype.of_equiv _ (subgraph_neighbor_set_in_supergraph h v).symm


lemma degree_le_top {G' : subgraph G} [decidable_rel G'.adj']
  (v : V ↟G') [fintype (neighbor_set (G'.map_top v))] :
  degree v ≤ degree (G'.map_top v) :=
begin
  repeat {rw ←card_neighbor_set_eq_degree},
  have h := hom.map_neighbor_set.inj G'.map_top v,
  apply fintype.card_le_of_injective _ h,
end

lemma degree_le {G' G'' : subgraph G} [decidable_rel G'.adj'] [decidable_rel G''.adj']
  (h : G' ≤ G'') (v : V ↟G') [fintype (neighbor_set v)] [fintype (neighbor_set (map h v))] :
  degree v ≤ degree (map h v) :=
begin
  repeat {rw ←card_neighbor_set_eq_degree},
  have h := hom.map_neighbor_set.inj (map h) v,
  exact fintype.card_le_of_injective _ h,
end

def is_cycle {G : simple_graph} (G' : subgraph G) : Prop :=
∃ (n : ℕ) (h : 3 ≤ n) (f : ↟(cycle_graph n h) →g ↟G'), hom.mono f

def cycles (G : simple_graph) : set (subgraph G) := { G' | is_cycle G' }

end subgraph
