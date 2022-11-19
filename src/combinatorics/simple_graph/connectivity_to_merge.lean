/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.acyclic
/-!

# Graph connectivity

## Main definitions


* `simple_graph.edge_connected` for k-edge-connectivity of a graph

## Tags
walks, trails, paths, circuits, cycles

-/

/-- this doesn't seem to be used in this file anymore (was a simp lemma) -/
lemma function.injective.mem_list_map_iff {α β : Type*} {f : α → β} {l : list α} {a : α}
  (hf : function.injective f) :
  (∃ (a' : α), a' ∈ l ∧ f a' = f a) ↔ a ∈ l :=
begin
  split,
  { rintro ⟨a', ha', h⟩,
    cases hf h,
    assumption },
  { intro h,
    exact ⟨_, h, rfl⟩ },
end

universes u

open function

namespace simple_graph
variables {V : Type u} {V' : Type*} (G : simple_graph V)

/-! ### Walks to paths -/


namespace walk
variables {G} [decidable_eq V]

/-- Whether or not the path `p` is a prefix of the path `q`. -/
def prefix_of {u v w : V} (p : G.walk u v) (q : G.walk u w) := ∃ (r : G.walk v w), p.append r = q

@[simp] lemma prefix_of_nil {u v : V} (q : G.walk u v) : (nil : G.walk u u).prefix_of q := ⟨q, rfl⟩

@[simp] lemma prefix_of_cons_nil {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  ¬ (cons h p).prefix_of (nil : G.walk u u) :=
by rintro ⟨r, -, -⟩

@[simp] lemma prefix_of_cons_cons {u v v' w x : V}
  (h : G.adj u v) (p : G.walk v w) (h' : G.adj u v') (q : G.walk v' x) :
  (cons h p).prefix_of (cons h' q) ↔ ∃ (hv : v = v'), (p.copy hv rfl).prefix_of q :=
begin
  split,
  { rintro ⟨r, hr⟩,
    rw [cons_append] at hr,
    unify_equations hr,
    use [rfl, r],
    refl, },
  { rintro ⟨rfl, r, rfl⟩,
    use [r],
    refl, }
end

def prefix_of' : Π {u v w : V} (p : G.walk u v) (q : G.walk u w), bool
| u v w nil _ := true
| u v w (cons _ _) nil := false
| u v w (cons' _ x _ r p) (@cons _ _ _ y _ s q) :=
  if h : x = y
  then by { subst y, exact prefix_of' p q }
  else false

instance {u v w : V} (p : G.walk u v) (q : G.walk u w) : decidable (p.prefix_of q) :=
decidable_of_bool (p.prefix_of' q)
begin
  induction p generalizing q,
  { simp [prefix_of'], },
  { cases q,
    { simp [prefix_of'], },
    { simp only [prefix_of', to_bool_false_eq_ff, prefix_of_cons_cons],
      split_ifs,
      { cases h,
        simp [p_ih], },
      { simp only [coe_sort_ff, false_iff, not_exists],
        rintro rfl,
        exact absurd rfl h, }, } }
end

end walk


namespace path
variables {G} {G' : simple_graph V'}

lemma singleton_edge_mem {u v : V} (h : G.adj u v) : ⟦(u, v)⟧ ∈ (singleton h : G.walk u v).edges :=
by simp [singleton]

lemma support_count_eq_one [decidable_eq V] {u v w : V} {p : G.path u v}
  (hw : w ∈ (p : G.walk u v).support) : (p : G.walk u v).support.count w = 1 :=
list.count_eq_one_of_mem p.property.support_nodup hw

lemma edges_count_eq_one [decidable_eq V] {u v : V} {p : G.path u v} (e : sym2 V)
  (hw : e ∈ (p : G.walk u v).edges) : (p : G.walk u v).edges.count e = 1 :=
list.count_eq_one_of_mem p.property.to_trail.edges_nodup hw

lemma nonempty_path_not_loop {v : V} {e : sym2 V} (p : G.path v v)
  (h : e ∈ walk.edges (p : G.walk v v)) : false :=
begin
  cases p with p hp,
  cases p,
  { exact h },
  { cases hp,
    simpa using hp_support_nodup },
end

end path

/-! ## `reachable` and `connected` -/


variables (G)

/-- A graph is *k-edge-connected* if it remains connected whenever
fewer than k edges are removed. -/
def edge_connected (k : ℕ) : Prop :=
∀ (s : finset (sym2 V)), ↑s ⊆ G.edge_set → s.card < k → (G.delete_edges ↑s).connected

variables {G}

lemma edge_connected.to_preconnected {k : ℕ} (h : G.edge_connected k) (hk : 0 < k) :
  G.preconnected :=
begin
  intros v w,
  simpa using (h ∅ (by simp) (by simp [hk])).preconnected v w,
end

lemma edge_connected.to_connected {k : ℕ} (h : G.edge_connected k) (hk : 0 < k) : G.connected :=
let C' := h ∅ (by simp) (by simp [hk]) in
{ preconnected := by simpa using C'.preconnected,
  nonempty := C'.nonempty }

variables (G)


namespace subgraph
variables {G} (H : subgraph G)

/-- An edge of a subgraph is a bridge edge if, after removing it, its incident vertices
are no longer reachable.  The vertices are meant to be adjacent.

Since this is for simple graphs, we use the endpoints of the vertices as the edge itself.

Implementation note: this uses `simple_graph.subgraph.spanning_coe` since adding
vertices to a subgraph does not change reachability, and it is simpler than
dealing with the dependent types from `simple_graph.subgraph.coe`. -/
def is_bridge (v w : V) : Prop :=
¬(H.delete_edges {⟦(v, w)⟧}).spanning_coe.reachable v w

end subgraph

/-- Get the unique path between two vertices in the tree. -/
noncomputable abbreviation tree_path (h : G.is_tree) (v w : V) : G.path v w :=
⟨((is_tree_iff_exists_unique_path.mp h).2 v w).some,
  ((is_tree_iff_exists_unique_path.mp h).2 v w).some_spec.1⟩

lemma tree_path_spec {h : G.is_tree} {v w : V} (p : G.path v w) : p = G.tree_path h v w :=
begin
  cases p,
  have := ((is_tree_iff_exists_unique_path.mp h).2 v w).some_spec,
  simp only [this.2 p_val p_property],
end

/-- The tree metric, which is the length of the path between any two vertices.

Fixing a vertex as the root, then `G.tree_dist h root` gives the depth of each node with
respect to the root. -/
noncomputable def tree_dist (h : G.is_tree) (v w : V) : ℕ :=
walk.length (G.tree_path h v w : G.walk v w)

variables {G}

/-- Given a tree and a choice of root, then we can tell whether a given ordered
pair of adjacent vertices `v` and `w` is *rootward* based on whether or not `w` lies
on the path from `v` to the root.

This gives paths a canonical orientation in a rooted tree. -/
def is_rootward (h : G.is_tree) (root : V) (v w : V) : Prop :=
G.adj v w ∧ ⟦(v, w)⟧ ∈ (G.tree_path h v root : G.walk v root).edges

lemma is_rootward_antisymm (h : G.is_tree) (root : V) : anti_symmetric (is_rootward h root) :=
begin
  classical,
  rintros v w ⟨ha, hvw⟩ ⟨ha', hwv⟩,
  by_contra hne,
  rw sym2.eq_swap at hwv,
  have hv := walk.fst_mem_support_of_mem_edges _ hwv,
  have h' := h.2,
  rw is_acyclic_iff_path_unique at h',
  specialize h'
    (G.tree_path h v root)
    ⟨walk.drop_until _ _ hv, walk.is_path.drop_until _ (path.is_path _) _⟩,
  have hs := congr_arg (λ p, multiset.count w ↑(walk.support p)) (walk.take_spec _ hv),
  dsimp only at hs,
  rw h' at hvw,
  have hw := walk.fst_mem_support_of_mem_edges _ hwv,
  rw walk.coe_support_append' at hs,
  have : multiset.count w {v} = 0,
  { simp only [multiset.cons_zero, multiset.count_eq_zero, multiset.mem_singleton],
    simpa using ne.symm hne },
  rw [multiset.count_sub, this, tsub_zero, multiset.count_add] at hs,
  simp_rw [multiset.coe_count] at hs,
  rw [path.support_count_eq_one] at hs,
  swap, { simp },
  rw ←subtype.coe_mk (walk.take_until _ _ _) at hs,
  swap, { apply walk.is_path.take_until, apply path.is_path },
  rw ←subtype.coe_mk (walk.drop_until _ _ _) at hs,
  swap, { apply walk.is_path.drop_until, apply path.is_path },
  rw [path.support_count_eq_one, path.support_count_eq_one] at hs,
  simpa using hs,
  apply walk.fst_mem_support_of_mem_edges _ (by { rw [sym2.eq_swap], exact hvw }),
  apply walk.start_mem_support,
end

lemma is_rootward_or_reverse (h : G.is_tree) (root : V) {v w : V} (hvw : G.adj v w) :
  is_rootward h root v w ∨ is_rootward h root w v :=
begin
  classical,
  have h' := h.2,
  rw is_acyclic_iff_path_unique at h',
  by_contra hr,
  simp only [is_rootward] at hr,
  push_neg at hr,
  rcases hr with ⟨hrv, hrw⟩,
  specialize hrv hvw,
  specialize hrw (G.symm hvw),
  let p := (G.tree_path h v root : G.walk v root).append
           (G.tree_path h w root : G.walk w root).reverse,
  specialize h' (path.singleton hvw) p.to_path,
  have hp := walk.edges_to_path_subset p,
  rw [←h', walk.edges_append, walk.edges_reverse] at hp,
  specialize hp (path.singleton_edge_mem hvw),
  rw [list.mem_append, list.mem_reverse] at hp,
  rw sym2.eq_swap at hrw,
  cases hp; simpa only [hrv, hrw] using hp,
end

open fintype

/-- Get the next edge after vertext `v` on a path `p` from `v` to vertex `w`. -/
def next_edge (G : simple_graph V) : ∀ (v w : V) (h : v ≠ w) (p : G.walk v w), G.incidence_set v
| v w h walk.nil := (h rfl).elim
| v w h (@walk.cons _ _ _ u _ hvw _) := ⟨⟦(v, u)⟧, hvw, sym2.mem_mk_left _ _⟩

lemma eq_next_edge_if_mem_path {u v w : V}
  (hne : u ≠ v) (hinc : ⟦(u, w)⟧ ∈ G.incidence_set u)
  (p : G.path u v) (h : ⟦(u, w)⟧ ∈ (p : G.walk u v).edges) :
  G.next_edge u v hne p = ⟨⟦(u, w)⟧, hinc⟩ :=
begin
  cases p with p hp,
  cases p,
  { exact (hne rfl).elim },
  { cases hp,
    simp at hp_support_nodup,
    simp only [next_edge, subtype.mk_eq_mk, subtype.coe_mk],
    congr,
    simp only [list.mem_cons_iff, subtype.coe_mk, simple_graph.walk.edges_cons, sym2.eq_iff] at h,
    cases h,
    { obtain (⟨_,rfl⟩|⟨rfl,rfl⟩) := h; refl },
    { have h := walk.fst_mem_support_of_mem_edges _ h,
      exact (hp_support_nodup.1 h).elim } },
end

lemma next_edge_mem_edges (G : simple_graph V) (v w : V) (h : v ≠ w) (p : G.walk v w) :
  (G.next_edge v w h p : sym2 V) ∈ p.edges :=
begin
  cases p with p hp,
  { exact (h rfl).elim },
  { simp only [next_edge, list.mem_cons_iff, walk.edges_cons, subtype.coe_mk],
    left,
    refl,},
end

lemma is_tree.card_edges_eq_card_vertices_sub_one
  [fintype G.edge_set] [fintype V] [nonempty V] (h : G.is_tree) :
  card G.edge_set = card V - 1 :=
begin
  classical,
  have root := classical.arbitrary V,
  rw ←set.card_ne_eq root,
  let f : {v | v ≠ root} → G.edge_set := λ v,
    ⟨G.next_edge v root v.property (G.tree_path h v root),
     G.incidence_set_subset _ (subtype.mem _)⟩,
  have finj : function.injective f,
  { rintros ⟨u₁, h₁⟩ ⟨u₂, h₂⟩,
    by_cases hne : u₁ = u₂,
    { simp [hne] },
    simp only [subtype.mk_eq_mk, subtype.coe_mk],
    generalize he₁ : G.next_edge _ _ _ _ = e₁,
    generalize he₂ : G.next_edge _ _ _ _ = e₂,
    cases e₁ with e₁ heu₁,
    cases e₂ with e₂ heu₂,
    simp only [subtype.coe_mk],
    rintro rfl,
    cases heu₁ with heu₁_edge heu₁_adj,
    cases heu₂ with heu₂_edge heu₂_adj,
    simp only [subtype.coe_mk] at heu₁_adj heu₂_adj,
    have e_is : e₁ = ⟦(u₁, u₂)⟧,
    { induction e₁ using sym2.ind with v₁ w₁,
      simp only [sym2.mem_iff] at heu₁_adj heu₂_adj,
      obtain (rfl|rfl) := heu₁_adj;
      obtain (rfl|rfl) := heu₂_adj;
      try { exact (hne rfl).elim };
      simp [sym2.eq_swap] },
    subst e₁,
    apply is_rootward_antisymm h root,
    { split,
      { exact heu₂_edge, },
      { convert G.next_edge_mem_edges _ _ h₁ _,
        erw he₁,
        refl } },
    { split,
      { exact G.symm heu₂_edge, },
      { convert G.next_edge_mem_edges _ _ h₂ _,
        erw he₂, simp [sym2.eq_swap] } } },
  have fsurj : function.surjective f,
  { rintro ⟨e, he⟩,
    induction e using sym2.ind with u₁ u₂,
    cases is_rootward_or_reverse h root he with hr hr,
    { use u₁,
      { rintro rfl,
        dsimp only [is_rootward] at hr,
        exact path.nonempty_path_not_loop _ hr.2, },
      { cases hr,
        simp only [f],
        erw eq_next_edge_if_mem_path _ ⟨he, _⟩ _ hr_right;
        simp [he] } },
    { use u₂,
      { rintro rfl,
        dsimp only [is_rootward] at hr,
        exact path.nonempty_path_not_loop _ hr.2, },
      { cases hr,
        simp only [f],
        erw eq_next_edge_if_mem_path _ ⟨_ , _⟩ _ hr_right;
        simp [he, sym2.eq_swap] } } },
  exact (card_of_bijective ⟨finj, fsurj⟩).symm,
end

end simple_graph
