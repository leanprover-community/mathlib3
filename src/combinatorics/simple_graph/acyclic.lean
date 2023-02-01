/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.subgraph
/-!

# Acyclic graphs and trees

This module introduces *acyclic graphs* (a.k.a. *forests*) and *trees*.

## Main definitions

* `simple_graph.is_acyclic` is a predicate for a graph having no cyclic walks
* `simple_graph.is_tree` is a predicate for a graph being a tree (a connected acyclic graph)

## Main statements

* `simple_graph.is_acyclic_iff_path_unique` characterizes acyclicity in terms of uniqueness of
  paths between pairs of vertices.
* `simple_graph.is_acyclic_iff_forall_edge_is_bridge` characterizes acyclicity in terms of every
  edge being a bridge edge.
* `simple_graph.is_tree_iff_exists_unique_path` characterizes trees in terms of existence and
  uniqueness of paths between pairs of vertices from a nonempty vertex type.

## References

The structure of the proofs for `simple_graph.is_acyclic` and `simple_graph.is_tree`, including
supporting lemmas about `simple_graph.is_bridge`, generally follows the high-level description
for these theorems for multigraphs from [Chou1994].

## Tags

acyclic graphs, trees
-/

universes u v

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/-- A graph is *acyclic* (or a *forest*) if it has no cycles. -/
def is_acyclic : Prop := ∀ (v : V) (c : G.walk v v), ¬c.is_cycle

/-- A *tree* is a connected acyclic graph. -/
@[mk_iff, protect_proj] structure is_tree : Prop :=
(is_connected : G.connected)
(is_acyclic : G.is_acyclic)

variables {G}

-- i think this can be generalized to say that there is a unique path between some u and v
-- then there is no cycle between them, useful in other proofs
lemma is_acyclic_iff_forall_adj_is_bridge :
  G.is_acyclic ↔ ∀ ⦃v w : V⦄, G.adj v w → G.is_bridge ⟦(v, w)⟧ :=
begin
  simp_rw [is_bridge_iff_adj_and_forall_cycle_not_mem],
  split,
  { intros ha v w hvw,
    apply and.intro hvw,
    intros u p hp,
    exact absurd hp (ha _ p), },
  { rintros hb v (_ | @⟨_, _, _, ha, p⟩) hp,
    { exact hp.not_of_nil },
    { specialize hb ha,
      apply hb.2 _ hp,
      rw [walk.edges_cons],
      apply list.mem_cons_self } },
end

lemma is_acyclic_iff_forall_edge_is_bridge :
  G.is_acyclic ↔ ∀ ⦃e⦄, e ∈ G.edge_set → G.is_bridge e :=
by simp [is_acyclic_iff_forall_adj_is_bridge, sym2.forall]

lemma is_acyclic.path_unique {G : simple_graph V} (h : G.is_acyclic) {v w : V} (p q : G.path v w) :
  p = q :=
begin
  obtain ⟨p, hp⟩ := p,
  obtain ⟨q, hq⟩ := q,
  simp only,
  induction p with u pu pv pw ph p ih generalizing q,
  { rw walk.is_path_iff_eq_nil at hq,
    exact hq.symm, },
  { rw is_acyclic_iff_forall_adj_is_bridge at h,
    specialize h ph,
    rw is_bridge_iff_adj_and_forall_walk_mem_edges at h,
    replace h := h.2 (q.append p.reverse),
    simp only [walk.edges_append, walk.edges_reverse, list.mem_append, list.mem_reverse] at h,
    cases h,
    { cases q,
      { simpa [walk.is_path_def] using hp },
      { rw walk.cons_is_path_iff at hp hq,
        simp only [walk.edges_cons, list.mem_cons_iff, sym2.eq_iff] at h,
        obtain (⟨h,rfl⟩ | ⟨rfl,rfl⟩) | h := h,
        { rw [ih hp.1 _ hq.1] },
        { simpa using hq },
        { exact absurd (walk.fst_mem_support_of_mem_edges _ h) hq.2 } } },
    { rw walk.cons_is_path_iff at hp,
      exact absurd (walk.fst_mem_support_of_mem_edges _ h) hp.2 } }
end

lemma is_acyclic_of_path_unique (h : ∀ (v w : V) (p q : G.path v w), p = q) : G.is_acyclic :=
begin
  intros v c hc,
  simp only [walk.is_cycle_def, ne.def] at hc,
  cases c,
  { exact absurd rfl hc.2.1 },
  { simp only [walk.cons_is_trail_iff, not_false_iff, walk.support_cons,
      list.tail_cons, true_and] at hc,
    specialize h _ _ ⟨c_p, by simp only [walk.is_path_def, hc.2]⟩ (path.singleton (G.symm c_h)),
    simp only [path.singleton] at h,
    simpa [-quotient.eq, sym2.eq_swap, h] using hc },
end

lemma is_acyclic_iff_path_unique : G.is_acyclic ↔ ∀ ⦃v w : V⦄ (p q : G.path v w), p = q :=
⟨is_acyclic.path_unique, is_acyclic_of_path_unique⟩

lemma is_tree_iff_exists_unique_path :
  G.is_tree ↔ nonempty V ∧ ∀ (v w : V), ∃! (p : G.walk v w), p.is_path :=
begin
  classical,
  rw [is_tree_iff, is_acyclic_iff_path_unique],
  split,
  { rintro ⟨hc, hu⟩,
    refine ⟨hc.nonempty, _⟩,
    intros v w,
    let q := (hc v w).some.to_path,
    use q,
    simp only [true_and, path.is_path],
    intros p hp,
    specialize hu ⟨p, hp⟩ q,
    exact subtype.ext_iff.mp hu, },
  { unfreezingI { rintro ⟨hV, h⟩ },
    refine ⟨connected.mk _, _⟩,
    { intros v w,
      obtain ⟨p, hp⟩ := h v w,
      exact p.reachable, },
    { rintros v w ⟨p, hp⟩ ⟨q, hq⟩,
      simp only [unique_of_exists_unique (h v w) hp hq] } },
end

-- let's do prufer codes, finally

variables (n : ℕ) (T : simple_graph (fin n)) (h : T.is_tree)

/-- A subgraph is acyclic if it is acyclic as a simple graph. -/
abbreviation subgraph.is_acyclic (H : G.subgraph) : Prop := H.coe.is_acyclic

instance  (G' H : subgraph G) (h : G' ≤ H) : has_lift_t ↥(G'.verts) ↥(H.verts) :=
by { fconstructor, exact λ v, ⟨v, h.1 (subtype.mem v)⟩, }

def lift_vert {G' H : subgraph G} (h : G' ≤ H) : ↥(G'.verts) → ↥(H.verts) :=
by { exact λ v, ⟨v, h.1 (subtype.mem v)⟩ }

-- need to show that subgraph of acyclic graph is acyclic
lemma spanning_subgraph_acyclic (h : G.is_acyclic) (G' : subgraph G) : G'.spanning_coe.is_acyclic :=
begin
  intros v p,
  specialize h v,
  have h2 : G'.spanning_coe ≤ G,
  rw ← is_subgraph_eq_le,
  unfold is_subgraph,
  intros v w h,
  simp at h,
  apply G'.adj_sub h,
  rw ← walk.map_le_is_cycle h2,
  exact h (walk.map_le h2 p),
end

lemma spanning_coe_acyclic {G' : subgraph G} : G'.spanning_coe.is_acyclic → G'.is_acyclic :=
begin
  intros h v p,
  have f := embedding.spanning_coe G'.coe,
  rw subgraph.spanning_coe_coe at f,
  have h3 : function.injective f.to_hom,
  exact rel_embedding.injective f,
  rw ← walk.map_is_cycle_iff_of_injective h3,
  exact h _ (walk.map f.to_hom p),
end

lemma acyclic_of_subgraph_acyclic (h : G.is_acyclic) (G' : subgraph G) : G'.is_acyclic :=
by { exact spanning_coe_acyclic (spanning_subgraph_acyclic h G') }

lemma spanning_coe_iff_coe_acyclic (G' : subgraph G) : G'.spanning_coe.is_acyclic ↔ G'.is_acyclic :=
begin
  split,
  apply spanning_coe_acyclic,
  intros h v p,
  sorry,
end

def lift_walk {G' H : subgraph G} (h : G' ≤ H) (v w : G'.verts) (p : G'.coe.walk v w) :
  H.coe.walk (lift_vert h v) (lift_vert h w) :=
begin

  sorry,
end
-- need one-to-one map here?

-- use spanning_coe to show that the regular subgraph is also acyclic
lemma subgraph_acyclic' (G' H : subgraph G) (h : G' ≤ H) (h2 : H.is_acyclic) : G'.is_acyclic :=
begin
  intros v p,
  specialize h2 (lift_vert h v),
  sorry,
end

lemma mem_induce_walk_support {u v : V} {s : set V} {p : G.walk u v} (h : {w | w ∈ p.support} ⊆ s) :
  u ∈ s ∧ v ∈ s:=
begin
  refine ⟨set.mem_of_subset_of_mem h (walk.start_mem_support p),
    set.mem_of_subset_of_mem h (walk.end_mem_support p)⟩,
end

variables (u v : V) (s : set V) (h1 : u ∈ s) (h2 : v ∈ s)

def induce_walk' (p : G.walk u v) (h : {w | w ∈ p.support} ⊆ s) : Π {u v : V},
G.walk u v → (G.induce s).walk ⟨u, h1⟩ ⟨v, (mem_induce_walk_support h).2⟩
| _ _ nil := nil
| _ _ (cons h p) := cons (f.map_adj h) (map p)

def induce_walk (u v : V) (s : set V) (p : G.walk u v) (h : {w | w ∈ p.support} ⊆ s) :
  (G.induce s).walk ⟨u, (mem_induce_walk_support h).1⟩ ⟨v, (mem_induce_walk_support h).2⟩ :=
begin
  induction p,
  have h2 : p ∈ s,
  apply (mem_induce_walk_support h).1,

  sorry,

  sorry,
end

lemma delete_leaf_connected (v : V) [fintype (G.neighbor_set v)] [nonempty (G.neighbor_set v)]
 (h : G.connected) : G.degree v = 1 → (induce {v}ᶜ G).connected :=
begin
  intros hdeg,
  rw connected_iff,
  cases h with pre non,
  refine ⟨_, _⟩,
  { rw preconnected,
    intros u w,
    specialize pre u w,
    rw reachable at pre,
    cases pre with p,
    split,
    -- show that v isn't in p
    sorry },
  { have h3 : G.neighbor_set v ⊆ {v}ᶜ,
    simp only [set.subset_compl_singleton_iff, mem_neighbor_set, simple_graph.irrefl, not_false_iff],
    rw set.nonempty_coe_sort,
    rw set.nonempty_compl,
    rw degree_one_iff_neighbor_singleton at hdeg,
    cases hdeg with w hw,
    rw set.ne_univ_iff_exists_not_mem,
    use w,
    rw set.mem_singleton_iff,
    have h2 : w ∈ G.neighbor_finset v,
    rw hw,
    simp,
    simp at h2,
    intros h3,
    rw h3 at h2,
    apply G.loopless v,
    exact h2 },
end
-- need to show that deleting a leaf from a tree produces a tree

lemma delete_leaf_tree (v : V) [fintype (G.neighbor_set v)] [nonempty (G.neighbor_set v)]
(h : G.is_tree) :
  G.degree v = 1 ↔ (G.induce {v}ᶜ).is_tree :=
begin
  split,
  intros h2,
  split,
  cases h with h1 h2,
  cases h1 with pre non,
  have h2 : nonempty ({v}ᶜ : set V),
  sorry,
  have h3 : (induce {v}ᶜ G).preconnected,
  sorry,
  rw connected_iff,
  exact ⟨h3, h2⟩,
  rw induce_eq_coe_induce_top,
  apply acyclic_of_subgraph_acyclic,
  exact h.2,
  sorry,
end

-- def prufer_step (l : list (fin n))



end simple_graph
