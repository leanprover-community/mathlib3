/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.connectivity
/-!

# Acyclic graphs and trees

This module introduces *acyclic graphs* (a.k.a. *forests*) and *trees*.

The general structure of the proofs of `simple_graph.is_acyclic` and `simple_graph.is_tree`
generally follows the description for these theorems for multigraphs from [Chou1994].

## Main definitions

* `simple_graph.is_acyclic` is a predicate for a graph having no cyclic walks
* `simple_graph.is_tree` is a predicate for a graph being a tree (a connected acyclic graph)
* `simple_graph.is_bridge` for whether two vertices constitute a bridge edge

## Main statements

* `simple_graph.is_acyclic_iff` characterizes acyclicity in terms of uniqueness of paths between
  pairs of vertices.
* `simple_graph.is_tree_iff` characterizes trees in terms of existence and uniqueness of paths
  between pairs of vertices from a nonempty vertex type.
* `simple_graph.is_bridge_iff_forall_cycle_not_mem` characterizes bridge edges in terms of
  there being no cycle that contains them.

## Tags

acyclic graphs, trees, bridge edges
-/

universes u v

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/-- A graph is *acyclic* (or a *forest*) if it has no cycles. -/
def is_acyclic : Prop := ∀ (v : V) (c : G.walk v v), ¬c.is_cycle

/-- A *tree* is a connected acyclic graph. -/
def is_tree : Prop := G.connected ∧ G.is_acyclic

/-- An edge of a graph is a *bridge* if, after removing it, its incident vertices
are no longer reachable from one another. Note that we do not require the vertices
to be adjacent.

Since this is for simple graphs, we use the endpoints the edge directly.-/
def is_bridge (v w : V) : Prop := ¬ (G.delete_edges {⟦(v, w)⟧}).reachable v w

lemma is_bridge_iff_forall_walk_mem_edges {v w : V} :
  G.is_bridge v w ↔ ∀ (p : G.walk v w), ⟦(v, w)⟧ ∈ p.edges :=
begin
  refine ⟨λ hb p, _, _⟩,
  { by_contra he,
    exact hb ⟨p.to_delete_edge _ he⟩ },
  { rintro hpe ⟨p'⟩,
    specialize hpe (p'.map (hom.map_spanning_subgraphs (G.delete_edges_le _))),
    simp only [set_coe.exists, walk.edges_map, list.mem_map] at hpe,
    obtain ⟨z, he, hd⟩ := hpe,
    simp only [hom.map_spanning_subgraphs, rel_hom.coe_fn_mk, sym2.map_id', id.def] at hd,
    simpa [hd] using p'.edges_subset_edge_set he }
end

lemma is_bridge_iff_forall_cycle_not_mem.aux [decidable_eq V]
  {u v w : V}
  (hb : ∀ (p : G.walk v w), ⟦(v, w)⟧ ∈ p.edges)
  (c : G.walk u u)
  (hc : c.is_trail)
  (he : ⟦(v, w)⟧ ∈ c.edges)
  (hw : w ∈ (c.take_until v (c.fst_mem_support_of_mem_edges he)).support) :
  false :=
begin
  have hv := c.fst_mem_support_of_mem_edges he,
  -- decompose c into
  --      puw     pwv     pvu
  --   u ----> w ----> v ----> u
  let puw := (c.take_until v hv).take_until w hw,
  let pwv := (c.take_until v hv).drop_until w hw,
  let pvu := c.drop_until v hv,
  have : c = (puw.append pwv).append pvu := by simp,
  -- We have two walks from v to w
  --      pvu     puw
  --   v ----> u ----> w
  --   |               ^
  --    `-------------'
  --      pwv.reverse
  -- so they both contain the edge ⟦(v, w)⟧, but that's a contradiction since c is a trail.
  have hbq := hb (pvu.append puw),
  have hpq' := hb pwv.reverse,
  rw [walk.edges_reverse, list.mem_reverse] at hpq',
  rw [walk.is_trail_def, this, walk.edges_append, walk.edges_append,
      list.nodup_append_comm, ← list.append_assoc, ← walk.edges_append] at hc,
  exact list.disjoint_of_nodup_append hc hbq hpq',
end

lemma is_bridge_iff_forall_cycle_not_mem {v w : V} (h : G.adj v w) :
  G.is_bridge v w ↔ ∀ {u : V} (p : G.walk u u), p.is_cycle → ⟦(v, w)⟧ ∉ p.edges :=
begin
  classical,
  split,
  { intros hb u c hc he,
    rw is_bridge_iff_forall_walk_mem_edges at hb,
    have hvc : v ∈ c.support := walk.fst_mem_support_of_mem_edges c he,
    have hwc : w ∈ c.support := walk.snd_mem_support_of_mem_edges c he,
    let puv := c.take_until v hvc,
    let pvu := c.drop_until v hvc,
    obtain (hw | hw') : w ∈ puv.support ∨ w ∈ pvu.support,
    { rwa [← walk.mem_support_append_iff, walk.take_spec] },
    { exact is_bridge_iff_forall_cycle_not_mem.aux G hb c hc.to_trail he hw },
    { have hb' : ∀ (p : G.walk w v), ⟦(w, v)⟧ ∈ p.edges,
      { intro p,
        simpa [sym2.eq_swap] using hb p.reverse, },
      apply is_bridge_iff_forall_cycle_not_mem.aux G hb' (pvu.append puv)
        (hc.to_trail.rotate hvc) _ (walk.start_mem_support _),
      rwa [walk.edges_append, list.mem_append, or_comm, ← list.mem_append,
           ← walk.edges_append, walk.take_spec, sym2.eq_swap], } },
  { rw is_bridge_iff_forall_walk_mem_edges,
    intros hc p,
    by_contra hne,
    apply hc (walk.cons h.symm p.to_path),
    { apply path.cons_is_cycle,
      rw sym2.eq_swap,
      intro h,
      exact absurd (walk.edges_to_path_subset p h) hne, },
    simp only [sym2.eq_swap, walk.edges_cons, list.mem_cons_iff, eq_self_iff_true, true_or], },
end

lemma is_acyclic_iff_forall_is_bridge : G.is_acyclic ↔ ∀ {v w : V}, G.adj v w → G.is_bridge v w :=
begin
  split,
  { intros ha v w hvw,
    rw is_bridge_iff_forall_cycle_not_mem _ hvw,
    intros u p hp,
    exact absurd hp (ha _ p), },
  { rintros hb v (_ | @⟨_, _, _, ha, p⟩) hp,
    { exact hp.not_of_nil },
    { specialize hb ha,
      rw is_bridge_iff_forall_cycle_not_mem _ ha at hb,
      apply hb _ hp,
      rw [walk.edges_cons],
      apply list.mem_cons_self } },
end

lemma is_acyclic.path_unique {G : simple_graph V} (h : G.is_acyclic)
  {v w : V} (p q : G.path v w) : p = q :=
begin
  obtain ⟨p, hp⟩ := p,
  obtain ⟨q, hq⟩ := q,
  simp only,
  induction p with u pu pv pw ph p ih generalizing q,
  { cases q,
    { refl },
    { simpa [walk.is_path_def] using hq, } },
  { rw is_acyclic_iff_forall_is_bridge at h,
    specialize h ph,
    rw is_bridge_iff_forall_walk_mem_edges at h,
    specialize h (q.append p.reverse),
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

lemma is_acyclic_iff : G.is_acyclic ↔ ∀ (v w : V) (p q : G.path v w), p = q :=
⟨is_acyclic.path_unique, is_acyclic_of_path_unique _⟩

lemma is_tree_iff : G.is_tree ↔ nonempty V ∧ ∀ (v w : V), ∃!(p : G.walk v w), p.is_path :=
begin
  classical,
  simp only [is_tree, is_acyclic_iff],
  split,
  { rintro ⟨hc, hu⟩,
    refine ⟨hc.nonempty, _⟩,
    intros v w,
    let q := (hc v w).some.to_path,
    use q,
    simp only [true_and, path.is_path],
    intros p hp,
    specialize hu v w ⟨p, hp⟩ q,
    simp only [←hu, subtype.coe_mk], },
  { rintro ⟨hV, h⟩,
    refine ⟨@connected.mk V _ _ hV, _⟩,
    { intros v w,
      obtain ⟨p, hp⟩ := h v w,
      use p, },
    { rintros v w ⟨p, hp⟩ ⟨q, hq⟩,
      simp only [unique_of_exists_unique (h v w) hp hq] } },
end

end simple_graph
