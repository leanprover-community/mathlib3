/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.connectivity
/-!

# Acyclic graphs and trees

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
variables {V : Type u} (G : simple_graph V) {v w : V}

open walk

/-- A graph is *acyclic* (or a *forest*) if it has no cycles. -/
def is_acyclic : Prop := ∀ (v : V) (c : G.walk v v), ¬c.is_cycle

/-- A *tree* is a connected acyclic graph. -/
@[mk_iff, protect_proj] structure is_tree : Prop :=
(is_connected : G.connected)
(is_acyclic : G.is_acyclic)

variables {G}

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

lemma is_tree.exists_unique_path (hG : G.is_tree) : ∀ v w, ∃! p : G.walk v w, p.is_path :=
(is_tree_iff_exists_unique_path.1 hG).2

lemma is_tree.card_edge_finset [fintype V] [fintype G.edge_set] (hG : G.is_tree) :
  finset.card G.edge_finset + 1 = fintype.card V :=
begin
  haveI := hG.is_connected.nonempty,
  inhabit V,
  classical,
  have : finset.card ({default} : finset V)ᶜ + 1 = fintype.card V,
  { rwa [finset.card_compl, finset.card_singleton, nat.sub_add_cancel fintype.card_pos] },
  rw [←this, add_left_inj],
  choose f hf hf' using λ v, hG.exists_unique_path v default,
  refine (finset.card_congr (λ w hw, ((f w).head _).edge) (λ a ha, _) _ _).symm,
  { simpa using hw },
  { simp only [mem_edge_finset, dart.edge_mem] },
  { simp only [finset.mem_compl, finset.mem_singleton],
    intros a b ha hb h,
    wlog h' : (f a).length ≤ (f b).length generalizing a b,
    { exact (this _ _ _ _ h.symm $ le_of_not_le h').symm },
    rw dart_edge_eq_iff at h,
    cases h,
    { simpa only [head_fst] using congr_arg (λ d : G.dart, d.to_prod.fst) h },
    have h1 : ((f a).head ha).snd = b,
    { rw [h, dart.symm_to_prod, prod.snd_swap, head_fst] },
    have h3 := congr_arg length (hf' _ (((f _).tail _).copy h1 rfl) _),
    rw [length_copy, ←add_left_inj 1, length_tail_add_one] at h3,
    { exfalso,
      linarith },
    { rw is_path_copy,
      exact (hf _).tail _ } },
  simp only [sym2.forall, finset.mem_compl, finset.mem_singleton, mem_edge_finset, mem_edge_set],
  intros x y h,
  wlog h' : (f x).length ≤ (f y).length generalizing x y,
  { rw sym2.eq_swap,
    exact this y x h.symm (le_of_not_le h') },
  refine ⟨y, _, dart_edge_eq_mk_iff'.2 $ or.inr ⟨head_fst _ _, _⟩⟩,
  { rintro rfl,
    rw [←hf' _ nil is_path.nil, length_nil, ←hf' _ (nil.cons h) (is_path.nil.cons $
      by simpa using h.ne), length_cons, length_nil] at h',
    simpa only [le_zero_iff, nat.one_ne_zero] using h' },
  rw [←hf' _ ((f x).cons h.symm) ((cons_is_path_iff _ _).2 ⟨hf _, λ hy, _⟩), head],
  suffices : (f x).take_until y hy = nil.cons h,
  { rw ←take_spec _ hy at h',
    simpa [this, hf' _ _ ((hf _).drop_until _ hy)] using h' },
  refine (hG.exists_unique_path _ _).unique ((hf _).take_until _) _,
  simp only [cons_is_path_iff, is_path_iff_eq_nil, support_nil, list.mem_singleton, true_and],
  exact h.ne,
end

end simple_graph
