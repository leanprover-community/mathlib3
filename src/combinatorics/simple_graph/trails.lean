/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.connectivity
import data.nat.parity

/-!

# Trails and Eulerian trails

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module contains additional theory about trails, including Eulerian trails (also known
as Eulerian circuits).

## Main definitions

* `simple_graph.walk.is_eulerian` is the predicate that a trail is an Eulerian trail.
* `simple_graph.walk.is_trail.even_countp_edges_iff` gives a condition on the number of edges
  in a trail that can be incident to a given vertex.
* `simple_graph.walk.is_eulerian.even_degree_iff` gives a condition on the degrees of vertices
  when there exists an Eulerian trail.
* `simple_graph.walk.is_eulerian.card_odd_degree` gives the possible numbers of odd-degree
  vertices when there exists an Eulerian trail.

## Todo

* Prove that there exists an Eulerian trail when the conclusion to
  `simple_graph.walk.is_eulerian.card_odd_degree` holds.

## Tags

Eulerian trails

-/

namespace simple_graph
variables {V : Type*} {G : simple_graph V}

namespace walk

/-- The edges of a trail as a finset, since each edge in a trail appears exactly once. -/
@[reducible] def is_trail.edges_finset {u v : V} {p : G.walk u v}
  (h : p.is_trail) : finset (sym2 V) :=
⟨p.edges, h.edges_nodup⟩

variables [decidable_eq V]

lemma is_trail.even_countp_edges_iff {u v : V} {p : G.walk u v} (ht : p.is_trail) (x : V) :
  even (p.edges.countp (λ e, x ∈ e)) ↔ (u ≠ v → x ≠ u ∧ x ≠ v) :=
begin
  induction p with u u v w huv p ih,
  { simp, },
  { rw [cons_is_trail_iff] at ht,
    specialize ih ht.1,
    simp only [list.countp_cons, ne.def, edges_cons, sym2.mem_iff],
    split_ifs with h,
    { obtain (rfl | rfl) := h,
      { rw [nat.even_add_one, ih],
        simp only [huv.ne, imp_false, ne.def, not_false_iff, true_and, not_forall, not_not,
          exists_prop, eq_self_iff_true, not_true, false_and, and_iff_right_iff_imp],
        rintro rfl rfl,
        exact G.loopless _ huv, },
      { rw [nat.even_add_one, ih, ← not_iff_not],
        simp only [huv.ne.symm, ne.def, eq_self_iff_true, not_true, false_and, not_forall,
          not_false_iff, exists_prop, and_true, not_not, true_and, iff_and_self],
        rintro rfl,
        exact huv.ne, } },
    { rw not_or_distrib at h,
      simp only [h.1, h.2, not_false_iff, true_and, add_zero, ne.def] at ih ⊢,
      rw ih,
      split;
      { rintro h' h'' rfl,
        simp only [imp_false, eq_self_iff_true, not_true, not_not] at h',
        cases h',
        simpa using h } } },
end

/-- An *Eulerian trail* (also known as an "Eulerian path") is a walk
`p` that visits every edge exactly once.  The lemma `simple_graph.walk.is_eulerian.is_trail` shows
that these are trails.

Combine with `p.is_circuit` to get an Eulerian circuit (also known as an "Eulerian cycle"). -/
def is_eulerian {u v : V} (p : G.walk u v) : Prop :=
∀ e, e ∈ G.edge_set → p.edges.count e = 1

lemma is_eulerian.is_trail {u v : V} {p : G.walk u v}
  (h : p.is_eulerian) : p.is_trail :=
begin
  rw [is_trail_def, list.nodup_iff_count_le_one],
  intro e,
  by_cases he : e ∈ p.edges,
  { exact (h e (edges_subset_edge_set _ he)).le },
  { simp [he] },
end

lemma is_eulerian.mem_edges_iff {u v : V} {p : G.walk u v} (h : p.is_eulerian) {e : sym2 V} :
  e ∈ p.edges ↔ e ∈ G.edge_set :=
⟨λ h, p.edges_subset_edge_set h, λ he, by simpa using (h e he).ge⟩

/-- The edge set of an Eulerian graph is finite. -/
def is_eulerian.fintype_edge_set {u v : V} {p : G.walk u v}
  (h : p.is_eulerian) : fintype G.edge_set :=
fintype.of_finset h.is_trail.edges_finset $ λ e,
by simp only [finset.mem_mk, multiset.mem_coe, h.mem_edges_iff]

lemma is_trail.is_eulerian_of_forall_mem {u v : V} {p : G.walk u v}
  (h : p.is_trail) (hc : ∀ e, e ∈ G.edge_set → e ∈ p.edges) :
  p.is_eulerian :=
λ e he, list.count_eq_one_of_mem h.edges_nodup (hc e he)

lemma is_eulerian_iff {u v : V} (p : G.walk u v) :
  p.is_eulerian ↔ p.is_trail ∧ ∀ e, e ∈ G.edge_set → e ∈ p.edges :=
begin
  split,
  { intro h,
    exact ⟨h.is_trail, λ _, h.mem_edges_iff.mpr⟩, },
  { rintro ⟨h, hl⟩,
    exact h.is_eulerian_of_forall_mem hl, },
end

lemma is_eulerian.edges_finset_eq [fintype G.edge_set]
  {u v : V} {p : G.walk u v} (h : p.is_eulerian) :
  h.is_trail.edges_finset = G.edge_finset :=
by { ext e, simp [h.mem_edges_iff] }

lemma is_eulerian.even_degree_iff {x u v : V} {p : G.walk u v} (ht : p.is_eulerian)
  [fintype V] [decidable_rel G.adj] :
  even (G.degree x) ↔ (u ≠ v → x ≠ u ∧ x ≠ v) :=
begin
  convert ht.is_trail.even_countp_edges_iff x,
  rw [← multiset.coe_countp, multiset.countp_eq_card_filter, ← card_incidence_finset_eq_degree],
  change multiset.card _ = _,
  congr' 1,
  convert_to _ = (ht.is_trail.edges_finset.filter (has_mem.mem x)).val,
  rw [ht.edges_finset_eq, G.incidence_finset_eq_filter x],
end

lemma is_eulerian.card_filter_odd_degree [fintype V] [decidable_rel G.adj]
  {u v : V} {p : G.walk u v} (ht : p.is_eulerian)
  {s} (h : s = (finset.univ : finset V).filter (λ v, odd (G.degree v))) :
  s.card = 0 ∨ s.card = 2 :=
begin
  subst s,
  simp only [nat.odd_iff_not_even, finset.card_eq_zero],
  simp only [ht.even_degree_iff, ne.def, not_forall, not_and, not_not, exists_prop],
  obtain (rfl | hn) := eq_or_ne u v,
  { left,
    simp, },
  { right,
    convert_to _ = ({u, v} : finset V).card,
    { simp [hn], },
    { congr',
      ext x,
      simp [hn, imp_iff_not_or], } },
end

lemma is_eulerian.card_odd_degree [fintype V] [decidable_rel G.adj]
  {u v : V} {p : G.walk u v} (ht : p.is_eulerian) :
  fintype.card {v : V | odd (G.degree v)} = 0 ∨ fintype.card {v : V | odd (G.degree v)} = 2 :=
begin
  rw ← set.to_finset_card,
  apply is_eulerian.card_filter_odd_degree ht,
  ext v,
  simp,
end

end walk

end simple_graph
