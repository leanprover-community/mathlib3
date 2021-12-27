/-
Copyright (c) 2021 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov
-/
import combinatorics.simple_graph.basic
import data.set.finite
/-!
# Strongly regular graphs

## Main definitions

* `G.is_SRG_with n k l m` (see `simple_graph.is_SRG_with`) is a structure for
  a `simple_graph` satisfying the following conditions:
  * The cardinality of the vertex set is `n`
  * `G` is a regular graph with degree `k`
  * The number of common neighbors between any two adjacent vertices in `G` is `l`
  * The number of common neighbors between any two nonadjacent vertices in `G` is `m`

## TODO
- Prove that the parameters of a strongly regular graph
  obey the relation `(n - k - 1) * m = k * (k - l - 1)`
- Prove that if `I` is the identity matrix and `J` is the all-one matrix,
  then the adj matrix `A` of SRG obeys relation `A^2 = kI + lA + m(J - I - A)`
-/

open finset

universes u

namespace simple_graph
variables {V : Type u}
variables [fintype V] [decidable_eq V]
variables (G : simple_graph V) [decidable_rel G.adj]

/--
A graph is strongly regular with parameters `n k l m` if
 * its vertex set has cardinality `n`
 * it is regular with degree `k`
 * every pair of adjacent vertices has `l` common neighbors
 * every pair of nonadjacent vertices has `m` common neighbors
-/
structure is_SRG_with (n k l m : ℕ) : Prop :=
(card : fintype.card V = n)
(regular : G.is_regular_of_degree k)
(adj_common : ∀ (v w : V), G.adj v w → fintype.card (G.common_neighbors v w) = l)
(nadj_common : ∀ (v w : V), v ≠ w ∧ ¬G.adj v w → fintype.card (G.common_neighbors v w) = m)

variables {n k l m : ℕ}

/-- Empty graphs are strongly regular. Note that the parameter `l` can take any value
  for empty graphs, since there are no pairs of adjacent vertices. -/
lemma bot_strongly_regular (l : ℕ) :
  (⊥ : simple_graph V).is_SRG_with (fintype.card V) 0 l 0 :=
{ card := rfl,
  regular := bot_degree,
  adj_common := λ v w h, h.elim,
  nadj_common := λ v w h, begin
    simp only [finset.card_eq_zero, finset.filter_congr_decidable, fintype.card_of_finset],
    ext,
    simp [mem_common_neighbors],
  end }

/-- Complete graphs are strongly regular. Note that the parameter `m` can take any value
  for complete graphs, since there are no distinct pairs of nonadjacent vertices. -/
lemma top_strongly_regular (m : ℕ) :
  (⊤ : simple_graph V).is_SRG_with (fintype.card V) (fintype.card V - 1) (fintype.card V - 2) m :=
{ card := rfl,
  regular := complete_graph_is_regular,
  adj_common := λ v w h, begin
    rw card_common_neighbors_top,
    exact h,
  end,
  nadj_common := λ v w h, false.elim $ by simpa using h }

lemma card_neighbor_finset_union_eq (h : G.is_SRG_with n k l m) (v w : V) :
  (G.neighbor_finset v ∪ G.neighbor_finset w).card =
    2 * k - fintype.card (G.common_neighbors v w) :=
begin
  apply @nat.add_right_cancel _ (fintype.card (G.common_neighbors v w)),
  rw [nat.sub_add_cancel, ← set.to_finset_card],
  { simp [neighbor_finset, common_neighbors, set.to_finset_inter, finset.card_union_add_card_inter,
      G.is_regular_of_degree_eq h.regular, two_mul], },
  { apply le_trans (card_common_neighbors_le_degree_left _ _ _),
    simp [G.is_regular_of_degree_eq h.regular, two_mul], },
end

/-- Assuming `G` is strongly regular, `2*(k + 1) - m` in `G` is the number of vertices that are
  adjacent to either `v` or `w` when `¬G.adj v w`. So it's the cardinality of
  `G.neighbor_set v ∪ G.neighbor_set w`. -/
lemma card_neighbor_finset_union_nadj (h : G.is_SRG_with n k l m)
  {v w : V} (hne : v ≠ w) (ha : ¬G.adj v w) :
  (G.neighbor_finset v ∪ G.neighbor_finset w).card = 2 * k - m :=
begin
  rw ← h.nadj_common v w ⟨hne, ha⟩,
  apply G.card_neighbor_finset_union_eq h,
end

lemma card_neighbor_finset_union_adj (h : G.is_SRG_with n k l m)
  {v w : V} (ha : G.adj v w) :
  (G.neighbor_finset v ∪ G.neighbor_finset w).card = 2 * k - l :=
begin
  rw ← h.adj_common v w ha,
  apply G.card_neighbor_finset_union_eq h,
end

@[simp] theorem finset_compl_union (s t : finset V) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := compl_sup

lemma compl_neighbor_finset_sdiff_inter_eq {v w : V} :
  (G.neighbor_finset v)ᶜ \ {v} ∩ ((G.neighbor_finset w)ᶜ \ {w}) =
    (G.neighbor_finset v)ᶜ ∩ (G.neighbor_finset w)ᶜ \ ({w} ∪ {v}) :=
by { ext, rw ← not_iff_not, simp [imp_iff_not_or, or_assoc, or_comm, or.left_comm], }

lemma sdiff_compl_neighbor_finset_inter_eq {v w : V} (h : G.adj v w) :
  (G.neighbor_finset v)ᶜ ∩ (G.neighbor_finset w)ᶜ \ ({w} ∪ {v}) =
    (G.neighbor_finset v)ᶜ ∩ (G.neighbor_finset w)ᶜ :=
begin
  ext,
  simp only [and_imp, mem_union, mem_sdiff, mem_compl, and_iff_left_iff_imp,
    mem_neighbor_finset, mem_inter, mem_singleton],
  rintros hnv hnw (rfl|rfl),
  { exact hnv h, },
  { apply hnw, rwa adj_comm, },
end

lemma compl_regular_of_strongly_regular (h : G.is_SRG_with n k l m) :
  Gᶜ.is_regular_of_degree (n - k - 1) :=
begin
  rw [← h.card, nat.sub_sub, add_comm, ←nat.sub_sub],
  exact G.is_regular_compl_of_is_regular k h.regular,
end

lemma compl_adj_common_of_strongly_regular (h : G.is_SRG_with n k l m) :
  ∀ (v w : V), Gᶜ.adj v w → fintype.card ↥(Gᶜ.common_neighbors v w) = n - (2 * k - m) - 2 :=
begin
  intros v w h2,
  simp only [←set.to_finset_card, common_neighbors, set.to_finset_inter, neighbor_set_compl,
    set.to_finset_sdiff, set.to_finset_singleton, set.to_finset_compl, ←neighbor_finset_def],
  simp_rw compl_neighbor_finset_sdiff_inter_eq,
  have hne : v ≠ w := ne_of_adj _ h2,
  rw compl_adj at h2,
  rw [card_sdiff, ← insert_eq, card_insert_of_not_mem, card_singleton, ← finset_compl_union],
  { change (1 + 1) with 2,
    rw [card_compl, G.card_neighbor_finset_union_nadj h hne h2.2, ← h.card], },
  { simp only [hne.symm, not_false_iff, mem_singleton], },
  { intro u,
    cases h2 with h2 h2',
    simp only [mem_union, mem_compl, mem_neighbor_finset, mem_inter, mem_singleton],
    rintro (rfl|rfl);
    simpa [adj_comm] using h2', },
end

lemma compl_nadj_common_of_strongly_regular (h : G.is_SRG_with n k l m) :
  ∀ (v w : V), v ≠ w ∧ ¬Gᶜ.adj v w → fintype.card ↥(Gᶜ.common_neighbors v w) = n - (2 * k - l) :=
begin
  intros v w h2,
  simp only [←set.to_finset_card, common_neighbors, set.to_finset_inter, neighbor_set_compl,
    set.to_finset_sdiff, set.to_finset_singleton, set.to_finset_compl, ←neighbor_finset_def],
  simp only [not_and, not_not, compl_adj, ne.def] at h2,
  have h2' := h2.2 h2.1,
  simp_rw [compl_neighbor_finset_sdiff_inter_eq, G.sdiff_compl_neighbor_finset_inter_eq h2'],
  rwa [← finset_compl_union, card_compl, G.card_neighbor_finset_union_adj h, ← h.card],
end

/-- The complement of a strongly regular graph is strongly regular. -/
lemma strongly_regular_complement (h : G.is_SRG_with n k l m) :
  Gᶜ.is_SRG_with n (n - k - 1) (n - (2 * k - m) - 2) (n - (2 * k - l)) :=
{ card := h.card,
  regular := compl_regular_of_strongly_regular G h,
  adj_common := compl_adj_common_of_strongly_regular G h,
  nadj_common := compl_nadj_common_of_strongly_regular G h, }

end simple_graph
