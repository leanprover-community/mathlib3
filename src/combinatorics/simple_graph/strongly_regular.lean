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

* `G.is_SRG_with n k ℓ μ` (see `simple_graph.is_SRG_with`) is a structure for
  a `simple_graph` satisfying the following conditions:
  * The cardinality of the vertex set is `n`
  * `G` is a regular graph with degree `k`
  * The number of common neighbors between any two adjacent vertices in `G` is `ℓ`
  * The number of common neighbors between any two nonadjacent vertices in `G` is `μ`

## TODO
- Prove that the parameters of a strongly regular graph
  obey the relation `(n - k - 1) * μ = k * (k - ℓ - 1)`
- Prove that if `I` is the identity matrix and `J` is the all-one matrix,
  then the adj matrix `A` of SRG obeys relation `A^2 = kI + ℓA + μ(J - I - A)`
-/

open finset

universes u

namespace simple_graph
variables {V : Type u}
variables [fintype V] [decidable_eq V]
variables (G : simple_graph V) [decidable_rel G.adj]

/--
A graph is strongly regular with parameters `n k ℓ μ` if
 * its vertex set has cardinality `n`
 * it is regular with degree `k`
 * every pair of adjacent vertices has `ℓ` common neighbors
 * every pair of nonadjacent vertices has `μ` common neighbors
-/
structure is_SRG_with (n k ℓ μ : ℕ) : Prop :=
(card : fintype.card V = n)
(regular : G.is_regular_of_degree k)
(of_adj : ∀ (v w : V), G.adj v w → fintype.card (G.common_neighbors v w) = ℓ)
(of_not_adj : ∀ (v w : V), v ≠ w → ¬G.adj v w → fintype.card (G.common_neighbors v w) = μ)

variables {G} {n k ℓ μ : ℕ}

/-- Empty graphs are strongly regular. Note that `ℓ` can take any value
  for empty graphs, since there are no pairs of adjacent vertices. -/
lemma bot_strongly_regular :
  (⊥ : simple_graph V).is_SRG_with (fintype.card V) 0 ℓ 0 :=
{ card := rfl,
  regular := bot_degree,
  of_adj := λ v w h, h.elim,
  of_not_adj := λ v w h, begin
    simp only [card_eq_zero, filter_congr_decidable, fintype.card_of_finset, forall_true_left,
      not_false_iff, bot_adj],
    ext,
    simp [mem_common_neighbors],
  end }

/-- Complete graphs are strongly regular. Note that `μ` can take any value
  for complete graphs, since there are no distinct pairs of non-adjacent vertices. -/
lemma is_SRG_with.top :
  (⊤ : simple_graph V).is_SRG_with (fintype.card V) (fintype.card V - 1) (fintype.card V - 2) μ :=
{ card := rfl,
  regular := is_regular_of_degree.top,
  of_adj := λ v w h, begin
    rw card_common_neighbors_top,
    exact h,
  end,
  of_not_adj := λ v w h h', false.elim $ by simpa using h }

lemma is_SRG_with.card_neighbor_finset_union_eq {v w : V} (h : G.is_SRG_with n k ℓ μ) :
  (G.neighbor_finset v ∪ G.neighbor_finset w).card =
    2 * k - fintype.card (G.common_neighbors v w) :=
begin
  apply @nat.add_right_cancel _ (fintype.card (G.common_neighbors v w)),
  rw [nat.sub_add_cancel, ← set.to_finset_card],
  { simp [neighbor_finset, common_neighbors, set.to_finset_inter, finset.card_union_add_card_inter,
      h.regular.degree_eq, two_mul], },
  { apply le_trans (card_common_neighbors_le_degree_left _ _ _),
    simp [h.regular.degree_eq, two_mul], },
end

/-- Assuming `G` is strongly regular, `2*(k + 1) - m` in `G` is the number of vertices that are
  adjacent to either `v` or `w` when `¬G.adj v w`. So it's the cardinality of
  `G.neighbor_set v ∪ G.neighbor_set w`. -/
lemma is_SRG_with.card_neighbor_finset_union_of_not_adj {v w : V} (h : G.is_SRG_with n k ℓ μ)
  (hne : v ≠ w) (ha : ¬G.adj v w) :
  (G.neighbor_finset v ∪ G.neighbor_finset w).card = 2 * k - μ :=
begin
  rw ← h.of_not_adj v w hne ha,
  apply h.card_neighbor_finset_union_eq,
end

lemma is_SRG_with.card_neighbor_finset_union_of_adj {v w : V} (h : G.is_SRG_with n k ℓ μ)
  (ha : G.adj v w) :
  (G.neighbor_finset v ∪ G.neighbor_finset w).card = 2 * k - ℓ :=
begin
  rw ← h.of_adj v w ha,
  apply h.card_neighbor_finset_union_eq,
end

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

lemma is_SRG_with.compl_is_regular (h : G.is_SRG_with n k ℓ μ) :
  Gᶜ.is_regular_of_degree (n - k - 1) :=
begin
  rw [← h.card, nat.sub_sub, add_comm, ←nat.sub_sub],
  exact h.regular.compl,
end

lemma is_SRG_with.card_common_neighbors_eq_of_adj_compl (h : G.is_SRG_with n k ℓ μ)
  {v w : V} (ha : Gᶜ.adj v w) :
  fintype.card ↥(Gᶜ.common_neighbors v w) = n - (2 * k - μ) - 2 :=
begin
  simp only [←set.to_finset_card, common_neighbors, set.to_finset_inter, neighbor_set_compl,
    set.to_finset_sdiff, set.to_finset_singleton, set.to_finset_compl, ←neighbor_finset_def],
  simp_rw compl_neighbor_finset_sdiff_inter_eq,
  have hne : v ≠ w := ne_of_adj _ ha,
  rw compl_adj at ha,
  rw [card_sdiff, ← insert_eq, card_insert_of_not_mem, card_singleton, ← finset.compl_union],
  { change (1 + 1) with 2,
    rw [card_compl, h.card_neighbor_finset_union_of_not_adj hne ha.2, ← h.card], },
  { simp only [hne.symm, not_false_iff, mem_singleton], },
  { intro u,
    simp only [mem_union, mem_compl, mem_neighbor_finset, mem_inter, mem_singleton],
    rintro (rfl|rfl);
    simpa [adj_comm] using ha.2, },
end

lemma is_SRG_with.card_common_neighbors_eq_of_not_adj_compl (h : G.is_SRG_with n k ℓ μ)
  {v w : V} (hn : v ≠ w) (hna : ¬Gᶜ.adj v w)  :
  fintype.card ↥(Gᶜ.common_neighbors v w) = n - (2 * k - ℓ) :=
begin
  simp only [←set.to_finset_card, common_neighbors, set.to_finset_inter, neighbor_set_compl,
    set.to_finset_sdiff, set.to_finset_singleton, set.to_finset_compl, ←neighbor_finset_def],
  simp only [not_and, not_not, compl_adj] at hna,
  have h2' := hna hn,
  simp_rw [compl_neighbor_finset_sdiff_inter_eq, sdiff_compl_neighbor_finset_inter_eq h2'],
  rwa [← finset.compl_union, card_compl, h.card_neighbor_finset_union_of_adj, ← h.card],
end

/-- The complement of a strongly regular graph is strongly regular. -/
lemma is_SRG_with.compl (h : G.is_SRG_with n k ℓ μ) :
  Gᶜ.is_SRG_with n (n - k - 1) (n - (2 * k - μ) - 2) (n - (2 * k - ℓ)) :=
{ card := h.card,
  regular := h.compl_is_regular,
  of_adj := λ v w ha, h.card_common_neighbors_eq_of_adj_compl ha,
  of_not_adj := λ v w hn hna, h.card_common_neighbors_eq_of_not_adj_compl hn hna, }

end simple_graph
