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

* `G.is_SRG_of n k l m` (see `is_simple_graph.is_SRG_of`) is a structure for a `simple_graph`
  satisfying the following conditions:
  * The cardinality of the vertex set is `n`
  * `G` is a regular graph with degree `k`
  * The number of common neighbors between any two adjacent vertices in `G` is `l`
  * The number of common neighbors between any two nonadjacent vertices in `G` is `m`

## TODO
- Prove that the complement of a strongly regular graph is strongly regular with parameters
  `is_SRG_of n (n - k - 1) (n - 2 - 2k + m) (n - 2k + l)`
- Prove that the parameters of a strongly regular graph
  obey the relation `(n - k - 1) * m = k * (k - l - 1)`
- Prove that if `I` is the identity matrix and `J` is the all-one matrix,
  then the adj matrix `A` of SRG obeys relation `A^2 = kI + lA + m(J - I - A)`
-/

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
structure is_SRG_of (n k l m : ℕ) : Prop :=
(card : fintype.card V = n)
(regular : G.is_regular_of_degree k)
(adj_common : ∀ (v w : V), G.adj v w → finset.card (G.common_neighbors v w).to_finset = l)
(nadj_common : ∀ (v w : V), v ≠ w ∧ ¬ G.adj v w →
  finset.card (G.common_neighbors v w).to_finset = m)

open finset

/-- Empty graphs are strongly regular. Note that the parameter `l` can take any value
  for empty graphs, since there are no pairs of adjacent vertices. -/
lemma empty_strongly_regular (l : ℕ) : (empty_graph V).is_SRG_of (fintype.card V) 0 l 0 :=
{ card := rfl,
  regular := empty_graph_degree,
  adj_common := λ v w h, h.elim,
  nadj_common := λ v w h,
    begin
      simp only [filter_congr_decidable, card_eq_zero, fintype.card_of_finset, common_neighbors,
        neighbor_set, empty_graph, set.set_of_false, set.empty_inter, set.not_mem_empty,
        filter_false, set.empty_card'],
      sorry,
    end }

/-- Complete graphs are strongly regular. Note that the parameter `m` can take any value
  for complete graphs, since there are no distinct pairs of nonadjacent vertices. -/
lemma complete_strongly_regular (m : ℕ) :
  (complete_graph V).is_SRG_of (fintype.card V) (fintype.card V - 1) (fintype.card V - 2) m :=
{ card := rfl,
  regular := complete_graph_degree,
  adj_common := λ v w (h : v ≠ w),
    begin
      simp only [fintype.card_of_finset, mem_common_neighbors, complete_graph, ne.def, filter_not,
        ←not_or_distrib, filter_eq, filter_or, card_univ_diff, mem_univ, if_pos, ←insert_eq],
      --rw [card_insert_of_not_mem, card_singleton],
      --simpa,
      sorry,
    end,
  nadj_common := sorry, }--λ v w (h : ¬(v ≠ w) ∧ _), (h.1 h.2).elim }


-- first of all, what is `2*(k + 1) - m` in `G`? what does it count?
-- it counts the number of vertices that are adjacent to either `v` or `w` when `¬ G.adj v w`
-- so it's the cardinality of `G.neighbor_set v ∪ G.neighbor_set w`
lemma card_neighbor_set_union_nadj (n k l m : ℕ) (h : G.is_SRG_of n k l m) (v w : V) (h2 : ¬ G.adj v w)
  (h3 : v ≠ w) :
finset.card (G.neighbor_set v ∪ G.neighbor_set w).to_finset = 2 * k - m :=
begin
  rw ← h.nadj_common v w ⟨h3, h2⟩,
  apply @nat.add_right_cancel _ (finset.card (G.common_neighbors v w).to_finset),
  rw nat.sub_add_cancel,
  unfold common_neighbors,
  rw [set.to_finset_union, set.to_finset_inter, card_union_add_card_inter, two_mul],
  simp only [card_neighbor_set_eq_degree, set.to_finset_card],
  rw [h.regular, h.regular],
  { rw two_mul,
    have h4 : (G.common_neighbors v w).to_finset.card ≤ k,
    { rw ← h.regular v,
      exact card_common_neighbors_le_degree_left' _ _ _ },
    apply le_add_right h4 },
end

lemma card_neighbor_set_union_adj (n k l m : ℕ) (h : G.is_SRG_of n k l m) (v w : V) (h2 : G.adj v w)
  (h3 : v ≠ w) :
finset.card (G.neighbor_set v ∪ G.neighbor_set w).to_finset = 2 * k - l :=
begin
  rw ← h.adj_common v w h2,
  apply @nat.add_right_cancel _ (finset.card (G.common_neighbors v w).to_finset),
  rw nat.sub_add_cancel,
  unfold common_neighbors,
  rw [set.to_finset_union, set.to_finset_inter, card_union_add_card_inter, two_mul],
  simp only [card_neighbor_set_eq_degree, set.to_finset_card],
  rw [h.regular, h.regular],
  { rw two_mul,
    have h4 : (G.common_neighbors v w).to_finset.card ≤ k,
    { rw ← h.regular v,
      exact card_common_neighbors_le_degree_left' _ _ _ },
    apply le_add_right h4 },
end

lemma adj_nadj_ne (v w x : V) (h6: ¬G.adj w x) (h3: G.adj w v) : x ≠ v :=
begin
  by_contra,
  apply h6,
  push_neg at h,
  rw h,
  exact h3,
end

-- ## i think i need ints in order to do any of this :(
-- Prove that the complement of a strongly regular graph is strongly regular with parameters
  -- `is_SRG_of n (n - k - 1) (n - 2 - 2k + m) (n - 2k + l)`
lemma strongly_regular_complement (n k l m : ℕ) (h : G.is_SRG_of n k l m) :
  Gᶜ.is_SRG_of n (n - k - 1) (n - (2 * (k + 1) - m)) (n - (2 * k - l)) :=
{ card := h.card,
  regular :=
    begin
      rw ← h.card,
      exact compl_regular_is_regular G k h.regular,
    end,
  adj_common :=
    begin
      intros v w h,
      -- essentially i need to show that if `Gᶜ.adj v w` then their common neighbors are all those
      -- vertices `(w : V)` that aren't adjacent to either `v` or `w`
      -- this is a principle of inclusion-exclusion argument
      simp_rw common_neighbors,
      /-simp_rw fintype.card_of_finset,
      simp_rw mem_common_neighbors,
      simp_rw compl_adj,-/
      --rw nat.add_sub_assoc,

      -- n - (2 * (k + 1) - m)
      --
      sorry,
    end,
  nadj_common :=
    begin
      intros v w h2,
      unfold common_neighbors,
      simp_rw [compl_neighbor_set G v, compl_neighbor_set G w],
      have h3 : (G.neighbor_set v)ᶜ \ {v} ∩ ((G.neighbor_set w)ᶜ \ {w}) = (G.neighbor_set v)ᶜ ∩ (G.neighbor_set w)ᶜ \ ({w} ∪ {v}),
      { ext;
        simp,
        refine ⟨by cc, by cc⟩ },
      simp_rw h3,
      have h4 : (G.neighbor_set v)ᶜ ∩ (G.neighbor_set w)ᶜ \ ({w} ∪ {v}) = (G.neighbor_set v)ᶜ ∩ (G.neighbor_set w)ᶜ,
      { ext;
        simp only [and_imp, set.mem_insert_iff, set.mem_inter_eq, set.mem_diff, set.mem_singleton_iff,
          and_iff_left_iff_imp, set.union_singleton, set.mem_compl_iff, mem_neighbor_set],
        intros h5 h6,
        push_neg,
        split,
        { have h3 : G.adj w v,
          { rw adj_compl,
            refine ⟨ne.symm h2.1, _⟩,
            rw edge_symm,
            exact h2.2 },
          exact adj_nadj_ne G v w x h6 h3 },
        { have h3 : G.adj v w,
          { rw adj_compl,
            refine ⟨h2.1, h2.2⟩ },
          exact adj_nadj_ne G w v x h5 h3 } },
      simp_rw [h4, ← set.compl_union, set.to_finset_compl, card_compl,
        card_neighbor_set_union_adj G n k l m h v w ((G.adj_compl v w).2 ⟨h2.1, h2.2⟩) h2.1,
        h.card],
    end }

end simple_graph
