/-
Copyright (c) 2021 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alena Gusakov
-/
import combinatorics.simple_graph.basic
import data.set.finite
/-!
# Strongly regular graphs

## Main definitions

* `common_neighbors` is the intersection of the neighbor sets of two given vertices

* `G.is_SRG_of n k l m` is a structure for a `simple_graph` with conditions
  * The cardinality of the vertex set is `n`
  * `G` is a regular graph with degree `k`
  * The number of common neighbors between any two adjacent vertices in `G` is `l`
  * The number of common neighbors between any two nonadjacent vertices in `G` is `m`

## TODO
- Prove that the complement of a strongly regular graph is strongly regular with parameters
  `is_SRG_of n (n - k - 1) (n - 2 - 2k + m) (v - 2k + l)`
- Prove that the parameters of a strongly regular graph
  obey relation `(n - k - 1) * m = k * (k - l - 1)`
- Prove that if I is the identity matrix and J is the all-one matrix,
  then the adj matrix A of SRG obeys relation A^2 = kI + lA + m(J - I - A)
-/

universes u

namespace simple_graph
variables {V : Type u}
variables (G : simple_graph V) [decidable_rel G.adj]

variables [fintype V] [decidable_eq V]

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
(adj_common : ∀ (v w : V), G.adj v w → fintype.card (G.common_neighbors v w) = l)
(nadj_common : ∀ (v w : V), ¬ G.adj v w ∧ v ≠ w → fintype.card (G.common_neighbors v w) = m)

lemma complete_strongly_regular (x : ℕ) :
  (complete_graph V).is_SRG_of (fintype.card V) (fintype.card V - 1) (fintype.card V - 2) x :=
{ card := rfl,
  regular := complete_graph_degree,
  adj_common := λ v w h,
    begin
      simp only [finset.filter_congr_decidable, fintype.card_of_finset, mem_common_neighbors],
      have h2 : (finset.filter (λ (x : V), ¬ (v ≠ x ∧ w ≠ x)) finset.univ).card = 2,
      { simp_rw [not_and_distrib, not_not, finset.filter_or],
        convert_to finset.card (insert v {w}) = 2,
        { congr' 1,
          ext; simp,
          split,
          { intros h,
            cases h with av aw,
            { rw ← av,
              refine finset.mem_insert_self v {w} },
            { rw ← aw,
              rw finset.insert_singleton_comm,
              refine finset.mem_insert_self w {v} } },
          intros h,
          finish },
        rw finset.card_insert_of_not_mem,
        { refl },
        { rw finset.not_mem_singleton,
          apply ne_of_adj _ h } },
      apply @nat.add_right_cancel _ 2 _,
      rw nat.sub_add_cancel,
      { rw ← finset.card_univ,
        change (finset.filter (λ (x : V), v ≠ x ∧ w ≠ x) finset.univ).card + 2 = finset.univ.card,
        rw [← h2, finset.filter_card_add_filter_neg_card_eq_card] },
      { rw [← h2, ← finset.card_univ],
        apply finset.card_filter_le },
    end,
  nadj_common := λ v w h,
    begin
      cases h with hnadj hne,
      rw [complete_graph, not_not] at hnadj,
      exfalso,
      apply hne hnadj,
    end }

end simple_graph
