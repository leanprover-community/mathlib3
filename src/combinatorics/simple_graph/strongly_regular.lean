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
  `is_SRG_of n (n - k - 1) (n - 2 - 2k + m) (v - 2k + l)`
- Prove that the parameters of a strongly regular graph
  obey the relation `(n - k - 1) * m = k * (k - l - 1)`
- Prove that if `I` is the identity matrix and `J` is the all-one matrix,
  then the adj matrix `A` of SRG obeys relation `A^2 = kI + lA + m(J - I - A)`
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

open finset

/-- Complete graphs are strongly regular. Note that the parameter `m` can take any value
  for complete graphs, since there are no distinct pairs of nonadjacent vertices. -/
lemma complete_strongly_regular (m : ℕ) :
  (⊤ : simple_graph V).is_SRG_of (fintype.card V) (fintype.card V - 1) (fintype.card V - 2) m :=
{ card := rfl,
  regular := complete_graph_degree,
  adj_common := λ v w (h : v ≠ w),
    begin
      simp only [fintype.card_of_finset, mem_common_neighbors, filter_not, ←not_or_distrib,
                 filter_eq, filter_or, card_univ_diff, mem_univ, if_pos, ←insert_eq, top_adj],
      rw [card_insert_of_not_mem, card_singleton],
      simp [h]
    end,
  nadj_common := λ v w (h : ¬(v ≠ w) ∧ _), (h.1 h.2).elim }

end simple_graph
