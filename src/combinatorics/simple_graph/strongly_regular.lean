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
- Define the complement of a graph
- Prove that the complement of a strongly regular graph is strongly regular
- Prove that the parameters of a strongly regular graph
  obey relation `(n - k - 1) * m = k * (k - l - 1)`
- Prove that if I is the identity matrix and J is the all-one matrix,
  then the adj matrix A of SRG obeys relation A^2 = kI + lA + m(J - I - A)
-/

-- CR : depends on
  -- graph_compl (#5697)
  -- graph_common_neighbors (#5718)
  -- to_finset_subset (#5725)

universes u

namespace simple_graph
variables {V : Type u}
variables (G : simple_graph V)

variables  [fintype V] [locally_finite G]

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
(nadj_common : ∀ (v w : V), ¬ G.adj v w → fintype.card (G.common_neighbors v w) = m)

lemma card_common_neighbors_le_degree (v w : V) :
  fintype.card (G.common_neighbors v w) ≤ G.degree v :=
begin
  rw degree,
  have h := G.common_neighbors_subset_neighbor_set v w,
  rw common_neighbors,
  rw ← set.to_finset_card,
  apply finset.card_le_of_subset,
  rw common_neighbors at h,
  rw neighbor_finset,
  rw ← set.subset_iff_to_finset_subset _ _,
  exact h,
end

lemma card_common_neighbors_lt_card_verts (G : simple_graph V) (v w : V) :
  fintype.card (G.common_neighbors v w) < fintype.card V :=
begin
  classical,
  have h := not_mem_left_common_neighbors G v w,
  rw ← set.to_finset_card,
  rw ← finset.card_univ,
  apply finset.card_lt_card,
  rw finset.ssubset_iff,
  use v,
  split,
  { simp,
    exact h },
  { apply finset.subset_univ },
end

lemma adj_card_common_neighbors_lt_degree (v w : V) (h : G.adj v w) :
  fintype.card (G.common_neighbors v w) < G.degree v :=
begin
  classical,
  rw degree,
  rw ← set.to_finset_card,
  apply finset.card_lt_card,
  rw finset.ssubset_iff,
  use w,
  split,
  { rw set.mem_to_finset,
    exact not_mem_right_common_neighbors G v w },
  { rw finset.insert_subset,
    split,
    { simpa },
    { rw neighbor_finset,
      rw ← set.subset_iff_to_finset_subset,
      exact common_neighbors_subset_neighbor_set G v w } },
end


lemma card_common_neighbors_le_regular_degree (v w : V) (k : ℕ) (h : G.is_regular_of_degree k) :
  fintype.card (G.common_neighbors v w) ≤ k :=
begin
  rw is_regular_of_degree at h,
  specialize h v,
  rw ← h,
  exact card_common_neighbors_le_degree G v w
end

lemma adj_card_common_neighbors_lt_regular_degree (v w : V) (h : G.adj v w) (k : ℕ)
  (h2 : G.is_regular_of_degree k) : fintype.card (G.common_neighbors v w) < k :=
begin
  rw is_regular_of_degree at h2,
  specialize h2 v,
  rw ← h2,
  exact G.adj_card_common_neighbors_lt_degree v w h,
end

lemma is_regular_degree_lt_card_verts [nonempty V] (G : simple_graph V) (k : ℕ) (h : G.is_regular_of_degree k) :
  k < fintype.card V :=
begin
  rw is_regular_of_degree at h,
  inhabit V,
  specialize h (default V),
  rw ← h,
  apply degree_lt_card_verts,
end


end simple_graph
