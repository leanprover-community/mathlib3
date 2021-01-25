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

-- CR : depends on
  -- graph_compl (#5697) `done`
  -- common_neighbor_card `PRed`
    -- graph_common_neighbors (#5718) `done`
  -- to_finset_subset (#5725) `done`

universes u

namespace simple_graph
variables {V : Type u}
variables (G : simple_graph V)

variables  [fintype V]

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

-- these aren't necessary i guess?
lemma card_common_neighbors_le_regular_degree (v w : V) (k : ℕ) (h : G.is_regular_of_degree k) :
  fintype.card (G.common_neighbors v w) ≤ k :=
begin
  rw is_regular_of_degree at h,
  specialize h v,
  rw ← h,
  exact card_common_neighbors_le_degree_left G v w
end

lemma adj_card_common_neighbors_lt_regular_degree (v w : V) (h : G.adj v w) (k : ℕ)
  (h2 : G.is_regular_of_degree k) : fintype.card (G.common_neighbors v w) < k :=
begin
  rw is_regular_of_degree at h2,
  specialize h2 v,
  rw ← h2,
  exact adj.card_common_neighbors_lt_degree h,
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
