/-
Copyright (c) 2021 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alena Gusakov
-/
import combinatorics.simple_graph.basic
/-!
# Strongly regular graphs

## Main definitions

* `common_neighbors` is the intersection of the neighbor sets of two given vertices

* `G.is_SRG_of n k l m` is a structure for a `simple_graph` with conditions
  * The cardinality of the vertex set is `n`
  * `G` is a regular graph with degree `k`
  * The number of common neighbors between any two adjacent vertices in `G` is `l`
  * The number of common neighbors between any two nonadjacent vertices in `G` is `m`

TODO:
- Prove that the complement of a strongly regular graph is strongly regular

- Prove that the parameters of a strongly regular graph
  obey relation `(n - k - 1) * m = k * (k - l - 1)`

- Prove that if I is the identity matrix and J is the all-one matrix,
  then the adj matrix A of SRG obeys relation A^2 = kI + lA + m(J - I - A)

TODO: Part of this would include defining the complement of a graph

-/
universes u

namespace simple_graph
variables {V : Type u} [fintype V]
variables (G : simple_graph V)

/--
The set of common neighbors between two vertices `v` and `w` in a graph `G` is the
intersection of the neighbor sets of `v` and `w`.
-/
def common_neighbors (v w : V) : set V := (G.neighbor_set v) ∩ (G.neighbor_set w)

lemma common_neighbors_eq_inter (v w : V) :
  G.common_neighbors v w = (G.neighbor_set v) ∩ (G.neighbor_set w) := rfl

lemma not_mem_left_common_neighbors (v w : V) : v ∉ (G.common_neighbors v w) :=
begin
  rw common_neighbors,
  simp only [set.mem_inter_eq, irrefl, mem_neighbor_set, not_false_iff, false_and],
end

lemma not_mem_right_common_neighbors (v w : V) : w ∉ (G.common_neighbors v w) :=
begin
  rw common_neighbors,
  simp,
end

variables  [locally_finite G]

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

lemma degree_lt_card_verts (G : simple_graph V) (v : V) : G.degree v < fintype.card V :=
begin
  classical,
  rw ← finset.card_univ,
  rw degree,
  apply finset.card_lt_card,
  rw finset.ssubset_iff,
  use v,
  split,
  { simp },
  { apply finset.subset_univ },
end

variables [nonempty V]

lemma is_regular_degree_lt_card_verts (G : simple_graph V) (k : ℕ) (h : G.is_regular_of_degree k) :
  k < fintype.card V :=
begin
  rw is_regular_of_degree at h,
  inhabit V,
  specialize h (default V),
  rw ← h,
  apply degree_lt_card_verts,
end

lemma common_neighbors_subset_neighbor_set (v w : V) : G.common_neighbors v w ⊆ G.neighbor_set v :=
begin
  rw common_neighbors_eq_inter,
  exact set.inter_subset_left _ _,
end

lemma set.to_finset_subset_to_finset_iff (α : Type*) (s t : set α) [fintype s] [fintype t] :
  s ⊆ t ↔ s.to_finset ⊆ t.to_finset :=
⟨λ h x hx, set.mem_to_finset.mpr $ h $ set.mem_to_finset.mp hx,
λ h x hx, set.mem_to_finset.mp $ h $ set.mem_to_finset.mpr hx⟩

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
  rw ← set.to_finset_subset_to_finset_iff _ _,
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
      rw ← set.to_finset_subset_to_finset_iff,
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


end simple_graph
