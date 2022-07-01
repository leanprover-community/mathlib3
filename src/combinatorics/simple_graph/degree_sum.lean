/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.basic
import algebra.big_operators.basic
import data.nat.parity
import data.zmod.parity

/-!
# Degree-sum formula and handshaking lemma

The degree-sum formula is that the sum of the degrees of the vertices in
a finite graph is equal to twice the number of edges.  The handshaking lemma,
a corollary, is that the number of odd-degree vertices is even.

## Main definitions

- `simple_graph.sum_degrees_eq_twice_card_edges` is the degree-sum formula.
- `simple_graph.even_card_odd_degree_vertices` is the handshaking lemma.
- `simple_graph.odd_card_odd_degree_vertices_ne` is that the number of odd-degree
  vertices different from a given odd-degree vertex is odd.
- `simple_graph.exists_ne_odd_degree_of_exists_odd_degree` is that the existence of an
  odd-degree vertex implies the existence of another one.

## Implementation notes

We give a combinatorial proof by using the facts that (1) the map from
darts to vertices is such that each fiber has cardinality the degree
of the corresponding vertex and that (2) the map from darts to edges is 2-to-1.

## Tags

simple graphs, sums, degree-sum formula, handshaking lemma
-/
open finset

open_locale big_operators

namespace simple_graph
universes u
variables {V : Type u} (G : simple_graph V)

section degree_sum
variables [fintype V] [decidable_rel G.adj]

lemma dart_fst_fiber [decidable_eq V] (v : V) :
  univ.filter (λ d : G.dart, d.fst = v) = univ.image (G.dart_of_neighbor_set v) :=
begin
  ext d,
  simp only [mem_image, true_and, mem_filter, set_coe.exists, mem_univ, exists_prop_of_true],
  split,
  { rintro rfl,
    exact ⟨_, d.is_adj, by ext; refl⟩, },
  { rintro ⟨e, he, rfl⟩,
    refl, },
end

lemma dart_fst_fiber_card_eq_degree [decidable_eq V] (v : V) :
  (univ.filter (λ d : G.dart, d.fst = v)).card = G.degree v :=
by simpa only [dart_fst_fiber, finset.card_univ, card_neighbor_set_eq_degree]
     using card_image_of_injective univ (G.dart_of_neighbor_set_injective v)

lemma dart_card_eq_sum_degrees : fintype.card G.dart = ∑ v, G.degree v :=
begin
  haveI := classical.dec_eq V,
  simp only [←card_univ, ←dart_fst_fiber_card_eq_degree],
  exact card_eq_sum_card_fiberwise (by simp),
end

variables {G} [decidable_eq V]

lemma dart.edge_fiber (d : G.dart) :
  (univ.filter (λ (d' : G.dart), d'.edge = d.edge)) = {d, d.symm} :=
finset.ext (λ d', by simpa using dart_edge_eq_iff d' d)

variables (G)

lemma dart_edge_fiber_card (e : sym2 V) (h : e ∈ G.edge_set) :
  (univ.filter (λ (d : G.dart), d.edge = e)).card = 2 :=
begin
  refine sym2.ind (λ v w h, _) e h,
  let d : G.dart := ⟨(v, w), h⟩,
  convert congr_arg card d.edge_fiber,
  rw [card_insert_of_not_mem, card_singleton],
  rw [mem_singleton],
  exact d.symm_ne.symm,
end

lemma dart_card_eq_twice_card_edges : fintype.card G.dart = 2 * G.edge_finset.card :=
begin
  rw ←card_univ,
  rw @card_eq_sum_card_fiberwise _ _ _ dart.edge _ G.edge_finset
    (λ d h, by { rw mem_edge_finset, apply dart.edge_mem }),
  rw [←mul_comm, sum_const_nat],
  intros e h,
  apply G.dart_edge_fiber_card e,
  rwa ←mem_edge_finset,
end

/-- The degree-sum formula.  This is also known as the handshaking lemma, which might
more specifically refer to `simple_graph.even_card_odd_degree_vertices`. -/
theorem sum_degrees_eq_twice_card_edges : ∑ v, G.degree v = 2 * G.edge_finset.card :=
G.dart_card_eq_sum_degrees.symm.trans G.dart_card_eq_twice_card_edges

end degree_sum

/-- The handshaking lemma.  See also `simple_graph.sum_degrees_eq_twice_card_edges`. -/
theorem even_card_odd_degree_vertices [fintype V] [decidable_rel G.adj] :
  even (univ.filter (λ v, odd (G.degree v))).card :=
begin
  classical,
  have h := congr_arg ((λ n, ↑n) : ℕ → zmod 2) G.sum_degrees_eq_twice_card_edges,
  simp only [zmod.nat_cast_self, zero_mul, nat.cast_mul] at h,
  rw [nat.cast_sum, ←sum_filter_ne_zero] at h,
  rw @sum_congr _ _ _ _ (λ v, (G.degree v : zmod 2)) (λ v, (1 : zmod 2)) _ rfl at h,
  { simp only [filter_congr_decidable, mul_one, nsmul_eq_mul, sum_const, ne.def] at h,
    rw ←zmod.eq_zero_iff_even,
    convert h,
    ext v,
    rw ←zmod.ne_zero_iff_odd, },
  { intros v,
    simp only [true_and, mem_filter, mem_univ, ne.def],
    rw [zmod.eq_zero_iff_even, zmod.eq_one_iff_odd, nat.odd_iff_not_even, imp_self],
    trivial }
end

lemma odd_card_odd_degree_vertices_ne [fintype V] [decidable_eq V] [decidable_rel G.adj]
  (v : V) (h : odd (G.degree v)) :
  odd (univ.filter (λ w, w ≠ v ∧ odd (G.degree w))).card :=
begin
  rcases G.even_card_odd_degree_vertices with ⟨k, hg⟩,
  have hk : 0 < k,
  { have hh : (filter (λ (v : V), odd (G.degree v)) univ).nonempty,
    { use v,
      simp only [true_and, mem_filter, mem_univ],
      use h, },
    rwa [←card_pos, hg, ← two_mul, zero_lt_mul_left] at hh,
    exact zero_lt_two, },
  have hc : (λ (w : V), w ≠ v ∧ odd (G.degree w)) = (λ (w : V), odd (G.degree w) ∧ w ≠ v),
  { ext w,
    rw and_comm, },
  simp only [hc, filter_congr_decidable],
  rw [←filter_filter, filter_ne', card_erase_of_mem],
  { refine ⟨k - 1, tsub_eq_of_eq_add $ hg.trans _⟩,
    rw [add_assoc, one_add_one_eq_two, ←nat.mul_succ, ← two_mul],
    congr,
    exact (tsub_add_cancel_of_le $ nat.succ_le_iff.2 hk).symm },
  { simpa only [true_and, mem_filter, mem_univ] },
end

lemma exists_ne_odd_degree_of_exists_odd_degree [fintype V] [decidable_rel G.adj]
  (v : V) (h : odd (G.degree v)) :
  ∃ (w : V), w ≠ v ∧ odd (G.degree w) :=
begin
  haveI := classical.dec_eq V,
  rcases G.odd_card_odd_degree_vertices_ne v h with ⟨k, hg⟩,
  have hg' : (filter (λ (w : V), w ≠ v ∧ odd (G.degree w)) univ).card > 0,
  { rw hg,
    apply nat.succ_pos, },
  rcases card_pos.mp hg' with ⟨w, hw⟩,
  simp only [true_and, mem_filter, mem_univ, ne.def] at hw,
  exact ⟨w, hw⟩,
end

end simple_graph
