/-
Copyright (c) 2021 Gabriel Moise. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Moise, Yaël Dillies, Kyle Miller
-/
import combinatorics.simple_graph.basic
import data.matrix.basic

/-!
# Incidence matrix of a simple graph

This file defines the unoriented incidence matrix of a simple graph.

## Main definitions

* `simple_graph.inc_matrix`: `G.inc_matrix R` is the incidence matrix of `G` over the ring `R`.

## Main results

* `simple_graph.inc_matrix_mul_transpose_diag`: The diagonal entries of the product of
  `G.inc_matrix R` and its transpose are the degrees of the vertices.
* `simple_graph.inc_matrix_mul_transpose`: Gives a complete description of the product of
  `G.inc_matrix R` and its transpose; the diagonal is the degrees of each vertex, and the
  off-diagonals are 1 or 0 depending on whether or not the vertices are adjacent.
* `simple_graph.inc_matrix_transpose_mul_diag`: The diagonal entries of the product of the
  transpose of `G.inc_matrix R` and `G.inc_matrix R` are `2` or `0` depending on whether or
  not the unordered pair is an edge of `G`.

## Implementation notes

The usual definition of an incidence matrix has one row per vertex and one column per edge.
However, this definition has columns indexed by all of `sym2 α`, where `α` is the vertex type.
This appears not to change the theory, and for simple graphs it has the nice effect that every
incidence matrix for each `simple_graph α` has the same type.

## TODO

* Define the oriented incidence matrices for oriented graphs.
* Define the graph Laplacian of a simple graph using the oriented incidence matrix from an
  arbitrary orientation of a simple graph.
-/

open finset matrix simple_graph sym2
open_locale big_operators matrix

namespace simple_graph
variables (R : Type*) {α : Type*} (G : simple_graph α)

/-- `G.inc_matrix R` is the `α × sym2 α` matrix whose `(a, e)`-entry is `1` if `e` is incident to
`a` and `0` otherwise. -/
noncomputable def inc_matrix [has_zero R] [has_one R] : matrix α (sym2 α) R :=
λ a, (G.incidence_set a).indicator 1

variables {R}

lemma inc_matrix_apply [has_zero R] [has_one R] {a : α} {e : sym2 α} :
  G.inc_matrix R a e = (G.incidence_set a).indicator 1 e := rfl

/-- Entries of the incidence matrix can be computed given additional decidable instances. -/
lemma inc_matrix_apply' [has_zero R] [has_one R] [decidable_eq α] [decidable_rel G.adj]
  {a : α} {e : sym2 α} :
  G.inc_matrix R a e = if e ∈ G.incidence_set a then 1 else 0 :=
by convert rfl

section mul_zero_one_class
variables [mul_zero_one_class R] {a b : α} {e : sym2 α}

lemma inc_matrix_apply_mul_inc_matrix_apply :
  G.inc_matrix R a e * G.inc_matrix R b e = (G.incidence_set a ∩ G.incidence_set b).indicator 1 e :=
begin
  classical,
  simp only [inc_matrix, set.indicator_apply, ←ite_and_mul_zero,
    pi.one_apply, mul_one, set.mem_inter_eq],
end

lemma inc_matrix_apply_mul_inc_matrix_apply_of_not_adj (hab : a ≠ b) (h : ¬ G.adj a b) :
  G.inc_matrix R a e * G.inc_matrix R b e = 0 :=
begin
  rw [inc_matrix_apply_mul_inc_matrix_apply, set.indicator_of_not_mem],
  rw [G.incidence_set_inter_incidence_set_of_not_adj h hab],
  exact set.not_mem_empty e,
end

lemma inc_matrix_of_not_mem_incidence_set (h : e ∉ G.incidence_set a) :
  G.inc_matrix R a e = 0 :=
by rw [inc_matrix_apply, set.indicator_of_not_mem h]

lemma inc_matrix_of_mem_incidence_set (h : e ∈ G.incidence_set a) : G.inc_matrix R a e = 1 :=
by rw [inc_matrix_apply, set.indicator_of_mem h, pi.one_apply]

variables [nontrivial R]

lemma inc_matrix_apply_eq_zero_iff : G.inc_matrix R a e = 0 ↔ e ∉ G.incidence_set a :=
begin
  simp only [inc_matrix_apply, set.indicator_apply_eq_zero, pi.one_apply, one_ne_zero],
  exact iff.rfl,
end

lemma inc_matrix_apply_eq_one_iff : G.inc_matrix R a e = 1 ↔ e ∈ G.incidence_set a :=
by { convert one_ne_zero.ite_eq_left_iff, assumption }

end mul_zero_one_class

section non_assoc_semiring
variables [fintype α] [non_assoc_semiring R] {a b : α} {e : sym2 α}

lemma sum_inc_matrix_apply [decidable_eq α] [decidable_rel G.adj] :
  ∑ e, G.inc_matrix R a e = G.degree a :=
by simp [inc_matrix_apply', sum_boole, set.filter_mem_univ_eq_to_finset]

lemma inc_matrix_mul_transpose_diag [decidable_eq α] [decidable_rel G.adj] :
  (G.inc_matrix R ⬝ (G.inc_matrix R)ᵀ) a a = G.degree a :=
begin
  rw ←sum_inc_matrix_apply,
  simp [matrix.mul_apply, inc_matrix_apply', ←ite_and_mul_zero],
end

lemma sum_inc_matrix_apply_of_mem_edge_set : e ∈ G.edge_set → ∑ a, G.inc_matrix R a e = 2 :=
begin
  classical,
  refine e.ind _,
  intros a b h,
  rw mem_edge_set at h,
  rw [←nat.cast_two, ←card_doubleton h.ne],
  simp only [inc_matrix_apply', sum_boole, mk_mem_incidence_set_iff, h, true_and],
  congr' 2,
  ext e,
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton],
end

lemma sum_inc_matrix_apply_of_not_mem_edge_set (h : e ∉ G.edge_set) : ∑ a, G.inc_matrix R a e = 0 :=
sum_eq_zero $ λ a _, G.inc_matrix_of_not_mem_incidence_set $ λ he, h he.1

lemma inc_matrix_transpose_mul_diag [decidable_rel G.adj] :
  ((G.inc_matrix R)ᵀ ⬝ G.inc_matrix R) e e = if e ∈ G.edge_set then 2 else 0 :=
begin
  classical,
  simp only [matrix.mul_apply, inc_matrix_apply', transpose_apply, ←ite_and_mul_zero,
    one_mul, sum_boole, and_self],
  split_ifs with h,
  { revert h,
    refine e.ind _,
    intros v w h,
    rw [←nat.cast_two, ←card_doubleton (G.ne_of_adj h)],
    simp [mk_mem_incidence_set_iff, G.mem_edge_set.mp h],
    congr' 2,
    ext u,
    simp, },
  { revert h,
    refine e.ind _,
    intros v w h,
    simp [mk_mem_incidence_set_iff, G.mem_edge_set.not.mp h], },
end

end non_assoc_semiring

section semiring
variables [fintype (sym2 α)] [semiring R] {a b : α} {e : sym2 α}

lemma inc_matrix_mul_transpose_apply_of_adj (h : G.adj a b) :
  (G.inc_matrix R ⬝ (G.inc_matrix R)ᵀ) a b = (1 : R) :=
begin
  classical,
  simp_rw [matrix.mul_apply, matrix.transpose_apply, inc_matrix_apply_mul_inc_matrix_apply,
    set.indicator_apply, pi.one_apply, sum_boole],
  convert nat.cast_one,
  convert card_singleton ⟦(a, b)⟧,
  rw [←coe_eq_singleton, coe_filter_univ],
  exact G.incidence_set_inter_incidence_set_of_adj h,
end

lemma inc_matrix_mul_transpose [fintype α] [decidable_eq α] [decidable_rel G.adj] :
  G.inc_matrix R ⬝ (G.inc_matrix R)ᵀ = λ a b,
    if a = b then G.degree a else if G.adj a b then 1 else 0 :=
begin
  ext a b,
  split_ifs with h h',
  { subst b,
    convert G.inc_matrix_mul_transpose_diag },
  { exact G.inc_matrix_mul_transpose_apply_of_adj h' },
  { simp only [matrix.mul_apply, matrix.transpose_apply,
    G.inc_matrix_apply_mul_inc_matrix_apply_of_not_adj h h', sum_const_zero] }
end

end semiring
end simple_graph
