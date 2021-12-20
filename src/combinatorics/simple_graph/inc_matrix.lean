/-
Copyright (c) 2021 Gabriel Moise. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Moise, Yaël Dillies
-/
import combinatorics.simple_graph.basic
import data.matrix.basic

/-!
# Incidence matrix of a simple graph

This file defines the unoriented incidence matrix of a simple graph.

## Main definitions

* `simple_graph.inc_matrix`: `G.inc_matrix R` is the incidence matrix of `G` over the ring `R`.

## Main results

* `inc_matrix_element_power_id`: Every element from `M` is idempotent.
* `degree_equals_sum_of_incidence_row`: The sum of elements from row `i` of `G.inc_matrix R`
is equal to the `degree` of vertex `i`.
* `simple_graph.inc_matrix_mul_transpose`: Gives a complete description of the product of
`G.inc_matrix R` and its transpose; the diagonal is the degrees of each vertex, and the
off-diagonals are 1 or 0 depending on whether or not the vertices are adjacent.

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

open_locale big_operators matrix
open finset matrix simple_graph sym2

@[simp] lemma ite_zero_mul_ite_zero_right {R : Type*} [mul_zero_class R] {P Q : Prop} [decidable P]
  [decidable Q] (a b : R) :
  (ite P a 0) * (ite Q b 0) = ite (P ∧ Q) (a * b) 0 :=
by simp [←ite_and]

variables {R α : Type*}

namespace simple_graph
variables [decidable_eq α] (G : simple_graph α) [decidable_rel G.adj] (R)

/-- `G.inc_matrix R` is the `α × sym2 α` matrix whose `(a, e)`-entry is `1` if `e` is incident to
`a` and `0` otherwise. -/
def inc_matrix [has_zero R] [has_one R] : matrix α (sym2 α) R :=
λ a e, if e ∈ G.incidence_set a then 1 else 0

variables {R}

@[simp]
lemma inc_matrix_apply {a : α} {e : sym2 α} [has_zero R] [has_one R] :
  G.inc_matrix R a e = if e ∈ G.incidence_set a then 1 else 0 := rfl

section mul_zero_one_class
variables [mul_zero_one_class R] {a b : α} {e : sym2 α}

lemma inc_matrix_apply_mul_inc_matrix_apply :
  G.inc_matrix R a e * G.inc_matrix R b e =
    if (e ∈ G.incidence_set a ∧ e ∈ G.incidence_set b) then 1 else 0 :=
by rw [inc_matrix, ite_zero_mul_ite_zero_right _ _, mul_one]

lemma inc_matrix_apply_mul_inc_matrix_apply_of_not_adj (hab : a ≠ b) (h : ¬ G.adj a b) :
  G.inc_matrix R a e * G.inc_matrix R b e = 0 :=
begin
  rw [inc_matrix_apply_mul_inc_matrix_apply, if_neg],
  exact λ h', h (G.adj_of_mem_incidence_set hab h'.1 h'.2),
end

variables [nontrivial R]

lemma inc_matrix_apply_eq_zero_iff : G.inc_matrix R a e = 0 ↔ e ∉ G.incidence_set a :=
one_ne_zero.ite_eq_right_iff

lemma inc_matrix_apply_eq_one_iff : G.inc_matrix R a e = 1 ↔ e ∈ G.incidence_set a :=
one_ne_zero.ite_eq_left_iff

end mul_zero_one_class

section non_assoc_semiring
variables [fintype α] [non_assoc_semiring R] {a b : α} {e : sym2 α}

/-- The sum of elements from row `a` of the incidence matrix is equal to the degree of vertex `a`.
-/
lemma sum_inc_matrix_apply : ∑ e, G.inc_matrix R a e = G.degree a :=
begin
  simp only [inc_matrix_apply, sum_boole],
  apply congr_arg,
  rw ←card_incidence_finset_eq_degree,
  congr' 1,
  ext e,
  simp,
end

lemma inc_matrix_mul_transpose_diag : (G.inc_matrix R ⬝ (G.inc_matrix R)ᵀ) a a = G.degree a :=
begin
  rw ←sum_inc_matrix_apply,
  simp only [matrix.mul_apply, matrix.transpose_apply, ite_zero_mul_ite_zero_right,
    inc_matrix_apply, and_self, mul_one],
  congr,
  ext,
  congr,
end

end non_assoc_semiring

section semiring
variables [fintype α] [semiring R] {a b : α} {e : sym2 α}

lemma inc_matrix_mul_transpose_apply_of_adj (h : G.adj a b) :
  (G.inc_matrix R ⬝ (G.inc_matrix R)ᵀ) a b = (1 : R) :=
begin
  simp_rw [matrix.mul_apply, matrix.transpose_apply, inc_matrix_apply_mul_inc_matrix_apply],
  rw sum_boole,
  convert nat.cast_one,
  convert card_singleton ⟦(a, b)⟧,
  rw [←coe_eq_singleton, coe_filter_univ],
  exact G.incidence_set_inter_incidence_set h,
end

lemma inc_matrix_mul_transpose :
  G.inc_matrix R ⬝ (G.inc_matrix R)ᵀ = λ a b,
    if a = b then G.degree a else if G.adj a b then 1 else 0 :=
begin
  ext a b,
  split_ifs with h h',
  { subst b,
    exact G.inc_matrix_mul_transpose_diag },
  { exact G.inc_matrix_mul_transpose_apply_of_adj h' },
  { simp only [matrix.mul_apply, matrix.transpose_apply,
    G.inc_matrix_apply_mul_inc_matrix_apply_of_not_adj h h', sum_const_zero] }
end

end semiring
end simple_graph
