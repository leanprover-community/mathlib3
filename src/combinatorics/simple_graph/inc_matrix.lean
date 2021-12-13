/-
Copyright (c) 2021 Gabriel Moise. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Moise, Yaël Dillies
-/
import combinatorics.simple_graph.basic
import data.matrix.basic

/-!
# Incidence matrix of a simple graph

This file defines the incidence matrix of a simple graph.

## Main definitions

* `simple_graph.inc_matrix`: `G.inc_matrix R` is the incidence matrix of `G` in ring `R`.

## Main results

* `inc_matrix_element_power_id`: Every element from `M` is idempotent.
* `degree_equals_sum_of_incidence_row`: The sum of elements from row `i` of `M` is equal to the
`degree` of vertex `i`.

## TODO

Define the incidence matrix of an oriented graph.
-/

open_locale big_operators matrix
open finset matrix simple_graph sym2

section to_move

@[simp] lemma ite_zero_mul_ite_zero_right {R : Type*} [mul_zero_class R] {P Q : Prop} [decidable P]
  [decidable Q] (a b : R) :
  (ite P a 0) * (ite Q b 0) = ite (P ∧ Q) (a * b) 0 :=
by simp [←ite_and]

end to_move

variables {R α : Type*}

namespace simple_graph
variables [decidable_eq α] (G : simple_graph α) [decidable_rel G.adj] (R)

/-- `G.inc_matrix R` is the `α × sym2 α` matrix whose `(a, e)`-entry is `1` if `e` is incident to
`a` and `0` else. -/
def inc_matrix [has_zero R] [has_one R] : matrix α (sym2 α) R :=
λ a e, if e ∈ G.incidence_set a then 1 else 0

@[simp]
lemma inc_matrix_apply {a : α} {e : sym2 α} [has_zero R] [has_one R] :
  G.inc_matrix R a e = if e ∈ G.incidence_set a then 1 else 0 := rfl

section mul_zero_one_class
variables [mul_zero_one_class R] {a b : α} {e : sym2 α}

lemma inc_matrix_apply_mul_inc_matrix_apply :
  G.inc_matrix R a e * G.inc_matrix R b e = if (e ∈ G.incidence_set a ∧ e ∈ G.incidence_set b)
    then 1 else 0 :=
by rw [inc_matrix, ite_zero_mul_ite_zero_right _ _, mul_one]

lemma inc_matrix_apply_mul_inc_matrix_apply_of_not_adj (hab : a ≠ b) (h : ¬G.adj a b) :
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
  rw ←card_incidence_set_eq_degree,
  congr' 1,
  refine eq.trans _ (finset.card_map ⟨@subtype.val _ (G.incidence_set a), subtype.val_injective⟩),
  congr,
  ext e,
  simp only [true_and, exists_prop, mem_filter, set_coe.exists, mem_univ, exists_eq_right,
    function.embedding.coe_fn_mk, mem_map, subtype.coe_mk],
end

end non_assoc_semiring

section semiring
variables [fintype α] [semiring R] {a b : α} {e : sym2 α}

lemma sum_inc_matrix_apply_mul_inc_matrix_apply_of_adj (h : G.adj a b) :
  ∑ e, G.inc_matrix R a e * G.inc_matrix R b e = (1 : R) :=
begin
  simp_rw inc_matrix_apply_mul_inc_matrix_apply,
  rw sum_boole,
  convert nat.cast_one,
  convert card_singleton ⟦(a, b)⟧,
  rw [←coe_eq_singleton, coe_filter_univ],
  exact G.incidence_set_inter_incidence_set h,
end

end semiring
end simple_graph
