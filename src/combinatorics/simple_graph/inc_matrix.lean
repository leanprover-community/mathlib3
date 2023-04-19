/-
Copyright (c) 2021 Gabriel Moise. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Moise, Yaël Dillies, Kyle Miller
-/
import combinatorics.simple_graph.basic
import data.matrix.basic

/-!
# Incidence matrix of a simple graph

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the unoriented incidence matrix of a simple graph and provides theorems and lemmas
connecting graph properties to computational properties of the matrix. It also defines the notion of
orientation for a simple graph, picking a direction for each undirected edge in the graph and then
defining the oriented incidence matrix based on that.

## Main definitions

* `simple_graph.inc_matrix`: `G.inc_matrix R` is the incidence matrix of `G` over the ring `R`.
* `simple_graph.orientation`: A choice of direction on the edges of a `simple_graph`.
* `simple_graph.oriented_inc_matrix`: The oriented incidence matrix of a `simple_graph` with
  respect to a given `orientation`.

## Main results

* `simple_graph.inc_matrix_mul_transpose_diag`: The diagonal entries of the product of
  `G.inc_matrix R` and its transpose are the degrees of the vertices.
* `simple_graph.inc_matrix_mul_transpose`: Gives a complete description of the product of
  `G.inc_matrix R` and its transpose; the diagonal is the degrees of each vertex, and the
  off-diagonals are 1 or 0 depending on whether or not the vertices are adjacent.
* `simple_graph.inc_matrix_transpose_mul_diag`: The diagonal entries of the product of the
  transpose of `G.inc_matrix R` and `G.inc_matrix R` are `2` or `0` depending on whether or
  not the unordered pair is an edge of `G`.
* `oriented_inc_matrix_elem_squared`: The square of each element from `oriented_inc_matrix` is equal
  to the corresponding element from `inc_matrix`.
* `vec_mul_oriented_inc_matrix`: `(xᵀ ⬝ oriented_inc_matrix) e = x o.head e - x o.tail e`.

## Implementation notes

The usual definition of an incidence matrix has one row per vertex and one column per edge.
However, this definition has columns indexed by all of `sym2 α`, where `α` is the vertex type.
This appears not to change the theory, and for simple graphs it has the nice effect that every
incidence matrix for each `simple_graph α` has the same type.

## TODO

* Define the oriented incidence matrices for oriented graphs.
* Define the graph Laplacian of a simple graph using the oriented incidence matrix from an
  arbitrary orientation of a simple graph.

## References

<https://en.wikipedia.org/wiki/Orientation_(graph_theory)>
-/

open finset matrix simple_graph sym2
open_locale big_operators matrix

section
variables {α : Type*}  {p q : Prop} [decidable p] [decidable q] {a b c : α}

lemma ite_assoc : ite p a (ite q b c) = ite (p ∨ q) (ite p a b) c := by split_ifs; tauto
lemma ite_assoc' : ite p (ite q a b) c = ite (p ∧ q) a (ite p b c) := by split_ifs; tauto

end

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
    pi.one_apply, mul_one, set.mem_inter_iff],
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
by { convert one_ne_zero.ite_eq_left_iff, apply_instance }

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

/-! ## Orientations -/

section orientations

/-- Define an `orientation` on the simple graph `G` as a structure that defines (consistently)
for each edge a `head` and a `tail`. -/
@[ext]
structure orientation (G : simple_graph α) :=
(head : G.edge_set → α)
(tail : G.edge_set → α)
(consistent (e : G.edge_set) : ↑e = ⟦(head e, tail e)⟧)

noncomputable instance (G : simple_graph α) : inhabited (orientation G) :=
⟨{ head := λ (e : G.edge_set), (quotient.out (e : sym2 α)).fst,
  tail := λ (e : G.edge_set), (quotient.out (e : sym2 α)).snd,
  consistent := λ (e : G.edge_set), by rw [prod.mk.eta, quotient.out_eq] }⟩

variables {o : orientation G}

-- lemma head_tail (o : orientation G) (i : α) (e : G.edge_set) :
--   i = o.head e ∨ i = o.tail e ∨ (i ≠ o.head e ∧ i ≠ o.tail e) :=
-- by tauto

lemma edge_not_incident {i j : α} {e : G.edge_set}
  (H_e : ¬↑e = ⟦(i, j)⟧) (H_adj : G.adj i j) : ↑e ∉ G.incidence_set i ∨ ↑e ∉ G.incidence_set j :=
by { by_contra' h, exact H_e (G.incidence_set_inter_incidence_set_subset (G.ne_of_adj H_adj) h) }

lemma head_ne_tail {e : G.edge_set} : o.head e ≠ o.tail e :=
begin
  apply G.ne_of_adj,
  rw [←G.mem_edge_set, ←o.consistent e],
  exact e.property
end

lemma incidence_set_orientation_head {e : G.edge_set} : ↑e ∈ G.incidence_set (o.head e) :=
by { rw [edge_mem_incidence_set_iff, o.consistent e],
  simp only [mem_iff, true_or, eq_self_iff_true] }

lemma incidence_set_orientation_tail {e : G.edge_set} : ↑e ∈ G.incidence_set (o.tail e) :=
by { rw [edge_mem_incidence_set_iff, o.consistent e],
  simp only [mem_iff, eq_self_iff_true, or_true] }

lemma incidence_set_orientation {i : α} {e : G.edge_set} :
  ↑e ∈ G.incidence_set i ↔ i = o.head e ∨ i = o.tail e :=
begin
  rw [o.consistent e, mk_mem_incidence_set_iff, and_iff_right],
  rw [←mem_edge_set, ←o.consistent e],
  exact e.property,
end

lemma not_inc_set_orientation {i : α} {e : G.edge_set} :
  i ≠ o.head e ∧ i ≠ o.tail e ↔ ↑e ∉ G.incidence_set i :=
by { rw G.incidence_set_orientation, tauto }

end orientations

/-! ## Oriented Incidence Matrix -/

section oriented_incidence
variables (R) [decidable_eq α] [ring R] {o : orientation G}

/-- An oriented incidence matrix is defined with respect to the orientation of the edges and is
defined to be `1` for entries (`i`,`e`) where `i` is the head of `e`, `-1` where `i` is the tail of
`e`, and `0` otherwise. -/
@[simp] def oriented_inc_matrix (o : orientation G) : matrix α G.edge_set R :=
λ i e, if i = o.head e then (1 : R) else if i = o.tail e then -1 else 0

lemma oriented_inc_matrix_head {i : α} {e : G.edge_set} (H_head : i = o.head e) :
  G.oriented_inc_matrix R o i e = 1 :=
by simp only [H_head, if_true, eq_self_iff_true, oriented_inc_matrix]

lemma oriented_inc_matrix_tail {i : α} {e : G.edge_set} (H_tail : i = o.tail e) :
  G.oriented_inc_matrix R o i e = -1 :=
by simp only [H_tail, oriented_inc_matrix, G.head_ne_tail.symm, if_false, if_true, eq_self_iff_true]

lemma oriented_inc_matrix_apply_eq_zero_iff {i : α} {e : G.edge_set} [char_zero R] :
  G.oriented_inc_matrix R o i e = 0 ↔ i ≠ o.head e ∧ i ≠ o.tail e :=
begin
  unfold oriented_inc_matrix,
  rw ite_assoc,
  exact (ne.ite_eq_right_iff $ by split_ifs; simp).trans not_or_distrib,
end

lemma oriented_inc_matrix_apply_eq_zero_iff' {i : α} {e : G.edge_set} [char_zero R] :
  G.oriented_inc_matrix R o i e = 0 ↔ ↑e ∉ G.incidence_set i :=
by rw [oriented_inc_matrix_apply_eq_zero_iff, not_inc_set_orientation]

lemma oriented_inc_matrix_non_zero {i : α} {e : G.edge_set} [char_zero R] :
  ¬ G.oriented_inc_matrix R o i e = 0 ↔ i = o.head e ∨ i = o.tail e :=
by rw [←not_iff_not, not_not, oriented_inc_matrix_apply_eq_zero_iff, ←not_or_distrib]

/-- The square of each element from `oriented_inc_matrix` is equal to the corresponding element from
`inc_matrix`. -/
lemma oriented_inc_matrix_elem_squared {i : α} {e : G.edge_set} [char_zero R] :
  G.oriented_inc_matrix R o i e * G.oriented_inc_matrix R o i e = G.inc_matrix R i e :=
begin
  unfold oriented_inc_matrix,
  split_ifs with head tail,
  { rw [head, mul_one, eq_comm, inc_matrix_apply_eq_one_iff],
    exact G.incidence_set_orientation_head },
  { rw [tail, ←sq, neg_one_sq, eq_comm, inc_matrix_apply_eq_one_iff],
    exact G.incidence_set_orientation_tail },
  { rw [mul_zero, eq_comm, inc_matrix_apply_eq_zero_iff],
    exact G.not_inc_set_orientation.mp ⟨head, tail⟩ }
end

lemma oriented_inc_matrix_mul_of_adj {i j : α} {e : G.edge_set} (H_adj : G.adj i j) [char_zero R]:
  G.oriented_inc_matrix R o i e * G.oriented_inc_matrix R o j e = ite (↑e = ⟦(i, j)⟧) (-1) 0 :=
begin
  by_cases H_e : ↑e = ⟦(i, j)⟧,
  { rw [H_e, if_pos rfl],
    rw [o.consistent e, eq_iff] at H_e,
    rcases H_e with (⟨H_head, H_tail⟩ | ⟨H_head, H_tail⟩);
    simp only [G.oriented_inc_matrix_head R, G.oriented_inc_matrix_tail R,
               H_head.symm, H_tail.symm, mul_one, one_mul] },
  { cases (G.edge_not_incident H_e H_adj) with H H;
    simp only [(G.oriented_inc_matrix_apply_eq_zero_iff' R).mpr H,
               zero_mul, mul_zero, H_e, if_false] }
end

lemma oriented_inc_matrix_mul_non_adj {i j : α} {e : G.edge_set} [char_zero R] (H_ij : i ≠ j)
  (H_ne_adj : ¬G.adj i j) : G.oriented_inc_matrix R o i e * G.oriented_inc_matrix R o j e = 0 :=
begin
  by_cases H₁ : G.oriented_inc_matrix R o i e = 0,
  { rw [H₁, zero_mul] },
  { by_cases H₂ : G.oriented_inc_matrix R o j e = 0,
    { rw [H₂, mul_zero] },
    { rcases ((G.oriented_inc_matrix_non_zero R).mp H₁) with (H_head_i | H_tail_i) ;
      rcases ((G.oriented_inc_matrix_non_zero R).mp H₂) with (H_head_j | H_tail_j),
      { rw [H_head_i, H_head_j] at H_ij, tauto },
      { refine (H_ne_adj _).elim,
        rw [H_head_i, H_tail_j, ←mem_edge_set, ←o.consistent e],
        exact e.property },
      { refine (H_ne_adj _).elim,
        rw [H_tail_i, H_head_j, adj_comm, ←mem_edge_set, ←o.consistent e],
        exact e.property },
      { rw [H_tail_i, H_tail_j] at H_ij, tauto } } }
end

variables [fintype α]

/-- `(xᵀ ⬝ oriented_inc_matrix) e = x o.head e - x o.tail e`. -/
lemma vec_mul_oriented_inc_matrix {o : orientation G} (x : α → R) (e : G.edge_set) :
  vec_mul x (G.oriented_inc_matrix R o) e = x (o.head e) - x (o.tail e) :=
begin
  simp only [vec_mul, dot_product, oriented_inc_matrix, mul_ite, mul_one, mul_neg, mul_zero],
  rw [sum_ite, sum_ite, sum_filter, sum_ite_eq', sum_const_zero, add_zero, filter_filter],
  simp only [mem_univ, if_true],
  have key : filter (λ (a : α), ¬a = o.head e ∧ a = o.tail e) univ = {o.tail e},
  { ext,
    simp only [mem_filter, mem_singleton, true_and, and_iff_right_iff_imp, mem_univ],
    rintro rfl,
    exact G.head_ne_tail.symm },
  rw [key, sum_singleton, sub_eq_add_neg],
end

end oriented_incidence
end simple_graph
