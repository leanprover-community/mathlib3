/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.simple_graph.degree_sum
import linear_algebra.matrix.symmetric
import linear_algebra.matrix.trace

/-!
# Laplacian of a simple graph

This file defines the Laplacian of a graph `G`. This is the matrix `M` indexed by vertices in both
directions such that `M a a` is the degree of `a`, `M a b` is `-1` if `a` and `b` are connected by
an edge and is `0` otherwise.

## Main declarations

* `simple_graph.laplacian`: The Laplacian of a simple graph.

## TODO

* `M Mᵀ = G.laplacian R` for `M` the oriented adjacency matrix of any orientation of `G`.
-/

open finset
open_locale big_operators matrix

namespace simple_graph
variables {α : Type*} [decidable_eq α] [fintype α] (R : Type*) [ring R] (G : simple_graph α)
  [decidable_rel G.adj]

/-- The Laplacian of a graph is the matrix on its vertices that's `G.degree a` in `(a, a)`, `-1`
in `(a, b)` if `a` and `b` are connected by an edge and `0` elsewhere. -/
def laplacian : matrix α α R :=
λ a b, if a = b
         then G.degree a
       else if G.adj a b
         then -1
         else 0

@[simp] lemma laplacian_apply (a b : α) :
  G.laplacian R a b = if a = b then G.degree a else if G.adj a b then -1 else 0 := rfl

lemma laplacian_comm (a b : α) : G.laplacian R a b = G.laplacian R b a :=
by { simp only [laplacian_apply, adj_comm, eq_comm], split_ifs, { subst h }, { refl }, refl }

@[simp] lemma transpose_laplacian : (G.laplacian R)ᵀ = G.laplacian R :=
by { ext, exact laplacian_comm _ _ _ _ }

@[simp] lemma is_symm_laplacian : (G.laplacian R).is_symm := transpose_laplacian _ _

@[simp] lemma trace_laplacian : (G.laplacian R).trace = 2 * G.edge_finset.card :=
by simp only [matrix.trace, matrix.diag, laplacian_apply, if_pos rfl, ←nat.cast_sum,
  sum_degrees_eq_twice_card_edges, nat.cast_mul, nat.cast_two]

lemma sum_laplacian_row (a : α) : ∑ b, G.laplacian R a b = 0 :=
begin
  simp_rw [laplacian_apply, sum_ite, filter_eq, if_pos (mem_univ a), sum_singleton, sum_const_zero,
    sum_const, smul_neg, nat.smul_one_eq_coe, add_zero, filter_filter, degree, ←sub_eq_add_neg,
    sub_eq_zero],
  congr',
  ext b,
  simpa using adj.ne,
end

lemma sum_laplacian_column (b : α) : ∑ a, G.laplacian R a b = 0 :=
by simp_rw [laplacian_comm, sum_laplacian_row]

end simple_graph
