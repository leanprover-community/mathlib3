/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author:  Aaron Anderson, Jalex Stark.
-/
import linear_algebra.matrix
import data.rel
import combinatorics.simple_graph

open_locale big_operators matrix
open finset matrix simple_graph

universes u v

namespace simple_graph

variables {β : Type*} [simple_graphs β] (G : β)
variables [fintype (V G)] [decidable_rel (adj G)]
variables (R : Type v) [semiring R]

/-- The matrix $A$ such that $A i j = 1$ if $i$ and $j$ are adjacent, and otherwise $A i j = 0$-/
def adjacency_matrix : matrix (V G) (V G) R
| i j := ite (i ~g j) 1 0

variable {R}

theorem transpose_adjacency_matrix : (adjacency_matrix G R)ᵀ = (adjacency_matrix G R) :=
by { ext, simp [adjacency_matrix, adj_symm], }

@[simp]
lemma adjacency_matrix_apply (v w : (V G)) : adjacency_matrix G R v w = ite (v ~g w) 1 0 := rfl

@[simp]
lemma adjacency_matrix_dot_product (v : (V G)) (vec : (V G) → R) :
  dot_product (adjacency_matrix G R v) vec = ∑ u in neighbor_finset v, vec u :=
by simp [neighbor_finset_eq_filter, dot_product, sum_filter]

@[simp]
lemma dot_product_adjacency_matrix (v : (V G)) (vec : (V G) → R) :
  dot_product vec (adjacency_matrix G R v) = ∑ u in neighbor_finset v, vec u :=
by simp [neighbor_finset_eq_filter, dot_product, sum_filter, sum_apply]

@[simp]
lemma adjacency_matrix_mul_apply (M : matrix (V G) (V G) R) (v w : (V G)) :
  (adjacency_matrix G R ⬝ M) v w = ∑ u in neighbor_finset v, M u w :=
by simp [mul_apply, neighbor_finset_eq_filter, sum_filter]

@[simp]
lemma mul_adjacency_matrix_apply (M : matrix (V G) (V G) R) (v w : (V G)) :
  (M ⬝ adjacency_matrix G R) v w = ∑ u in neighbor_finset w, M v u :=
by simp [mul_apply, neighbor_finset_eq_filter, sum_filter, adj_symm]

variable (R)
theorem adj_mat_traceless : matrix.trace (V G) R R (adjacency_matrix G R) = 0 := by simp
variable {R}

theorem adj_mat_sq_apply_eq (i : (V G)) :
  ((adjacency_matrix G R) ⬝ (adjacency_matrix G R)) i i = degree i :=
by simp [degree]

variable {G}

lemma adj_mat_mul_const_vec_of_regular {d : ℕ} {r : R} (hd : is_regular_of_degree G d) :
  (adjacency_matrix G R).mul_vec (λ j : (V G), r) = λ _, d * r :=
by { ext, rw [← hd x, matrix.mul_vec, adjacency_matrix_dot_product]; simp [degree] }

end simple_graph
