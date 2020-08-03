/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author:  Aaron Anderson, Jalex Stark.
-/
import linear_algebra.matrix
import data.rel
import combinatorics.simple_graph

open_locale classical big_operators matrix
open finset matrix simple_graph
noncomputable theory

universes u v
variables {α : Type u} [fintype α] [decidable_eq α]
variables (R : Type v) [semiring R]

namespace simple_graph

variables (G : simple_graph α) (R)

/-- The matrix $A$ such that $A i j = 1$ if $i$ and $j$ are adjacent, and otherwise $A i j = 0$-/
def adjacency_matrix : matrix α α R
| i j := ite (G.adj i j) 1 0

variable {R}

theorem transpose_adjacency_matrix : (G.adjacency_matrix R)ᵀ = (G.adjacency_matrix R) :=
by { ext, simp [adjacency_matrix, edge_symm], }

@[simp]
lemma adjacency_matrix_apply (v w : α) : G.adjacency_matrix R v w = ite (G.adj v w) 1 0 := rfl

@[simp]
lemma adjacency_matrix_dot_product (v : α) (vec : α → R) :
  dot_product (G.adjacency_matrix R v) vec = ∑ u in G.neighbor_finset v, vec u :=
by simp [neighbor_finset_eq_filter, dot_product, sum_filter]

@[simp]
lemma dot_product_adjacency_matrix (v : α) (vec : α → R) :
  dot_product vec (G.adjacency_matrix R v) = ∑ u in G.neighbor_finset v, vec u :=
by simp [neighbor_finset_eq_filter, dot_product, sum_filter, sum_apply]

@[simp]
lemma adjacency_matrix_mul_apply (M : matrix α α R) (v w : α) :
  (G.adjacency_matrix R ⬝ M) v w = ∑ u in G.neighbor_finset v, M u w :=
by simp [mul_val, neighbor_finset_eq_filter, sum_filter]

@[simp]
lemma mul_adjacency_matrix_apply (M : matrix α α R) (v w : α) :
  (M ⬝ G.adjacency_matrix R) v w = ∑ u in G.neighbor_finset w, M v u :=
by simp [mul_val, neighbor_finset_eq_filter, sum_filter, edge_symm]

variable (R)
theorem adj_mat_traceless : matrix.trace α R R (G.adjacency_matrix R) = 0 := by simp
variable {R}

theorem adj_mat_sq_apply_eq (i : α) :
  ((G.adjacency_matrix R) ⬝ (G.adjacency_matrix R)) i i = degree G i :=
by simp [degree]

variable {G}

lemma adj_mat_mul_const_vec_of_regular {d : ℕ} {r : R} (hd : G.is_regular_of_degree d) :
  (G.adjacency_matrix R).mul_vec (λ j : α, r) = λ _, d * r :=
by { ext, rw [← hd x, matrix.mul_vec, adjacency_matrix_dot_product]; simp [degree] }

end simple_graph
