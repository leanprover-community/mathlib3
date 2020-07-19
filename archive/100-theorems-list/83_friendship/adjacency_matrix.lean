/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author:  Aaron Anderson, Jalex Stark.
-/
import linear_algebra.matrix
import .sym_matrix
import .simple_graph

open_locale classical big_operators
open finset matrix simple_graph
noncomputable theory

universes u v
variables {V : Type u} [fintype V] (G : simple_graph V)
variables (R : Type v) [semiring R]

-- instance quux : has_scalar ℕ R := by apply_instance
-- I am having a hard time figuring out where in the library the above instance is defined
@[simp]
lemma nat.smul_one (d : ℕ) : d • (1 : R) = (d : R) :=
begin
  induction d with k hk, { simp },
  rw nat.succ_eq_add_one, push_cast,
  rw ← hk, simp [add_smul],
end

@[simp]
lemma int.smul_one (d : ℤ) (R : Type*) [ring R] : d • (1 : R) = (d : R) :=
by apply gsmul_one

section adjacency_matrix

def adjacency_matrix : matrix V V R :=
λ v w : V, if G.E v w then 1 else 0

variable {R}

-- bad name
@[simp] lemma adjacency_matrix_el_idem (i j : V) :
 (adjacency_matrix G R i j) * (adjacency_matrix G R i j) = adjacency_matrix G R i j :=
by { unfold adjacency_matrix, split_ifs; simp [h] }

theorem adjacency_matrix_sym :
 sym_matrix (adjacency_matrix G R) :=
by { ext, unfold adjacency_matrix, rw edge_symm, simp }

@[simp]
lemma adjacency_matrix_apply (v w : V) :
  adjacency_matrix G R v w = ite (G.E v w) 1 0 := rfl

@[simp]
lemma adjacency_matrix_dot_product (v : V) (vec : V → R) :
  dot_product (adjacency_matrix G R v) vec = ∑ u in neighbors G v, vec u :=
by simp [dot_product, neighbors, sum_filter]

@[simp]
lemma dot_product_adjacency_matrix (v : V) (vec : V → R) :
  dot_product vec (adjacency_matrix G R v) = ∑ u in neighbors G v, vec u :=
by simp [dot_product, neighbors, sum_filter]

@[simp]
lemma adjacency_matrix_mul_apply (M : matrix V V R) (v w : V) :
(adjacency_matrix G R * M) v w = (neighbors G v).sum M w :=
by rw [mul_eq_mul, mul_val', adjacency_matrix_dot_product G, sum_apply]

@[simp]
lemma mul_adjacency_matrix_apply (M : matrix V V R) (v w : V) :
  (M * adjacency_matrix G R) v w = ∑ u in neighbors G w, M v u :=
by { rw [mul_eq_mul, mul_val', ← dot_product_adjacency_matrix G], simp_rw sym_matrix_apply (adjacency_matrix_sym G) }

variable (R)
theorem adj_mat_traceless : matrix.trace V R R (adjacency_matrix G R) = 0 := by simp
variable {R}

theorem adj_mat_sq_apply_eq (i : V) :
  ((adjacency_matrix G R) * (adjacency_matrix G R)) i i = degree G i :=
by simp [degree]

variable {G}

lemma adj_mat_mul_vec_ones_apply_of_regular {d : ℕ} (hd : regular_graph G d) (i : V) :
  (adjacency_matrix G R).mul_vec (λ j : V, 1) i = d :=
by rw [← hd i, matrix.mul_vec, adjacency_matrix_dot_product]; simp [degree]

end adjacency_matrix
