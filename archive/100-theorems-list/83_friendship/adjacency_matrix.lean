import linear_algebra.matrix
import .sym_matrix

open_locale classical
open finset matrix
noncomputable theory

lemma symm_iff {α : Type*} {r : α → α → Prop} (h : symmetric r) {a b : α} : r a b ↔ r b a :=
by { split; apply h }

variable {V : Type*}

section graph

variable (V)

structure simple_graph :=
(E : V → V → Prop)
(loopless : irreflexive E)
(undirected : symmetric E)


variables {V} (G : simple_graph V)

@[simp] lemma simple_graph.irrefl {v : V} : ¬ G.E v v := G.loopless v

@[simp] lemma foo_symmetry {v : V} : (λ w : V, G.E w v) = G.E v := by { ext, apply symm_iff G.undirected, }

variable [fintype V]

def neighbors (v : V) : finset V := univ.filter (G.E v)

@[simp] lemma neighbor_iff_adjacent (v w : V) :
 w ∈ neighbors G v ↔ G.E v w := by { unfold neighbors, simp }

def degree (v : V) : ℕ := (neighbors G v).card

def regular_graph (d : ℕ) : Prop :=
 ∀ v : V, degree G v = d

end graph

section adjacency_matrix

variables {V} [fintype V] (R : Type*) [ring R] (G : simple_graph V) -- R can be a semiring if we generalize trace

def adjacency_matrix : matrix V V R :=
 λ v w : V, ite (G.E v w) 1 0

variable {R}

@[simp] lemma adjacency_matrix_el_idem (i j : V) :
 (adjacency_matrix R G i j) * (adjacency_matrix R G i j) = adjacency_matrix R G i j :=
by { unfold adjacency_matrix, by_cases G.E i j; simp [h], }

theorem adjacency_matrix_sym :
 sym_matrix (adjacency_matrix R G) :=
begin
  unfold sym_matrix, ext,
  unfold matrix.transpose, unfold adjacency_matrix,
  rw symm_iff G.undirected,
end

@[simp]
lemma adjacency_matrix_apply {v w : V} :
  adjacency_matrix R G v w = ite (G.E v w) 1 0 := rfl

@[simp]
lemma adjacency_matrix_dot_product {v : V} {vec : V → R} :
  dot_product (adjacency_matrix R G v) vec = (neighbors G v).sum vec :=
begin
  unfold dot_product, unfold neighbors, simp [sum_filter],
end

@[simp]
lemma dot_product_adjacency_matrix {v : V} {vec : V → R} :
  dot_product vec (adjacency_matrix R G v) = (neighbors G v).sum vec :=
begin
  unfold dot_product, unfold neighbors, simp [sum_filter],
end

@[simp]
lemma adjacency_matrix_mul_apply {M : matrix V V R} {v w : V} : (adjacency_matrix R G * M) v w = (neighbors G v).sum M w :=
by { rw [mul_eq_mul, mul_val', adjacency_matrix_dot_product G, sum_apply] }

@[simp]
lemma mul_adjacency_matrix_apply {M : matrix V V R} {v w : V} : (M * adjacency_matrix R G) v w = (neighbors G w).sum (M v) :=
by { rw [mul_eq_mul, mul_val', ← dot_product_adjacency_matrix G], simp_rw sym_matrix_apply (adjacency_matrix_sym G) }

variable (R)
theorem adj_mat_traceless : matrix.trace V R R (adjacency_matrix R G) = 0 := by simp
variable {R}

theorem adj_mat_sq_apply_eq {i : V} :
  ((adjacency_matrix R G) * (adjacency_matrix R G)) i i = degree G i :=
begin
  unfold degree, simp only [filter_congr_decidable, adjacency_matrix_mul_apply, sum_boole, sum_apply, adjacency_matrix_apply],
  refine congr rfl (congr rfl _), ext,
  simp only [mem_filter, neighbor_iff_adjacent], rw symm_iff G.undirected, tauto,
end

variable {G}

lemma adj_mat_mul_vec_ones_apply_of_regular {d : ℕ} (reg : regular_graph G d) (i : V):
  (adjacency_matrix R G).mul_vec (λ j : V, 1) i = d :=
begin
  unfold matrix.mul_vec, rw adjacency_matrix_dot_product, simp only [mul_one, nsmul_eq_mul, sum_const],
  rw ← reg i, refl,
end

end adjacency_matrix
