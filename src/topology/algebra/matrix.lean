/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Eric Wieser
-/
import linear_algebra.determinant
import topology.algebra.ring

/-!
# Topological properties of matrices

This file is a place to collect topological results about matrices.

## Main definitions:

 * `continuous_det`: the determinant is continuous over a topological ring.
-/

open matrix

variables {α l m n p S R : Type*} [topological_space R]

instance : topological_space (matrix m n R) := Pi.topological_space

/-- To show a function into matrices is continuous it suffices to show the coefficients of the
resulting matrix are continuous-/
lemma continuous_matrix [topological_space α] {f : α → matrix m n R}
  (h : ∀ i j, continuous (λ a, f a i j)) : continuous f :=
continuous_pi $ λ _, continuous_pi $ λ j, h _ _

lemma continuous_matrix_elem (i : m) (j : n) : continuous (λ A : matrix m n R, A i j) :=
continuous_apply_apply i j

namespace matrix

lemma continuous_diagonal [has_zero R] [decidable_eq n] :
  continuous (diagonal : (n → R) → matrix n n R) :=
continuous_matrix $ λ i j, begin
  obtain rfl | hij := decidable.eq_or_ne i j,
  { simp_rw diagonal_apply_eq,
    exact continuous_apply _ },
  { simp_rw diagonal_apply_ne hij,
    exact continuous_zero },
end

lemma continuous_row : continuous (row : (n → R) → matrix unit n R) :=
continuous_matrix $ λ i j, continuous_apply _

lemma continuous_col : continuous (col : (n → R) → matrix n unit R) :=
continuous_matrix $ λ i j, continuous_apply _

lemma continuous_diag [semiring S] [add_comm_monoid R] [module S R] :
  continuous (matrix.diag n S R) :=
continuous_pi (λ _, continuous_matrix_elem _ _)

lemma continuous_trace [fintype n] [semiring S] [add_comm_monoid R] [has_continuous_add R]
  [module S R] :
  continuous (trace n S R) :=
continuous_finset_sum _ $ λ i hi, continuous_matrix_elem _ _

lemma continuous_dot_product [fintype n] [has_mul R] [add_comm_monoid R] [has_continuous_add R]
  [has_continuous_mul R] :
  continuous (λ A : (n → R) × (n → R), dot_product A.1 A.2) :=
continuous_finset_sum _ $ λ i _,
  ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)

lemma continuous_mul [fintype n] [has_mul R] [add_comm_monoid R] [has_continuous_add R]
  [has_continuous_mul R] :
  continuous (λ A : matrix m n R × matrix n p R, A.1.mul A.2) :=
continuous_matrix $ λ i j, continuous_finset_sum _ $ λ k _,
  ((continuous_matrix_elem _ _).comp continuous_fst).mul
    ((continuous_matrix_elem _ _).comp continuous_snd)

lemma continuous_minor (e₁ : m → l) (e₂ : p → n) :
  continuous (λ A : matrix l n R, A.minor e₁ e₂) :=
continuous_matrix $ λ i j, continuous_matrix_elem _ _

lemma continuous_reindex (e₁ : l ≃ m) (e₂ : n ≃ p) :
  continuous (reindex e₁ e₂ : matrix l n R → matrix m p R) :=
continuous_minor _ _

end matrix

variables [fintype n] [decidable_eq n] [comm_ring R] [topological_ring R]

lemma continuous_det : continuous (det : matrix n n R → R) :=
begin
  show continuous (λ A : matrix n n R, A.det),
  simp_rw matrix.det_apply,
  refine continuous_finset_sum _ (λ l _, continuous.const_smul _ _),
  refine continuous_finset_prod _ (λ l _, continuous_matrix_elem _ _),
end
