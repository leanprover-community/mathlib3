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

 * `matrix.topological_ring`: square matrices form a topological ring
 * `matrix.continuous_det`: the determinant is continuous over a topological ring.
 * `matrix.continuous_adjugate`: the adjugate is continuous over a topological ring.
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

lemma continuous_map [topological_space S] (f : S → R) (hf : continuous f) :
  continuous (λ A : matrix m n S, A.map f) :=
continuous_matrix $ λ i j, hf.comp (continuous_matrix_elem _ _)

lemma continuous_transpose :
  continuous (transpose : matrix m n R → matrix n m R) :=
continuous_matrix $ λ i j, continuous_matrix_elem _ _

/-! TODO: add a `has_continuous_star` typeclass so we can write
```
lemma continuous_conj_transpose [has_star R] :
  continuous (conj_transpose : matrix m n R → matrix n m R) :=
continuous_matrix $ λ i j, continuous.comp sorry (continuous_matrix_elem _ _)
```
-/

lemma continuous_col : continuous (col : (n → R) → matrix n unit R) :=
continuous_matrix $ λ i j, continuous_apply _

lemma continuous_row : continuous (row : (n → R) → matrix unit n R) :=
continuous_matrix $ λ i j, continuous_apply _

lemma continuous_diag [semiring S] [add_comm_monoid R] [module S R] :
  continuous (matrix.diag n S R) :=
continuous_pi (λ _, continuous_matrix_elem _ _)

lemma continuous_trace [fintype n] [semiring S] [add_comm_monoid R] [has_continuous_add R]
  [module S R] :
  continuous (trace n S R) :=
continuous_finset_sum _ $ λ i hi, continuous_matrix_elem _ _

lemma continuous_diagonal [has_zero R] [decidable_eq n] :
  continuous (diagonal : (n → R) → matrix n n R) :=
continuous_matrix $ λ i j, begin
  obtain rfl | hij := decidable.eq_or_ne i j,
  { simp_rw diagonal_apply_eq,
    exact continuous_apply _ },
  { simp_rw diagonal_apply_ne hij,
    exact continuous_zero },
end

lemma continuous_dot_product [fintype n] [has_mul R] [add_comm_monoid R] [has_continuous_add R]
  [has_continuous_mul R] :
  continuous (λ A : (n → R) × (n → R), dot_product A.1 A.2) :=
continuous_finset_sum _ $ λ i _,
  ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)

/-- Note this refers to `matrix.mul`, for square matrices the usual `continuous_mul` can be used. -/
lemma continuous_mul [fintype n] [has_mul R] [add_comm_monoid R] [has_continuous_add R]
  [has_continuous_mul R] :
  continuous (λ A : matrix m n R × matrix n p R, A.1.mul A.2) :=
continuous_matrix $ λ i j, continuous_finset_sum _ $ λ k _,
  ((continuous_matrix_elem _ _).comp continuous_fst).mul
    ((continuous_matrix_elem _ _).comp continuous_snd)

instance [fintype n] [has_mul R] [add_comm_monoid R] [has_continuous_add R]
  [has_continuous_mul R] : has_continuous_mul (matrix n n R) :=
⟨continuous_mul⟩

instance [has_scalar α R] [has_continuous_const_smul α R] :
  has_continuous_const_smul α (matrix n n R) :=
pi.has_continuous_const_smul

instance [topological_space α] [has_scalar α R] [has_continuous_smul α R] :
  has_continuous_smul α (matrix n n R) :=
pi.has_continuous_smul

instance [fintype n] [decidable_eq n] [semiring R] [topological_ring R] :
  topological_ring (matrix n n R) :=
{ ..pi.has_continuous_add }

lemma continuous_minor (e₁ : m → l) (e₂ : p → n) :
  continuous (λ A : matrix l n R, A.minor e₁ e₂) :=
continuous_matrix $ λ i j, continuous_matrix_elem _ _

lemma continuous_reindex (e₁ : l ≃ m) (e₂ : n ≃ p) :
  continuous (reindex e₁ e₂ : matrix l n R → matrix m p R) :=
continuous_minor _ _

lemma continuous_det [fintype n] [decidable_eq n] [comm_ring R] [topological_ring R] :
  continuous (det : matrix n n R → R) :=
begin
  show continuous (λ A : matrix n n R, A.det),
  simp_rw matrix.det_apply,
  refine continuous_finset_sum _ (λ l _, continuous.const_smul _ _),
  refine continuous_finset_prod _ (λ l _, continuous_matrix_elem _ _),
end

lemma continuous_update_column [decidable_eq n] (i : n) :
  continuous (λ x : matrix m n R × (m → R), x.1.update_column i x.2) :=
continuous_matrix $ λ j k, (continuous_apply k).comp $ continuous.update
  ((continuous_apply _).comp continuous_fst) i ((continuous_apply _).comp continuous_snd)

lemma continuous_update_row [decidable_eq m] (i : m) :
  continuous (λ x : matrix m n R × (n → R), x.1.update_row i x.2) :=
continuous_update i

lemma continuous_cramer [fintype n] [decidable_eq n] [comm_ring R] [topological_ring R] :
  continuous (λ A : matrix n n R × (n → R), A.1.cramer A.2) :=
continuous_pi $ λ i, continuous_det.comp $ continuous_update_column _

lemma continuous_adjugate [fintype n] [decidable_eq n] [comm_ring R] [topological_ring R] :
  continuous (adjugate : matrix n n R → matrix n n R) :=
continuous_matrix $ λ j k, continuous_det.comp $ begin
  show continuous (
    (λ (a : matrix n n R × (n → R)), a.1.update_column k a.2) ∘
    (λ a, (a, pi.single j 1)) ∘
    transpose),
  exact (continuous_update_column k).comp
    (continuous.comp (continuous_id.prod_mk continuous_const) continuous_transpose),
end

/-- When `ring.inverse` is continuous at the determinant (such as in a `normed_ring`, or a
`topological_field`), so is `matrix.has_inv`. -/
lemma continuous_at_inv [fintype n] [decidable_eq n] [comm_ring R] [topological_ring R]
  (A : matrix n n R) (h : continuous_at ring.inverse A.det) :
  continuous_at has_inv.inv A :=
(h.comp continuous_det.continuous_at).smul continuous_adjugate.continuous_at

end matrix
