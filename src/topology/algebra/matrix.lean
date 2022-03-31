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
 * `continuous.matrix_det`: the determinant is continuous over a topological ring.
 * `continuous.matrix_adjugate`: the adjugate is continuous over a topological ring.
-/

open matrix
open_locale matrix

variables {X α l m n p S R : Type*} [topological_space X] [topological_space R]

instance : topological_space (matrix m n R) := Pi.topological_space

instance [has_scalar α R] [has_continuous_const_smul α R] :
  has_continuous_const_smul α (matrix n n R) :=
pi.has_continuous_const_smul

instance [topological_space α] [has_scalar α R] [has_continuous_smul α R] :
  has_continuous_smul α (matrix n n R) :=
pi.has_continuous_smul

/-- To show a function into matrices is continuous it suffices to show the coefficients of the
resulting matrix are continuous -/
@[continuity]
lemma continuous_matrix [topological_space α] {f : α → matrix m n R}
  (h : ∀ i j, continuous (λ a, f a i j)) : continuous f :=
continuous_pi $ λ _, continuous_pi $ λ j, h _ _

lemma continuous.matrix_elem {A : X → matrix m n R} (hA : continuous A) (i : m) (j : n) :
  continuous (λ x, A x i j) :=
(continuous_apply_apply i j).comp hA

@[continuity]
lemma continuous.matrix_map [topological_space S] {A : X → matrix n m S} {f : S → R}
   (hA : continuous A) (hf : continuous f) :
  continuous (λ x, (A x).map f) :=
continuous_matrix $ λ i j, hf.comp $ hA.matrix_elem _ _

@[continuity]
lemma continuous.matrix_transpose {A : X → matrix n m R} (hA : continuous A) :
  continuous (λ x, (A x)ᵀ) :=
continuous_matrix $ λ i j, hA.matrix_elem j i

/-! TODO: add a `has_continuous_star` typeclass so we can write
```
lemma continuous.matrix.conj_transpose [has_star R] {A : X → matrix n m R} (hA : continuous A) :
  continuous (λ x, (A x)ᴴ) :=
hA.matrix_transpose.matrix_map continuous_star
```
-/

@[continuity]
lemma continuous.matrix_col {A : X → n → R} (hA : continuous A) : continuous (λ x, col (A x)) :=
continuous_matrix $ λ i j, (continuous_apply _).comp hA

@[continuity]
lemma continuous.matrix_row {A : X → n → R} (hA : continuous A) : continuous (λ x, row (A x)) :=
continuous_matrix $ λ i j, (continuous_apply _).comp hA

@[continuity]
lemma continuous_matrix.diagonal [has_zero R] [decidable_eq n] {A : X → n → R} (hA : continuous A) :
  continuous (λ x, diagonal (A x)) :=
continuous_matrix $ λ i j, ((continuous_apply i).comp hA).if_const _ continuous_zero

@[continuity]
lemma continuous.matrix_dot_product [fintype n] [has_mul R] [add_comm_monoid R]
  [has_continuous_add R] [has_continuous_mul R]
  {A : X → n → R} {B : X → n → R} (hA : continuous A) (hB : continuous B) :
  continuous (λ x, dot_product (A x) (B x)) :=
continuous_finset_sum _ $ λ i _, ((continuous_apply i).comp hA).mul ((continuous_apply i).comp hB)

/-- For square matrices the usual `continuous_mul` can be used. -/
@[continuity]
lemma continuous.matrix_mul [fintype n] [has_mul R] [add_comm_monoid R] [has_continuous_add R]
  [has_continuous_mul R]
  {A : X → matrix m n R} {B : X → matrix n p R} (hA : continuous A) (hB : continuous B) :
  continuous (λ x, (A x).mul (B x)) :=
continuous_matrix $ λ i j, continuous_finset_sum _ $ λ k _,
  (hA.matrix_elem _ _).mul (hB.matrix_elem _ _)

instance [fintype n] [has_mul R] [add_comm_monoid R] [has_continuous_add R]
  [has_continuous_mul R] : has_continuous_mul (matrix n n R) :=
⟨continuous_fst.matrix_mul continuous_snd⟩

instance [fintype n] [non_unital_non_assoc_semiring R] [topological_semiring R] :
  topological_semiring (matrix n n R) :=
{ ..pi.has_continuous_add }

instance [fintype n] [non_unital_non_assoc_ring R] [topological_ring R] :
  topological_ring (matrix n n R) :=
{ ..pi.has_continuous_neg, ..pi.has_continuous_add }

@[continuity]
lemma continuous.matrix_vec_mul_vec [has_mul R] [has_continuous_mul R]
  {A : X → m → R} {B : X → n → R} (hA : continuous A) (hB : continuous B) :
  continuous (λ x, vec_mul_vec (A x) (B x)) :=
continuous_matrix $ λ i j, ((continuous_apply _).comp hA).mul ((continuous_apply _).comp hB)

@[continuity]
lemma continuous.matrix_mul_vec [non_unital_non_assoc_semiring R] [has_continuous_add R]
  [has_continuous_mul R] [fintype n]
  {A : X → matrix m n R} {B : X → n → R} (hA : continuous A) (hB : continuous B) :
  continuous (λ x, (A x).mul_vec (B x)) :=
continuous_pi $ λ i, ((continuous_apply i).comp hA).matrix_dot_product hB

@[continuity]
lemma continuous.matrix_vec_mul [non_unital_non_assoc_semiring R] [has_continuous_add R]
  [has_continuous_mul R] [fintype m]
  {A : X → m → R} {B : X → matrix m n R} (hA : continuous A) (hB : continuous B) :
  continuous (λ x, vec_mul (A x) (B x)) :=
continuous_pi $ λ i, hA.matrix_dot_product $ continuous_pi $ λ j, hB.matrix_elem _ _

@[continuity]
lemma continuous.matrix_minor {A : X → matrix l n R} (hA : continuous A) (e₁ : m → l) (e₂ : p → n) :
  continuous (λ x, (A x).minor e₁ e₂) :=
continuous_matrix $ λ i j, hA.matrix_elem _ _

@[continuity]
lemma continuous.matrix_reindex {A : X → matrix l n R}
  (hA : continuous A) (e₁ : l ≃ m) (e₂ : n ≃ p) :
  continuous (λ x, reindex e₁ e₂ (A x)) :=
hA.matrix_minor _ _

@[continuity]
lemma continuous.matrix_diag [semiring S] [add_comm_monoid R] [module S R]
  {A : X → matrix n n R} (hA : continuous A) :
  continuous (λ x, matrix.diag n S R (A x)) :=
continuous_pi $ λ _, hA.matrix_elem _ _

@[continuity]
lemma continuous.matrix_trace [fintype n] [semiring S] [add_comm_monoid R] [has_continuous_add R]
  [module S R] {A : X → matrix n n R} (hA : continuous A) :
  continuous (λ x, trace n S R (A x)) :=
continuous_finset_sum _ $ λ i hi, hA.matrix_elem _ _

@[continuity]
lemma continuous.matrix_det [fintype n] [decidable_eq n] [comm_ring R] [topological_ring R]
  {A : X → matrix n n R} (hA : continuous A) :
  continuous (λ x, (A x).det) :=
begin
  simp_rw matrix.det_apply,
  refine continuous_finset_sum _ (λ l _, continuous.const_smul _ _),
  refine continuous_finset_prod _ (λ l _, hA.matrix_elem _ _),
end

@[continuity]
lemma continuous.matrix_update_column [decidable_eq n] (i : n)
  {A : X → matrix m n R} {B : X → m → R} (hA : continuous A) (hB : continuous B) :
  continuous (λ x, (A x).update_column i (B x)) :=
continuous_matrix $ λ j k, (continuous_apply k).comp $
  ((continuous_apply _).comp hA).update i ((continuous_apply _).comp hB)

@[continuity]
lemma continuous.matrix_update_row [decidable_eq m] (i : m)
  {A : X → matrix m n R} {B : X → n → R} (hA : continuous A) (hB : continuous B) :
  continuous (λ x, (A x).update_row i (B x)) :=
hA.update i hB

@[continuity]
lemma continuous.matrix_cramer [fintype n] [decidable_eq n] [comm_ring R] [topological_ring R]
  {A : X → matrix n n R} {B : X → n → R} (hA : continuous A) (hB : continuous B) :
  continuous (λ x, (A x).cramer (B x)) :=
continuous_pi $ λ i, (hA.matrix_update_column _ hB).matrix_det

@[continuity]
lemma continuous.matrix_adjugate [fintype n] [decidable_eq n] [comm_ring R] [topological_ring R]
  {A : X → matrix n n R} (hA : continuous A) :
  continuous (λ x, (A x).adjugate) :=
continuous_matrix $ λ j k, (hA.matrix_transpose.matrix_update_column k continuous_const).matrix_det

/-- When `ring.inverse` is continuous at the determinant (such as in a `normed_ring`, or a
`topological_field`), so is `matrix.has_inv`. -/
lemma continuous_at_matrix_inv [fintype n] [decidable_eq n] [comm_ring R] [topological_ring R]
  (A : matrix n n R) (h : continuous_at ring.inverse A.det) :
  continuous_at has_inv.inv A :=
(h.comp continuous_id.matrix_det.continuous_at).smul continuous_id.matrix_adjugate.continuous_at
