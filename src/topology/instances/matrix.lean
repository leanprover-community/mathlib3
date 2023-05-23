/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Eric Wieser
-/
import topology.algebra.infinite_sum.basic
import topology.algebra.ring.basic
import topology.algebra.star
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.trace

/-!
# Topological properties of matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file is a place to collect topological results about matrices.

## Main definitions:

* `matrix.topological_ring`: square matrices form a topological ring

## Main results

* Continuity:
  * `continuous.matrix_det`: the determinant is continuous over a topological ring.
  * `continuous.matrix_adjugate`: the adjugate is continuous over a topological ring.
* Infinite sums
  * `matrix.transpose_tsum`: transpose commutes with infinite sums
  * `matrix.diagonal_tsum`: diagonal commutes with infinite sums
  * `matrix.block_diagonal_tsum`: block diagonal commutes with infinite sums
  * `matrix.block_diagonal'_tsum`: non-uniform block diagonal commutes with infinite sums
-/

open matrix
open_locale matrix

variables {X α l m n p S R : Type*} {m' n' : l → Type*}

instance [topological_space R] : topological_space (matrix m n R) := Pi.topological_space

instance [topological_space R] [t2_space R] : t2_space (matrix m n R) := Pi.t2_space

/-! ### Lemmas about continuity of operations -/
section continuity
variables [topological_space X] [topological_space R]

instance [has_smul α R] [has_continuous_const_smul α R] :
  has_continuous_const_smul α (matrix m n R) :=
pi.has_continuous_const_smul

instance [topological_space α] [has_smul α R] [has_continuous_smul α R] :
  has_continuous_smul α (matrix m n R) :=
pi.has_continuous_smul

instance [has_add R] [has_continuous_add R] : has_continuous_add (matrix m n R) :=
pi.has_continuous_add

instance [has_neg R] [has_continuous_neg R] : has_continuous_neg (matrix m n R) :=
pi.has_continuous_neg

instance [add_group R] [topological_add_group R] : topological_add_group (matrix m n R) :=
pi.topological_add_group

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
lemma continuous.matrix_map [topological_space S] {A : X → matrix m n S} {f : S → R}
   (hA : continuous A) (hf : continuous f) :
  continuous (λ x, (A x).map f) :=
continuous_matrix $ λ i j, hf.comp $ hA.matrix_elem _ _

@[continuity]
lemma continuous.matrix_transpose {A : X → matrix m n R} (hA : continuous A) :
  continuous (λ x, (A x)ᵀ) :=
continuous_matrix $ λ i j, hA.matrix_elem j i

lemma continuous.matrix_conj_transpose [has_star R] [has_continuous_star R] {A : X → matrix m n R}
  (hA : continuous A) : continuous (λ x, (A x)ᴴ) :=
hA.matrix_transpose.matrix_map continuous_star

instance [has_star R] [has_continuous_star R] : has_continuous_star (matrix m m R) :=
⟨continuous_id.matrix_conj_transpose⟩

@[continuity]
lemma continuous.matrix_col {A : X → n → R} (hA : continuous A) : continuous (λ x, col (A x)) :=
continuous_matrix $ λ i j, (continuous_apply _).comp hA

@[continuity]
lemma continuous.matrix_row {A : X → n → R} (hA : continuous A) : continuous (λ x, row (A x)) :=
continuous_matrix $ λ i j, (continuous_apply _).comp hA

@[continuity]
lemma continuous.matrix_diagonal [has_zero R] [decidable_eq n] {A : X → n → R} (hA : continuous A) :
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
{}

instance [fintype n] [non_unital_non_assoc_ring R] [topological_ring R] :
  topological_ring (matrix n n R) :=
{}

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
lemma continuous.matrix_submatrix
  {A : X → matrix l n R} (hA : continuous A) (e₁ : m → l) (e₂ : p → n) :
  continuous (λ x, (A x).submatrix e₁ e₂) :=
continuous_matrix $ λ i j, hA.matrix_elem _ _

@[continuity]
lemma continuous.matrix_reindex {A : X → matrix l n R}
  (hA : continuous A) (e₁ : l ≃ m) (e₂ : n ≃ p) :
  continuous (λ x, reindex e₁ e₂ (A x)) :=
hA.matrix_submatrix _ _

@[continuity]
lemma continuous.matrix_diag {A : X → matrix n n R} (hA : continuous A) :
  continuous (λ x, matrix.diag (A x)) :=
continuous_pi $ λ _, hA.matrix_elem _ _

-- note this doesn't elaborate well from the above
lemma continuous_matrix_diag : continuous (matrix.diag : matrix n n R → n → R) :=
show continuous (λ x : matrix n n R, matrix.diag x), from continuous_id.matrix_diag

@[continuity]
lemma continuous.matrix_trace [fintype n] [add_comm_monoid R] [has_continuous_add R]
  {A : X → matrix n n R} (hA : continuous A) :
  continuous (λ x, trace (A x)) :=
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

-- lemmas about functions in `data/matrix/block.lean`
section block_matrices

@[continuity]
lemma continuous.matrix_from_blocks
  {A : X → matrix n l R} {B : X → matrix n m R} {C : X → matrix p l R} {D : X → matrix p m R}
  (hA : continuous A) (hB : continuous B) (hC : continuous C) (hD : continuous D) :
  continuous (λ x, matrix.from_blocks (A x) (B x) (C x) (D x)) :=
continuous_matrix $ λ i j,
  by cases i; cases j; refine continuous.matrix_elem _ i j; assumption

@[continuity]
lemma continuous.matrix_block_diagonal [has_zero R] [decidable_eq p] {A : X → p → matrix m n R}
  (hA : continuous A) :
  continuous (λ x, block_diagonal (A x)) :=
continuous_matrix $ λ ⟨i₁, i₂⟩ ⟨j₁, j₂⟩,
  (((continuous_apply i₂).comp hA).matrix_elem i₁ j₁).if_const _ continuous_zero

@[continuity]
lemma continuous.matrix_block_diag {A : X → matrix (m × p) (n × p) R} (hA : continuous A) :
  continuous (λ x, block_diag (A x)) :=
continuous_pi $ λ i, continuous_matrix $ λ j k, hA.matrix_elem _ _

@[continuity]
lemma continuous.matrix_block_diagonal' [has_zero R] [decidable_eq l]
  {A : X → Π i, matrix (m' i) (n' i) R} (hA : continuous A) :
  continuous (λ x, block_diagonal' (A x)) :=
continuous_matrix $ λ ⟨i₁, i₂⟩ ⟨j₁, j₂⟩, begin
  dsimp only [block_diagonal'_apply'],
  split_ifs,
  { subst h,
    exact ((continuous_apply i₁).comp hA).matrix_elem i₂ j₂ },
  { exact continuous_const },
end

@[continuity]
lemma continuous.matrix_block_diag' {A : X → matrix (Σ i, m' i) (Σ i, n' i) R} (hA : continuous A) :
  continuous (λ x, block_diag' (A x)) :=
continuous_pi $ λ i, continuous_matrix $ λ j k, hA.matrix_elem _ _

end block_matrices

end continuity

/-! ### Lemmas about infinite sums -/
section tsum
variables [semiring α] [add_comm_monoid R] [topological_space R] [module α R]

lemma has_sum.matrix_transpose {f : X → matrix m n R} {a : matrix m n R} (hf : has_sum f a) :
  has_sum (λ x, (f x)ᵀ) aᵀ :=
(hf.map (matrix.transpose_add_equiv m n R) continuous_id.matrix_transpose : _)

lemma summable.matrix_transpose {f : X → matrix m n R} (hf : summable f) :
  summable (λ x, (f x)ᵀ) :=
hf.has_sum.matrix_transpose.summable

@[simp] lemma summable_matrix_transpose {f : X → matrix m n R} :
  summable (λ x, (f x)ᵀ) ↔ summable f :=
(summable.map_iff_of_equiv (matrix.transpose_add_equiv m n R)
    (@continuous_id (matrix m n R) _).matrix_transpose (continuous_id.matrix_transpose) : _)

lemma matrix.transpose_tsum [t2_space R] {f : X → matrix m n R} : (∑' x, f x)ᵀ = ∑' x, (f x)ᵀ :=
begin
  by_cases hf : summable f,
  { exact hf.has_sum.matrix_transpose.tsum_eq.symm },
  { have hft := summable_matrix_transpose.not.mpr hf,
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft, transpose_zero] },
end

lemma has_sum.matrix_conj_transpose [star_add_monoid R] [has_continuous_star R]
  {f : X → matrix m n R} {a : matrix m n R} (hf : has_sum f a) :
  has_sum (λ x, (f x)ᴴ) aᴴ :=
(hf.map (matrix.conj_transpose_add_equiv m n R) continuous_id.matrix_conj_transpose : _)

lemma summable.matrix_conj_transpose [star_add_monoid R] [has_continuous_star R]
  {f : X → matrix m n R} (hf : summable f) :
  summable (λ x, (f x)ᴴ) :=
hf.has_sum.matrix_conj_transpose.summable

@[simp] lemma summable_matrix_conj_transpose [star_add_monoid R] [has_continuous_star R]
  {f : X → matrix m n R} :
  summable (λ x, (f x)ᴴ) ↔ summable f :=
(summable.map_iff_of_equiv (matrix.conj_transpose_add_equiv m n R)
  (@continuous_id (matrix m n R) _).matrix_conj_transpose (continuous_id.matrix_conj_transpose) : _)

lemma matrix.conj_transpose_tsum [star_add_monoid R] [has_continuous_star R] [t2_space R]
  {f : X → matrix m n R} : (∑' x, f x)ᴴ = ∑' x, (f x)ᴴ :=
begin
  by_cases hf : summable f,
  { exact hf.has_sum.matrix_conj_transpose.tsum_eq.symm },
  { have hft := summable_matrix_conj_transpose.not.mpr hf,
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft, conj_transpose_zero] },
end

lemma has_sum.matrix_diagonal [decidable_eq n] {f : X → n → R} {a : n → R} (hf : has_sum f a) :
  has_sum (λ x, diagonal (f x)) (diagonal a) :=
(hf.map (diagonal_add_monoid_hom n R) $ continuous.matrix_diagonal $ by exact continuous_id : _)

lemma summable.matrix_diagonal [decidable_eq n] {f : X → n → R} (hf : summable f) :
  summable (λ x, diagonal (f x)) :=
hf.has_sum.matrix_diagonal.summable

@[simp] lemma summable_matrix_diagonal [decidable_eq n] {f : X → n → R} :
  summable (λ x, diagonal (f x)) ↔ summable f :=
(summable.map_iff_of_left_inverse
  (@matrix.diagonal_add_monoid_hom n R _ _) (matrix.diag_add_monoid_hom n R)
  (by exact continuous.matrix_diagonal continuous_id)
  continuous_matrix_diag
  (λ A, diag_diagonal A) : _)

lemma matrix.diagonal_tsum [decidable_eq n] [t2_space R] {f : X → n → R} :
  diagonal (∑' x, f x) = ∑' x, diagonal (f x) :=
begin
  by_cases hf : summable f,
  { exact hf.has_sum.matrix_diagonal.tsum_eq.symm },
  { have hft := summable_matrix_diagonal.not.mpr hf,
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft],
    exact diagonal_zero },
end

lemma has_sum.matrix_diag {f : X → matrix n n R} {a : matrix n n R} (hf : has_sum f a) :
  has_sum (λ x, diag (f x)) (diag a) :=
(hf.map (diag_add_monoid_hom n R) continuous_matrix_diag : _)

lemma summable.matrix_diag {f : X → matrix n n R} (hf : summable f) : summable (λ x, diag (f x)) :=
hf.has_sum.matrix_diag.summable

section block_matrices

lemma has_sum.matrix_block_diagonal [decidable_eq p]
  {f : X → p → matrix m n R} {a : p → matrix m n R} (hf : has_sum f a) :
  has_sum (λ x, block_diagonal (f x)) (block_diagonal a) :=
(hf.map (block_diagonal_add_monoid_hom m n p R) $
  continuous.matrix_block_diagonal $ by exact continuous_id : _)

lemma summable.matrix_block_diagonal [decidable_eq p] {f : X → p → matrix m n R} (hf : summable f) :
  summable (λ x, block_diagonal (f x)) :=
hf.has_sum.matrix_block_diagonal.summable

lemma summable_matrix_block_diagonal [decidable_eq p] {f : X → p → matrix m n R} :
  summable (λ x, block_diagonal (f x)) ↔ summable f :=
(summable.map_iff_of_left_inverse
  (matrix.block_diagonal_add_monoid_hom m n p R) (matrix.block_diag_add_monoid_hom m n p R)
  (by exact continuous.matrix_block_diagonal continuous_id)
  (by exact continuous.matrix_block_diag continuous_id)
  (λ A, block_diag_block_diagonal A) : _)

lemma matrix.block_diagonal_tsum [decidable_eq p] [t2_space R] {f : X → p → matrix m n R} :
  block_diagonal (∑' x, f x) = ∑' x, block_diagonal (f x) :=
begin
  by_cases hf : summable f,
  { exact hf.has_sum.matrix_block_diagonal.tsum_eq.symm },
  { have hft := summable_matrix_block_diagonal.not.mpr hf,
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft],
    exact block_diagonal_zero },
end

lemma has_sum.matrix_block_diag {f : X → matrix (m × p) (n × p) R}
  {a : matrix (m × p) (n × p) R} (hf : has_sum f a) :
  has_sum (λ x, block_diag (f x)) (block_diag a) :=
(hf.map (block_diag_add_monoid_hom m n p R) $ continuous.matrix_block_diag continuous_id : _)

lemma summable.matrix_block_diag {f : X → matrix (m × p) (n × p) R} (hf : summable f) :
  summable (λ x, block_diag (f x)) :=
hf.has_sum.matrix_block_diag.summable

lemma has_sum.matrix_block_diagonal' [decidable_eq l]
  {f : X → Π i, matrix (m' i) (n' i) R} {a : Π i, matrix (m' i) (n' i) R} (hf : has_sum f a) :
  has_sum (λ x, block_diagonal' (f x)) (block_diagonal' a) :=
(hf.map (block_diagonal'_add_monoid_hom m' n' R) $
  continuous.matrix_block_diagonal' $ by exact continuous_id : _)

lemma summable.matrix_block_diagonal' [decidable_eq l]
  {f : X → Π i, matrix (m' i) (n' i) R} (hf : summable f) :
  summable (λ x, block_diagonal' (f x)) :=
hf.has_sum.matrix_block_diagonal'.summable

lemma summable_matrix_block_diagonal' [decidable_eq l] {f : X → Π i, matrix (m' i) (n' i) R} :
  summable (λ x, block_diagonal' (f x)) ↔ summable f :=
(summable.map_iff_of_left_inverse
  (matrix.block_diagonal'_add_monoid_hom m' n' R) (matrix.block_diag'_add_monoid_hom m' n' R)
  (by exact continuous.matrix_block_diagonal' continuous_id)
  (by exact continuous.matrix_block_diag' continuous_id)
  (λ A, block_diag'_block_diagonal' A) : _)

lemma matrix.block_diagonal'_tsum [decidable_eq l] [t2_space R]
  {f : X → Π i, matrix (m' i) (n' i) R} :
  block_diagonal' (∑' x, f x) = ∑' x, block_diagonal' (f x) :=
begin
  by_cases hf : summable f,
  { exact hf.has_sum.matrix_block_diagonal'.tsum_eq.symm },
  { have hft := summable_matrix_block_diagonal'.not.mpr hf,
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft],
    exact block_diagonal'_zero },
end

lemma has_sum.matrix_block_diag' {f : X → matrix (Σ i, m' i) (Σ i, n' i) R}
  {a : matrix (Σ i, m' i) (Σ i, n' i) R} (hf : has_sum f a) :
  has_sum (λ x, block_diag' (f x)) (block_diag' a) :=
(hf.map (block_diag'_add_monoid_hom m' n' R) $ continuous.matrix_block_diag' continuous_id : _)

lemma summable.matrix_block_diag' {f : X → matrix (Σ i, m' i) (Σ i, n' i) R} (hf : summable f) :
  summable (λ x, block_diag' (f x)) :=
hf.has_sum.matrix_block_diag'.summable

end block_matrices

end tsum
