/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import data.matrix.basic
import linear_algebra.matrix.determinant
import linear_algebra.matrix.adjugate

/-!
# Matrices associated with non-degenerate bilinear forms

## Main definitions

* `matrix.nondegenerate A`: the proposition that when interpreted as a bilinear form, the matrix `A`
  is nondegenerate.

-/

namespace matrix

variables {m R A : Type*} [fintype m] [comm_ring R]

/-- A matrix `M` is nondegenerate if for all `v ≠ 0`, there is a `w ≠ 0` with `w ⬝ M ⬝ v ≠ 0`. -/
def nondegenerate (M : matrix m m R) :=
∀ v, (∀ w, matrix.dot_product v (mul_vec M w) = 0) → v = 0

/-- If `M` is nondegenerate and `w ⬝ M ⬝ v = 0` for all `w`, then `v = 0`. -/
lemma nondegenerate.eq_zero_of_ortho {M : matrix m m R} (hM : nondegenerate M)
  {v : m → R} (hv : ∀ w, matrix.dot_product v (mul_vec M w) = 0) : v = 0 :=
hM v hv

/-- If `M` is nondegenerate and `v ≠ 0`, then there is some `w` such that `w ⬝ M ⬝ v ≠ 0`. -/
lemma nondegenerate.exists_not_ortho_of_ne_zero {M : matrix m m R} (hM : nondegenerate M)
  {v : m → R} (hv : v ≠ 0) : ∃ w, matrix.dot_product v (mul_vec M w) ≠ 0 :=
not_forall.mp (mt hM.eq_zero_of_ortho hv)

variables [comm_ring A] [is_domain A]

/-- If `M` has a nonzero determinant, then `M` as a bilinear form on `n → A` is nondegenerate.

See also `bilin_form.nondegenerate_of_det_ne_zero'` and `bilin_form.nondegenerate_of_det_ne_zero`.
-/
theorem nondegenerate_of_det_ne_zero [decidable_eq m] {M : matrix m m A} (hM : M.det ≠ 0) :
  nondegenerate M :=
begin
  intros v hv,
  ext i,
  specialize hv (M.cramer (pi.single i 1)),
  refine (mul_eq_zero.mp _).resolve_right hM,
  convert hv,
  simp only [mul_vec_cramer M (pi.single i 1), dot_product, pi.smul_apply, smul_eq_mul],
  rw [finset.sum_eq_single i, pi.single_eq_same, mul_one],
  { intros j _ hj, simp [hj] },
  { intros, have := finset.mem_univ i, contradiction }
end

theorem eq_zero_of_vec_mul_eq_zero [decidable_eq m] {M : matrix m m A} (hM : M.det ≠ 0) {v : m → A}
  (hv : M.vec_mul v = 0) : v = 0 :=
(nondegenerate_of_det_ne_zero hM).eq_zero_of_ortho
  (λ w, by rw [dot_product_mul_vec, hv, zero_dot_product])

theorem eq_zero_of_mul_vec_eq_zero [decidable_eq m] {M : matrix m m A} (hM : M.det ≠ 0) {v : m → A}
  (hv : M.mul_vec v = 0) :
  v = 0 :=
eq_zero_of_vec_mul_eq_zero (by rwa det_transpose) ((vec_mul_transpose M v).trans hv)

end matrix
