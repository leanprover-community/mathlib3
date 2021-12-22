/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import ring_theory.trace

/-!
# Discriminant of a family of vectors

Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define the
*discriminant* of `b` as the determinant of the matrix whose `(i j)`-th element is the trace of
`b i * b j`.

## Main definition

* `algebra.discr A b` : the discriminant of `b : ι → B`.

## Main results

* `algebra.discr_zero_of_not_linear_independent` : if `b` is not linear independent, then
  `algebra.discr A b = 0`.
* `algebra.discr_of_matrix_vec_mul` and `discr_of_matrix_mul_vec` : formulas relating
  `algebra.discr A ι b` with `algebra.discr A ((P.map (algebra_map A B)).vec_mul b)` and
  `algebra.discr A ((P.map (algebra_map A B)).mul_vec b)`.
* `algebra.discr_not_zero_of_linear_independent` : over a field, if `b` is linear independent, then
  `algebra.discr K b ≠ 0`.
* `algebra.discr_eq_det_embeddings_matrix_reindex_pow_two` if `L/K` is a field extension and
  `b : ι → L`, then `discr K b` is the square of the determinant of the matrix whose `(i, j)`
  coefficient is `σⱼ (b i)`, where `σⱼ : L →ₐ[K] E` is the embedding in an algebraically closed
  field `E` corresponding to `j : ι` via a bijection `e : ι ≃ (L →ₐ[K] E)`.
* `algebra.discr_of_power_basis_eq_prod` : the discriminant of a power basis.

## Implementation details

Our definition works for any `A`-algebra `B`, but note that if `B` is not free as an `A`-module,
then `trace A B = 0` by definition, so `discr A b = 0` for any `b`.
-/

universes u v w z

open_locale matrix big_operators

open matrix finite_dimensional fintype polynomial finset

namespace algebra

variables (A : Type u) {B : Type v} (C : Type z) {ι : Type w}
variables [comm_ring A] [comm_ring B] [algebra A B] [comm_ring C] [algebra A C]

section discr

/-- Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define
`discr A ι b` as the determinant of `trace_matrix A ι b`. -/
noncomputable
def discr (A : Type u) {B : Type v} [comm_ring A] [comm_ring B] [algebra A B] [fintype ι]
  (b : ι → B) := by { classical, exact (trace_matrix A b).det }

lemma discr_def [decidable_eq ι] [fintype ι] (b : ι → B) :
  discr A b = (trace_matrix A b).det := by convert rfl

variable [fintype ι]

section basic

lemma discr_zero_of_not_linear_independent [is_domain A] {b : ι → B}
  (hli : ¬linear_independent A b) : discr A b = 0 :=
begin
  classical,
  obtain ⟨g, hg, i, hi⟩ := fintype.not_linear_independent_iff.1 hli,
  have : (trace_matrix A b).mul_vec g = 0,
  { ext i,
    have : ∀ j, (trace A B) (b i * b j) * g j = (trace A B) (((g j) • (b j)) * b i),
    { intro j, simp [mul_comm], },
    simp only [mul_vec, dot_product, trace_matrix, pi.zero_apply, trace_form_apply,
      λ j, this j, ← linear_map.map_sum, ← sum_mul, hg, zero_mul, linear_map.map_zero] },
  by_contra h,
  rw discr_def at h,
  simpa [matrix.eq_zero_of_mul_vec_eq_zero h this] using hi,
end

variable {A}

lemma discr_of_matrix_vec_mul [decidable_eq ι] (b : ι → B) (P : matrix ι ι A) :
  discr A ((P.map (algebra_map A B)).vec_mul b) = P.det ^ 2 * discr A b :=
by rw [discr_def, trace_matrix_of_matrix_vec_mul, det_mul, det_mul, det_transpose, mul_comm,
    ← mul_assoc, discr_def, pow_two]


lemma discr_of_matrix_mul_vec [decidable_eq ι] (b : ι → B) (P : matrix ι ι A) :
  discr A ((P.map (algebra_map A B)).mul_vec b) = P.det ^ 2 * discr A b :=
by rw [discr_def, trace_matrix_of_matrix_mul_vec, det_mul, det_mul, det_transpose,
  mul_comm, ← mul_assoc, discr_def, pow_two]

end basic

section field

variables (K : Type u) {L : Type v} (E : Type z) [field K] [field L] [field E]
variables [algebra K L] [algebra K E]
variables [module.finite K L] [is_separable K L] [is_alg_closed E]
variables (b : ι → L) (pb : power_basis K L)

lemma discr_not_zero_of_linear_independent [nonempty ι]
  (hcard : fintype.card ι = finrank K L) (hli : linear_independent K b) : discr K b ≠ 0 :=
begin
  classical,
  have := span_eq_top_of_linear_independent_of_card_eq_finrank hli hcard,
  rw [discr_def, trace_matrix_def],
  simp_rw [← basis.mk_apply hli this],
  rw [← trace_matrix_def, trace_matrix_of_basis, ← bilin_form.nondegenerate_iff_det_ne_zero],
  exact trace_form_nondegenerate _ _
end

lemma discr_eq_det_embeddings_matrix_reindex_pow_two [decidable_eq ι]
  (e : ι ≃ (L →ₐ[K] E)) : algebra_map K E (discr K b) =
  (embeddings_matrix_reindex K E b e).det ^ 2 :=
by rw [discr_def, ring_hom.map_det, ring_hom.map_matrix_apply,
    trace_matrix_eq_embeddings_matrix_reindex_mul_trans, det_mul, det_transpose, pow_two]

lemma discr_power_basis_eq_prod (e : fin pb.dim ≃ (L →ₐ[K] E)) :
  algebra_map K E (discr K pb.basis) =
  ∏ i : fin pb.dim, ∏ j in finset.univ.filter (λ j, i < j), (e j pb.gen- (e i pb.gen)) ^ 2 :=
begin
  rw [discr_eq_det_embeddings_matrix_reindex_pow_two K E pb.basis e,
    embeddings_matrix_reindex_eq_vandermonde, det_transpose, det_vandermonde, ← prod_pow],
  congr, ext i,
  rw [← prod_pow]
end

end field

end discr

end algebra
