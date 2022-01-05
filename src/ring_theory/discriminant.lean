/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import ring_theory.trace
import ring_theory.norm

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
* `algebra.discr_eq_det_embeddings_matrix_reindex_pow_two` : if `L/K` is a field extension and
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

/-- If `b` is not linear independent, then `algebra.discr A b = 0`. -/
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

/-- Relation between `algebra.discr A ι b` and
`algebra.discr A ((P.map (algebra_map A B)).vec_mul b)`. -/
lemma discr_of_matrix_vec_mul [decidable_eq ι] (b : ι → B) (P : matrix ι ι A) :
  discr A ((P.map (algebra_map A B)).vec_mul b) = P.det ^ 2 * discr A b :=
by rw [discr_def, trace_matrix_of_matrix_vec_mul, det_mul, det_mul, det_transpose, mul_comm,
    ← mul_assoc, discr_def, pow_two]

/-- Relation between `algebra.discr A ι b` and
`algebra.discr A ((P.map (algebra_map A B)).mul_vec b)`. -/
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

/-- Over a field, if `b` is linear independent, then `algebra.discr K b ≠ 0`. -/
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

/-- If `L/K` is a field extension and `b : ι → L`, then `discr K b` is the square of the
determinant of the matrix whose `(i, j)` coefficient is `σⱼ (b i)`, where `σⱼ : L →ₐ[K] E` is the
embedding in an algebraically closed field `E` corresponding to `j : ι` via a bijection
`e : ι ≃ (L →ₐ[K] E)`. -/
lemma discr_eq_det_embeddings_matrix_reindex_pow_two [decidable_eq ι]
  (e : ι ≃ (L →ₐ[K] E)) : algebra_map K E (discr K b) =
  (embeddings_matrix_reindex K E b e).det ^ 2 :=
by rw [discr_def, ring_hom.map_det, ring_hom.map_matrix_apply,
    trace_matrix_eq_embeddings_matrix_reindex_mul_trans, det_mul, det_transpose, pow_two]

/-- The discriminant of a power basis. -/
lemma discr_power_basis_eq_prod (e : fin pb.dim ≃ (L →ₐ[K] E)) :
  algebra_map K E (discr K pb.basis) =
  ∏ i : fin pb.dim, ∏ j in finset.univ.filter (λ j, i < j), (e j pb.gen- (e i pb.gen)) ^ 2 :=
begin
  rw [discr_eq_det_embeddings_matrix_reindex_pow_two K E pb.basis e,
    embeddings_matrix_reindex_eq_vandermonde, det_transpose, det_vandermonde, ← prod_pow],
  congr, ext i,
  rw [← prod_pow]
end

/-- A variation of `of_power_basis_eq_prod`. -/
lemma of_power_basis_eq_prod' (e : fin pb.dim ≃ (L →ₐ[K] E)) :
  algebra_map K E (discr K pb.basis) =
  ∏ i : fin pb.dim, ∏ j in finset.univ.filter (λ j, i < j),
  -((e j pb.gen- (e i pb.gen)) * (e i pb.gen- (e j pb.gen))) :=
begin
  rw [discr_power_basis_eq_prod _ _ _ e],
  congr, ext i, congr, ext j,
  ring
end

local notation `n` := finrank K L

/-- A variation of `of_power_basis_eq_prod`. -/
lemma of_power_basis_eq_prod'' (e : fin pb.dim ≃ (L →ₐ[K] E)) :
  algebra_map K E (discr K pb.basis) =
  (-1) ^ (n * (n - 1) / 2) * ∏ i : fin pb.dim, ∏ j in finset.univ.filter (λ j, i < j),
  ((e j pb.gen- (e i pb.gen)) * (e i pb.gen- (e j pb.gen))) :=
begin
  rw [of_power_basis_eq_prod' _ _ _ e],
  simp_rw [λ i j, neg_eq_neg_one_mul ((e j pb.gen- (e i pb.gen)) * (e i pb.gen- (e j pb.gen))),
    prod_mul_distrib],
  congr,
  simp only [prod_pow_eq_pow_sum, prod_const],
  congr,
  simp_rw [fin.card_filter_lt],
  apply (@nat.cast_inj ℚ _ _ _ _ _).1,
  rw [nat.cast_sum],
  have : ∀ (x : fin pb.dim), (↑x + 1) ≤ pb.dim := by simp [nat.succ_le_iff, fin.is_lt],
  simp_rw [nat.sub_sub],
  simp only [nat.cast_sub, this, finset.card_fin, nsmul_eq_mul, sum_const, sum_sub_distrib,
    nat.cast_add, nat.cast_one, sum_add_distrib, mul_one],
  rw [← nat.cast_sum, ← @finset.sum_range ℕ _ pb.dim (λ i, i), sum_range_id ],
  have hn : n = pb.dim,
  { rw [← alg_hom.card K L E, ← fintype.card_fin pb.dim],
    exact card_congr (equiv.symm e) },
  have h₂ : 2 ∣ (pb.dim * (pb.dim - 1)) := even_iff_two_dvd.1 (nat.even_mul_self_pred _),
  have hne : ((2 : ℕ) : ℚ) ≠ 0 := by simp,
  have hle : 1 ≤ pb.dim,
  { rw [← hn, nat.one_le_iff_ne_zero, ← zero_lt_iff, finite_dimensional.finrank_pos_iff],
    apply_instance },
  rw [hn, nat.cast_dvd h₂ hne, nat.cast_mul, nat.cast_sub hle],
  field_simp,
  ring,
end

/-- Formula for the discriminant of a power basis using the norm of the field extension. -/
lemma of_power_basis_eq_norm : discr K pb.basis =
  (-1) ^ (n * (n - 1) / 2) * (norm K (aeval pb.gen (minpoly K pb.gen).derivative)) :=
begin
  let E := algebraic_closure L,
  letI := λ (a b : E), classical.prop_decidable (eq a b),

  have e : fin pb.dim ≃ (L →ₐ[K] E),
  { refine equiv_of_card_eq _,
    rw [fintype.card_fin, alg_hom.card],
    exact (power_basis.finrank pb).symm },
  have hnodup : (map (algebra_map K E) (minpoly K pb.gen)).roots.nodup :=
    nodup_roots (separable.map (is_separable.separable K pb.gen)),
  have hroots : ∀ σ : L →ₐ[K] E, σ pb.gen ∈ (map (algebra_map K E) (minpoly K pb.gen)).roots,
  { intro σ,
    rw [mem_roots, is_root.def, eval_map, ← aeval_def, aeval_alg_hom_apply],
    repeat { simp [minpoly.ne_zero (is_separable.is_integral K pb.gen)] } },

  apply (algebra_map K E).injective,
  rw [ring_hom.map_mul, ring_hom.map_pow, ring_hom.map_neg, ring_hom.map_one,
    of_power_basis_eq_prod'' _ _ _ e],
  congr,
  rw [norm_eq_prod_embeddings, fin.prod_filter_lt_mul_neg_eq_prod_off_diag],
  conv_rhs { congr, skip, funext,
    rw [← aeval_alg_hom_apply, aeval_root_derivative_of_splits (minpoly.monic
      (is_separable.is_integral K pb.gen)) (is_alg_closed.splits_codomain _) (hroots σ),
      ← finset.prod_mk _ (multiset.nodup_erase_of_nodup _ hnodup)] },
  rw [prod_sigma', prod_sigma'],
  refine prod_bij (λ i hi, ⟨e i.2, e i.1 pb.gen⟩) (λ i hi, _) (λ i hi, by simp at hi)
    (λ i j hi hj hij, _) (λ σ hσ, _),
  { simp only [true_and, mem_mk, mem_univ, mem_sigma],
    rw [multiset.mem_erase_of_ne (λ h, _)],
    { exact hroots _ },
    { simp only [true_and, mem_filter, mem_univ, ne.def, mem_sigma] at hi,
      refine hi (equiv.injective e (equiv.injective (power_basis.lift_equiv pb) _)),
      rw [← power_basis.lift_equiv_apply_coe, ← power_basis.lift_equiv_apply_coe] at h,
      exact subtype.eq h } },
  { simp only [equiv.apply_eq_iff_eq, heq_iff_eq] at hij,
    have h := hij.2,
    rw [← power_basis.lift_equiv_apply_coe, ← power_basis.lift_equiv_apply_coe] at h,
    refine sigma.eq (equiv.injective e (equiv.injective _ (subtype.eq h))) (by simp [hij.1]) },
  { simp only [true_and, mem_mk, mem_univ, mem_sigma] at hσ,
    simp only [sigma.exists, true_and, exists_prop, mem_filter, mem_univ, ne.def, mem_sigma],
    refine ⟨e.symm (power_basis.lift pb σ.2 _), e.symm σ.1, ⟨λ h, _, sigma.eq _ _⟩⟩,
    { rw [aeval_def, eval₂_eq_eval_map, ← is_root.def, ← mem_roots],
      { exact multiset.erase_subset _ _ hσ },
      { simp [minpoly.ne_zero (is_separable.is_integral K pb.gen)] } },
    { replace h := alg_hom.congr_fun (equiv.injective _ h) pb.gen,
      rw [power_basis.lift_gen] at h,
      rw [← h] at hσ,
      refine multiset.mem_erase_of_nodup hnodup hσ, },
    all_goals { simp } }
end

end field

end discr

end algebra
