/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Heather Macbeth
-/
import analysis.inner_product_space.gram_schmidt_ortho
import linear_algebra.orientation

/-!
# Orientations of real inner product spaces.

This file provides definitions and proves lemmas about orientations of real inner product spaces.

## Main definitions

* `orthonormal_basis.adjust_to_orientation` takes an orthonormal basis and an orientation, and
  returns an orthonormal basis with that orientation: either the original orthonormal basis, or one
  constructed by negating a single (arbitrary) basis vector.
* `orientation.fin_orthonormal_basis` is an orthonormal basis, indexed by `fin n`, with the given
  orientation.
* `orientation.volume_form` is a nonvanishing top-dimensional alternating form on an oriented real
  inner product space, uniquely defined by compatibility with the orientation and inner product
  structure.

## Main theorems

* `orientation.volume_form_apply_le` states that the result of applying the volume form to a set of
  `n` vectors, where `n` is the dimension the inner product space, is bounded by the product of the
  lengths of the vectors.
* `orientation.abs_volume_form_apply_of_pairwise_orthogonal` states that the result of applying the
  volume form to a set of `n` orthogonal vectors, where `n` is the dimension the inner product
  space, is equal up to sign to the product of the lengths of the vectors.

-/

noncomputable theory

variables {E : Type*} [inner_product_space ℝ E]

open finite_dimensional
open_locale big_operators real_inner_product_space

namespace orthonormal_basis
variables {ι : Type*} [fintype ι] [decidable_eq ι] [ne : nonempty ι] (e f : orthonormal_basis ι ℝ E)
  (x : orientation ℝ E ι)

/-- The change-of-basis matrix between two orthonormal bases with the same orientation has
determinant 1. -/
lemma det_to_matrix_orthonormal_basis_of_same_orientation
  (h : e.to_basis.orientation = f.to_basis.orientation) :
  e.to_basis.det f = 1 :=
begin
  apply (e.det_to_matrix_orthonormal_basis_real f).resolve_right,
  have : 0 < e.to_basis.det f,
  { rw e.to_basis.orientation_eq_iff_det_pos at h,
    simpa using h },
  linarith,
end

/-- The change-of-basis matrix between two orthonormal bases with the opposite orientations has
determinant -1. -/
lemma det_to_matrix_orthonormal_basis_of_opposite_orientation
  (h : e.to_basis.orientation ≠ f.to_basis.orientation) :
  e.to_basis.det f = -1 :=
begin
  contrapose! h,
  simp [e.to_basis.orientation_eq_iff_det_pos,
    (e.det_to_matrix_orthonormal_basis_real f).resolve_right h],
end

variables {e f}

/-- Two orthonormal bases with the same orientation determine the same "determinant" top-dimensional
form on `E`, and conversely. -/
lemma same_orientation_iff_det_eq_det :
  e.to_basis.det = f.to_basis.det ↔ e.to_basis.orientation = f.to_basis.orientation :=
begin
  split,
  { intros h,
    dsimp [basis.orientation],
    congr' },
  { intros h,
    rw e.to_basis.det.eq_smul_basis_det f.to_basis,
    simp [e.det_to_matrix_orthonormal_basis_of_same_orientation f h], },
end

variables (e f)

/-- Two orthonormal bases with opposite orientations determine opposite "determinant"
top-dimensional forms on `E`. -/
lemma det_eq_neg_det_of_opposite_orientation
  (h : e.to_basis.orientation ≠ f.to_basis.orientation) :
  e.to_basis.det = -f.to_basis.det :=
begin
  rw e.to_basis.det.eq_smul_basis_det f.to_basis,
  simp [e.det_to_matrix_orthonormal_basis_of_opposite_orientation f h],
end

section adjust_to_orientation
include ne

/-- `orthonormal_basis.adjust_to_orientation`, applied to an orthonormal basis, preserves the
property of orthonormality. -/
lemma orthonormal_adjust_to_orientation : orthonormal ℝ (e.to_basis.adjust_to_orientation x) :=
begin
  apply e.orthonormal.orthonormal_of_forall_eq_or_eq_neg,
  simpa using e.to_basis.adjust_to_orientation_apply_eq_or_eq_neg x
end

/-- Given an orthonormal basis and an orientation, return an orthonormal basis giving that
orientation: either the original basis, or one constructed by negating a single (arbitrary) basis
vector. -/
def adjust_to_orientation : orthonormal_basis ι ℝ E :=
(e.to_basis.adjust_to_orientation x).to_orthonormal_basis (e.orthonormal_adjust_to_orientation x)

lemma to_basis_adjust_to_orientation :
  (e.adjust_to_orientation x).to_basis = e.to_basis.adjust_to_orientation x :=
(e.to_basis.adjust_to_orientation x).to_basis_to_orthonormal_basis _

/-- `adjust_to_orientation` gives an orthonormal basis with the required orientation. -/
@[simp] lemma orientation_adjust_to_orientation :
  (e.adjust_to_orientation x).to_basis.orientation = x :=
begin
  rw e.to_basis_adjust_to_orientation,
  exact e.to_basis.orientation_adjust_to_orientation x,
end

/-- Every basis vector from `adjust_to_orientation` is either that from the original basis or its
negation. -/
lemma adjust_to_orientation_apply_eq_or_eq_neg (i : ι) :
  e.adjust_to_orientation x i = e i ∨ e.adjust_to_orientation x i = -(e i) :=
by simpa [← e.to_basis_adjust_to_orientation]
  using e.to_basis.adjust_to_orientation_apply_eq_or_eq_neg x i

lemma det_adjust_to_orientation :
  (e.adjust_to_orientation x).to_basis.det = e.to_basis.det
  ∨ (e.adjust_to_orientation x).to_basis.det = -e.to_basis.det :=
by simpa using e.to_basis.det_adjust_to_orientation x

lemma abs_det_adjust_to_orientation (v : ι → E) :
  |(e.adjust_to_orientation x).to_basis.det v| = |e.to_basis.det v| :=
by simp [to_basis_adjust_to_orientation]

end adjust_to_orientation

end orthonormal_basis

namespace orientation
variables {n : ℕ}

open orthonormal_basis

/-- An orthonormal basis, indexed by `fin n`, with the given orientation. -/
protected def fin_orthonormal_basis (hn : 0 < n) (h : finrank ℝ E = n)
  (x : orientation ℝ E (fin n)) : orthonormal_basis (fin n) ℝ E :=
begin
  haveI := fin.pos_iff_nonempty.1 hn,
  haveI := finite_dimensional_of_finrank (h.symm ▸ hn : 0 < finrank ℝ E),
  exact ((std_orthonormal_basis _ _).reindex $ fin_congr h).adjust_to_orientation x
end

/-- `orientation.fin_orthonormal_basis` gives a basis with the required orientation. -/
@[simp] lemma fin_orthonormal_basis_orientation (hn : 0 < n)
  (h : finrank ℝ E = n) (x : orientation ℝ E (fin n)) :
  (x.fin_orthonormal_basis hn h).to_basis.orientation = x :=
begin
  haveI := fin.pos_iff_nonempty.1 hn,
  haveI := finite_dimensional_of_finrank (h.symm ▸ hn : 0 < finrank ℝ E),
  exact ((std_orthonormal_basis _ _).reindex $ fin_congr h).orientation_adjust_to_orientation x
end

section volume_form
variables [_i : fact (finrank ℝ E = n)] (o : orientation ℝ E (fin n))

include _i o

/-- The volume form on an oriented real inner product space, a nonvanishing top-dimensional
alternating form uniquely defined by compatibility with the orientation and inner product structure.
-/
@[irreducible] def volume_form : alternating_map ℝ E ℝ (fin n) :=
begin
  classical,
  unfreezingI { cases n },
  { let opos : alternating_map ℝ E ℝ (fin 0) := alternating_map.const_of_is_empty ℝ E (1:ℝ),
    exact o.eq_or_eq_neg_of_is_empty.by_cases (λ _, opos) (λ _, -opos) },
  { exact (o.fin_orthonormal_basis n.succ_pos _i.out).to_basis.det }
end

omit _i o

@[simp] lemma volume_form_zero_pos [_i : fact (finrank ℝ E = 0)] :
  orientation.volume_form (positive_orientation : orientation ℝ E (fin 0))
  = alternating_map.const_linear_equiv_of_is_empty 1 :=
by simp [volume_form, or.by_cases, if_pos]

lemma volume_form_zero_neg [_i : fact (finrank ℝ E = 0)] :
  orientation.volume_form (-positive_orientation : orientation ℝ E (fin 0))
  = - alternating_map.const_linear_equiv_of_is_empty 1 :=
begin
  dsimp [volume_form, or.by_cases, positive_orientation],
  apply if_neg,
  rw [ray_eq_iff, same_ray_comm],
  intros h,
  simpa using
    congr_arg alternating_map.const_linear_equiv_of_is_empty.symm (eq_zero_of_same_ray_self_neg h),
end

include _i o

/-- The volume form on an oriented real inner product space can be evaluated as the determinant with
respect to any orthonormal basis of the space compatible with the orientation. -/
lemma volume_form_robust (b : orthonormal_basis (fin n) ℝ E) (hb : b.to_basis.orientation = o) :
  o.volume_form = b.to_basis.det :=
begin
  unfreezingI { cases n },
  { classical,
    have : o = positive_orientation := hb.symm.trans b.to_basis.orientation_is_empty,
    simp [volume_form, or.by_cases, dif_pos this] },
  { dsimp [volume_form],
    rw [same_orientation_iff_det_eq_det, hb],
    exact o.fin_orthonormal_basis_orientation _ _ },
end

/-- The volume form on an oriented real inner product space can be evaluated as the determinant with
respect to any orthonormal basis of the space compatible with the orientation. -/
lemma volume_form_robust_neg (b : orthonormal_basis (fin n) ℝ E)
  (hb : b.to_basis.orientation ≠ o) :
  o.volume_form = - b.to_basis.det :=
begin
  unfreezingI { cases n },
  { classical,
    have : positive_orientation ≠ o := by rwa b.to_basis.orientation_is_empty at hb,
    simp [volume_form, or.by_cases, dif_neg this.symm] },
  let e : orthonormal_basis (fin n.succ) ℝ E := o.fin_orthonormal_basis n.succ_pos (fact.out _),
  dsimp [volume_form],
  apply e.det_eq_neg_det_of_opposite_orientation b,
  convert hb.symm,
  exact o.fin_orthonormal_basis_orientation _ _,
end

@[simp] lemma volume_form_neg_orientation : (-o).volume_form = - o.volume_form :=
begin
  unfreezingI { cases n },
  { refine o.eq_or_eq_neg_of_is_empty.elim _ _; rintros rfl; simp [volume_form_zero_neg] },
  let e : orthonormal_basis (fin n.succ) ℝ E := o.fin_orthonormal_basis n.succ_pos (fact.out _),
  have h₁ : e.to_basis.orientation = o := o.fin_orthonormal_basis_orientation _ _,
  have h₂ : e.to_basis.orientation ≠ -o,
  { symmetry,
    rw [e.to_basis.orientation_ne_iff_eq_neg, h₁] },
  rw [o.volume_form_robust e h₁, (-o).volume_form_robust_neg e h₂],
end

lemma volume_form_robust' (b : orthonormal_basis (fin n) ℝ E) (v : fin n → E) :
  |o.volume_form v| = |b.to_basis.det v| :=
begin
  unfreezingI { cases n },
  { refine o.eq_or_eq_neg_of_is_empty.elim _ _; rintros rfl; simp },
  { rw [o.volume_form_robust (b.adjust_to_orientation o) (b.orientation_adjust_to_orientation o),
      b.abs_det_adjust_to_orientation] },
end

/-- Let `v` be an indexed family of `n` vectors in an oriented `n`-dimensional real inner
product space `E`. The output of the volume form of `E` when evaluated on `v` is bounded in absolute
value by the product of the norms of the vectors `v i`. -/
lemma abs_volume_form_apply_le (v : fin n → E) : |o.volume_form v| ≤ ∏ i : fin n, ‖v i‖ :=
begin
  unfreezingI { cases n },
  { refine o.eq_or_eq_neg_of_is_empty.elim _ _; rintros rfl; simp },
  haveI : finite_dimensional ℝ E := fact_finite_dimensional_of_finrank_eq_succ n,
  have : finrank ℝ E = fintype.card (fin n.succ) := by simpa using _i.out,
  let b : orthonormal_basis (fin n.succ) ℝ E := gram_schmidt_orthonormal_basis this v,
  have hb : b.to_basis.det v = ∏ i, ⟪b i, v i⟫ := gram_schmidt_orthonormal_basis_det this v,
  rw [o.volume_form_robust' b, hb, finset.abs_prod],
  apply finset.prod_le_prod,
  { intros i hi,
    positivity },
  intros i hi,
  convert abs_real_inner_le_norm (b i) (v i),
  simp [b.orthonormal.1 i],
end

lemma volume_form_apply_le (v : fin n → E) : o.volume_form v ≤ ∏ i : fin n, ‖v i‖ :=
(le_abs_self _).trans (o.abs_volume_form_apply_le v)

/-- Let `v` be an indexed family of `n` orthogonal vectors in an oriented `n`-dimensional
real inner product space `E`. The output of the volume form of `E` when evaluated on `v` is, up to
sign, the product of the norms of the vectors `v i`. -/
lemma abs_volume_form_apply_of_pairwise_orthogonal
  {v : fin n → E} (hv : pairwise (λ i j, ⟪v i, v j⟫ = 0)) :
  |o.volume_form v| = ∏ i : fin n, ‖v i‖ :=
begin
  unfreezingI { cases n },
  { refine o.eq_or_eq_neg_of_is_empty.elim _ _; rintros rfl; simp },
  haveI : finite_dimensional ℝ E := fact_finite_dimensional_of_finrank_eq_succ n,
  have hdim : finrank ℝ E = fintype.card (fin n.succ) := by simpa using _i.out,
  let b : orthonormal_basis (fin n.succ) ℝ E := gram_schmidt_orthonormal_basis hdim v,
  have hb : b.to_basis.det v = ∏ i, ⟪b i, v i⟫ := gram_schmidt_orthonormal_basis_det hdim v,
  rw [o.volume_form_robust' b, hb, finset.abs_prod],
  by_cases h : ∃ i, v i = 0,
  obtain ⟨i, hi⟩ := h,
  { rw [finset.prod_eq_zero (finset.mem_univ i), finset.prod_eq_zero (finset.mem_univ i)];
    simp [hi] },
  push_neg at h,
  congr,
  ext i,
  have hb : b i = ‖v i‖⁻¹ • v i := gram_schmidt_orthonormal_basis_apply_of_orthogonal hdim hv (h i),
  simp only [hb, inner_smul_left, real_inner_self_eq_norm_mul_norm, is_R_or_C.conj_to_real],
  rw abs_of_nonneg,
  { have : ‖v i‖ ≠ 0 := by simpa using h i,
    field_simp },
  { positivity },
end

/-- The output of the volume form of an oriented real inner product space `E` when evaluated on an
orthonormal basis is ±1. -/
lemma abs_volume_form_apply_of_orthonormal (v : orthonormal_basis (fin n) ℝ E) :
  |o.volume_form v| = 1 :=
by simpa [o.volume_form_robust' v v] using congr_arg abs v.to_basis.det_self

lemma volume_form_map {F : Type*} [inner_product_space ℝ F] [fact (finrank ℝ F = n)]
  (φ : E ≃ₗᵢ[ℝ] F) (x : fin n → F) :
  (orientation.map (fin n) φ.to_linear_equiv o).volume_form x = o.volume_form (φ.symm ∘ x) :=
begin
  unfreezingI { cases n },
  { refine o.eq_or_eq_neg_of_is_empty.elim _ _; rintros rfl; simp },
  let e : orthonormal_basis (fin n.succ) ℝ E := o.fin_orthonormal_basis n.succ_pos (fact.out _),
  have he : e.to_basis.orientation = o :=
    (o.fin_orthonormal_basis_orientation n.succ_pos (fact.out _)),
  have heφ : (e.map φ).to_basis.orientation = orientation.map (fin n.succ) φ.to_linear_equiv o,
  { rw ← he,
    exact (e.to_basis.orientation_map φ.to_linear_equiv) },
  rw (orientation.map (fin n.succ) φ.to_linear_equiv o).volume_form_robust (e.map φ) heφ,
  rw o.volume_form_robust e he,
  simp,
end

/-- The volume form is invariant under pullback by a positively-oriented isometric automorphism. -/
lemma volume_form_comp_linear_isometry_equiv (φ : E ≃ₗᵢ[ℝ] E)
  (hφ : 0 < (φ.to_linear_equiv : E →ₗ[ℝ] E).det) (x : fin n → E) :
  o.volume_form (φ ∘ x) = o.volume_form x :=
begin
  convert o.volume_form_map φ (φ ∘ x),
  { symmetry,
    rwa ← o.map_eq_iff_det_pos φ.to_linear_equiv at hφ,
    rw [_i.out, fintype.card_fin] },
  { ext,
    simp }
end

end volume_form

end orientation
