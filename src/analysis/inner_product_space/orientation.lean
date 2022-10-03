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

* `orientation.fin_orthonormal_basis` is an orthonormal basis, indexed by `fin n`, with the given
orientation.

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

/-- Two orthonormal bases with the same orientation determine the same "determinant" top-dimensional
form on `E`. -/
lemma det_eq_det_of_same_orientation
  (h : e.to_basis.orientation = f.to_basis.orientation) :
  e.to_basis.det = f.to_basis.det :=
begin
  rw e.to_basis.det.eq_smul_basis_det f.to_basis,
  simp [e.det_to_matrix_orthonormal_basis_of_same_orientation f h],
end

section adjust_to_orientation
include ne

/-- `orthonormal_basis.adjust_to_orientation`, applied to an orthonormal basis, preserves the property of
orthonormality. -/
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
variables [fact (finrank ℝ E = n + 1)] (ω : orientation ℝ E (fin n.succ))

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ

/-- The volume form on an oriented real inner product space, a nonvanishing top-dimensional
alternating form uniquely defined by compatibility with the orientation and inner product structure.
-/
def volume_form : alternating_map ℝ E ℝ (fin n.succ) :=
(ω.fin_orthonormal_basis n.succ_pos (fact.out (finrank ℝ E = n + 1))).to_basis.det

/-- The volume form on an oriented real inner product space can be evaluated as the determinant with
respect to any orthonormal basis of the space compatible with the orientation. -/
lemma volume_form_robust (b : orthonormal_basis (fin n.succ) ℝ E)
  (hb : b.to_basis.orientation = ω) :
  ω.volume_form = b.to_basis.det :=
begin
  let e : orthonormal_basis (fin n.succ) ℝ E := ω.fin_orthonormal_basis n.succ_pos (fact.out _),
  apply e.det_eq_det_of_same_orientation b,
  rw hb,
  exact ω.fin_orthonormal_basis_orientation _ _,
end

attribute [irreducible] orientation.volume_form

lemma volume_form_robust' (b : orthonormal_basis (fin n.succ) ℝ E) (v : fin n.succ → E) :
  |ω.volume_form v| = |b.to_basis.det v| :=
by rw [ω.volume_form_robust (b.adjust_to_orientation ω) (b.orientation_adjust_to_orientation ω),
  b.abs_det_adjust_to_orientation]

/-- Let `v` be an indexed family of `n + 1` vectors in an oriented `(n + 1)`-dimensional real inner
product space `E`. The output of the volume form of `E` when evaluated on `v` is bounded in absolute
value by the product of the norms of the vectors `v i`. -/
lemma abs_volume_form_apply_le (v : fin n.succ → E) : |ω.volume_form v| ≤ ∏ i : fin n.succ, ∥v i∥ :=
begin
  have : finrank ℝ E = fintype.card (fin n.succ) := by simpa using fact.out _,
  let b : orthonormal_basis (fin n.succ) ℝ E := gram_schmidt_orthonormal_basis this v,
  have hb : b.to_basis.det v = ∏ i, ⟪b i, v i⟫ := gram_schmidt_orthonormal_basis_det this v,
  rw [ω.volume_form_robust' b, hb, finset.abs_prod],
  apply finset.prod_le_prod,
  { intros i hi,
    positivity },
  intros i hi,
  convert abs_real_inner_le_norm (b i) (v i),
  simp [b.orthonormal.1 i],
end

lemma volume_form_apply_le (v : fin n.succ → E) :
  ω.volume_form v ≤ ∏ i : fin n.succ, ∥v i∥ :=
(le_abs_self _).trans (ω.abs_volume_form_apply_le v)

/-- Let `v` be an indexed family of `n + 1` orthogonal vectors in an oriented `(n + 1)`-dimensional
real inner product space `E`. The output of the volume form of `E` when evaluated on `v` is, up to
sign, the product of the norms of the vectors `v i`. -/
lemma abs_volume_form_apply_of_pairwise_orthogonal
  {v : fin n.succ → E} (hv : pairwise (λ i j, ⟪v i, v j⟫ = 0)) :
  |ω.volume_form v| = ∏ i : fin n.succ, ∥v i∥ :=
begin
  have hdim : finrank ℝ E = fintype.card (fin n.succ) := by simpa using fact.out _,
  let b : orthonormal_basis (fin n.succ) ℝ E := gram_schmidt_orthonormal_basis hdim v,
  have hb : b.to_basis.det v = ∏ i, ⟪b i, v i⟫ := gram_schmidt_orthonormal_basis_det hdim v,
  rw [ω.volume_form_robust' b, hb, finset.abs_prod],
  by_cases h : ∃ i, v i = 0,
  obtain ⟨i, hi⟩ := h,
  { rw [finset.prod_eq_zero (finset.mem_univ i), finset.prod_eq_zero (finset.mem_univ i)];
    simp [hi] },
  push_neg at h,
  congr,
  ext i,
  have hb : b i = ∥v i∥⁻¹ • v i := gram_schmidt_orthonormal_basis_apply_of_orthogonal hdim hv (h i),
  simp only [hb, inner_smul_left, real_inner_self_eq_norm_mul_norm, is_R_or_C.conj_to_real],
  rw abs_of_nonneg,
  { have : ∥v i∥ ≠ 0 := by simpa using h i,
    field_simp },
  { positivity },
end

/-- The output of the volume form of an oriented real inner product space `E` when evaluated on an
orthonormal basis is ±1. -/
lemma abs_volume_form_apply_of_orthonormal (v : orthonormal_basis (fin n.succ) ℝ E) :
  |ω.volume_form v| = 1 :=
by simpa [ω.volume_form_robust' v v] using congr_arg abs v.to_basis.det_self

end volume_form

end orientation
