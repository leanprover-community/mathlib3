/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import analysis.inner_product_space.pi_L2
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
variables {ι : Type*} [fintype ι] [decidable_eq ι]

open finite_dimensional

/-- `basis.adjust_to_orientation`, applied to an orthonormal basis, produces an orthonormal
basis. -/
lemma orthonormal.orthonormal_adjust_to_orientation [nonempty ι] {e : basis ι ℝ E}
  (h : orthonormal ℝ e) (x : orientation ℝ E ι) : orthonormal ℝ (e.adjust_to_orientation x) :=
h.orthonormal_of_forall_eq_or_eq_neg (e.adjust_to_orientation_apply_eq_or_eq_neg x)

/-- An orthonormal basis, indexed by `fin n`, with the given orientation. -/
protected def orientation.fin_orthonormal_basis {n : ℕ} (hn : 0 < n) (h : finrank ℝ E = n)
  (x : orientation ℝ E (fin n)) : basis (fin n) ℝ E :=
begin
  haveI := fin.pos_iff_nonempty.1 hn,
  haveI := finite_dimensional_of_finrank (h.symm ▸ hn : 0 < finrank ℝ E),
  exact (fin_std_orthonormal_basis h).to_basis.adjust_to_orientation x
end

/-- `orientation.fin_orthonormal_basis` is orthonormal. -/
protected lemma orientation.fin_orthonormal_basis_orthonormal {n : ℕ} (hn : 0 < n)
  (h : finrank ℝ E = n) (x : orientation ℝ E (fin n)) :
  orthonormal ℝ (x.fin_orthonormal_basis hn h) :=
begin
  haveI := fin.pos_iff_nonempty.1 hn,
  haveI := finite_dimensional_of_finrank (h.symm ▸ hn : 0 < finrank ℝ E),
  exact (show orthonormal ℝ (fin_std_orthonormal_basis h).to_basis, -- Note sure how to format this
    by simp only [orthonormal_basis.coe_to_basis, orthonormal_basis.orthonormal]
    ).orthonormal_adjust_to_orientation _
end

/-- `orientation.fin_orthonormal_basis` gives a basis with the required orientation. -/
@[simp] lemma orientation.fin_orthonormal_basis_orientation {n : ℕ} (hn : 0 < n)
  (h : finrank ℝ E = n) (x : orientation ℝ E (fin n)) :
  (x.fin_orthonormal_basis hn h).orientation = x :=
begin
  haveI := fin.pos_iff_nonempty.1 hn,
  exact basis.orientation_adjust_to_orientation _ _
end
