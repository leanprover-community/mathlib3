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

open finite_dimensional

section adjust_to_orientation
variables {ι : Type*} [fintype ι] [decidable_eq ι] [nonempty ι] (e : orthonormal_basis ι ℝ E)
  (x : orientation ℝ E ι)

/-- `orthonormal_basis.adjust_to_orientation`, applied to an orthonormal basis, produces an orthonormal
basis. -/
lemma orthonormal_basis.orthonormal_adjust_to_orientation :
  orthonormal ℝ (e.to_basis.adjust_to_orientation x) :=
begin
  apply e.orthonormal.orthonormal_of_forall_eq_or_eq_neg,
  simpa using e.to_basis.adjust_to_orientation_apply_eq_or_eq_neg x
end

/-- Given an orthonormal basis and an orientation, return an orthonormal basis giving that
orientation: either the original basis, or one constructed by negating a single (arbitrary) basis
vector. -/
def orthonormal_basis.adjust_to_orientation : orthonormal_basis ι ℝ E :=
(e.to_basis.adjust_to_orientation x).to_orthonormal_basis (e.orthonormal_adjust_to_orientation x)

lemma orthonormal_basis.to_basis_adjust_to_orientation :
  (e.adjust_to_orientation x).to_basis = e.to_basis.adjust_to_orientation x :=
(e.to_basis.adjust_to_orientation x).to_basis_to_orthonormal_basis _

/-- `adjust_to_orientation` gives an orthonormal basis with the required orientation. -/
@[simp] lemma orthonormal_basis.orientation_adjust_to_orientation :
  (e.adjust_to_orientation x).to_basis.orientation = x :=
begin
  rw e.to_basis_adjust_to_orientation,
  exact e.to_basis.orientation_adjust_to_orientation x,
end

/-- Every basis vector from `adjust_to_orientation` is either that from the original basis or its
negation. -/
lemma orthonormal_basis.adjust_to_orientation_apply_eq_or_eq_neg (i : ι) :
  e.adjust_to_orientation x i = e i ∨ e.adjust_to_orientation x i = -(e i) :=
by simpa [← e.to_basis_adjust_to_orientation]
  using e.to_basis.adjust_to_orientation_apply_eq_or_eq_neg x i

end adjust_to_orientation

/-- An orthonormal basis, indexed by `fin n`, with the given orientation. -/
protected def orientation.fin_orthonormal_basis {n : ℕ} (hn : 0 < n) (h : finrank ℝ E = n)
  (x : orientation ℝ E (fin n)) : orthonormal_basis (fin n) ℝ E :=
begin
  haveI := fin.pos_iff_nonempty.1 hn,
  haveI := finite_dimensional_of_finrank (h.symm ▸ hn : 0 < finrank ℝ E),
  exact (fin_std_orthonormal_basis h).adjust_to_orientation x
end

/-- `orientation.fin_orthonormal_basis` gives a basis with the required orientation. -/
@[simp] lemma orientation.fin_orthonormal_basis_orientation {n : ℕ} (hn : 0 < n)
  (h : finrank ℝ E = n) (x : orientation ℝ E (fin n)) :
  (x.fin_orthonormal_basis hn h).to_basis.orientation = x :=
begin
  haveI := fin.pos_iff_nonempty.1 hn,
  haveI := finite_dimensional_of_finrank (h.symm ▸ hn : 0 < finrank ℝ E),
  exact (fin_std_orthonormal_basis h).orientation_adjust_to_orientation x
end
