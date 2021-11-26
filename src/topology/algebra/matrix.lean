/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import linear_algebra.determinant
import topology.algebra.ring

/-!
# Topological properties of matrices

This file is a place to collect topological results about matrices.

## Main definitions:

 * `continuous_det`: the determinant is continuous over a topological ring.
-/

open matrix

variables {ι k : Type*} [topological_space k]

instance : topological_space (matrix ι ι k) := Pi.topological_space

variables [fintype ι] [decidable_eq ι] [comm_ring k] [topological_ring k]

lemma continuous_det : continuous (det : matrix ι ι k → k) :=
begin
  suffices : ∀ (n : ℕ), continuous (det : matrix (fin n) (fin n) k → k),
  { have h : (det : matrix ι ι k → k) = det ∘ reindex (fintype.equiv_fin ι) (fintype.equiv_fin ι),
    { ext, simp, },
    rw h,
    apply (this (fintype.card ι)).comp,
    refine continuous_pi (λ i, continuous_pi (λ j, _)),
    simp only [minor_apply, reindex_apply],
    apply continuous_apply_apply, },
  intros n,
  induction n with n ih,
  { rw coe_det_is_empty,
    exact continuous_const, },
  change continuous (λ (A : matrix (fin n.succ) (fin n.succ) k), A.det),
  simp_rw det_succ_column_zero,
  refine continuous_finset_sum _ (λ l _, _),
  apply continuous.mul,
  { refine continuous_const.mul _,
    apply continuous_apply_apply, },
  { apply ih.comp,
    refine continuous_pi (λ i, continuous_pi (λ j, _)),
    simp only [minor_apply],
    apply continuous_apply_apply, },
end
