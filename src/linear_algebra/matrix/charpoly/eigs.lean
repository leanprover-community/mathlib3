/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import data.polynomial.basic
import field_theory.is_alg_closed.basic
import data.matrix.basic
import linear_algebra.matrix.spectrum
import linear_algebra.eigenspace.basic
import linear_algebra.charpoly.to_matrix
import linear_algebra.matrix.charpoly.minpoly
import linear_algebra.matrix.to_linear_equiv

/-!
# Eigenvalues are characteristic polynomial roots.

In fields we show that:

* `matrix.det_eq_prod_roots_charpoly_of_splits`: the determinant (in the field of the matrix)
  is the product of the roots of the characteristic polynomial if the polynomial splits in the field
  of the matrix.
* `matrix.trace_eq_sum_roots_charpoly_of_splits`: the trace is the sum of the roots of the
  characteristic polynomial if the polynomial splits in the field of the matrix.

In an algebraically closed field we show that:

* `matrix.det_eq_prod_roots_charpoly`: the determinant is the product of the roots of the
  characteristic polynomial.
* `matrix.trace_eq_sum_roots_charpoly`: the trace is the sum of the roots of the
  characteristic polynomial.

Note that over other fields such as `ℝ`, these results can be used by using
`A.map (algebra_map ℝ ℂ)` as the matrix, and then applying `ring_hom.map_det`.

The two lemmas `matrix.det_eq_prod_roots_charpoly` and `matrix.trace_eq_sum_roots_charpoly` are more
commonly stated as trace is the sum of eigenvalues and determinant is the product of eigenvalues.
Mathlib has already defined eigenvalues in `linear_algebra.eigenspace` as the roots of the minimal
polynomial of a linear endomorphism. These do not have correct multiplicity and cannot be used in
the theorems above. Hence we express these theorems in terms of the roots of the characteristic
polynomial directly.

To provide the linkage between the eigenvalues as defined by mathlib in `linear_algebra.eigenspace`
and the roots of the characteristic polynomial we also provide the following lemmas:

* `matrix.root_charpoly_iff_has_eigenvalue`: a root of the characterisitc polynomial is an eigenvalue
  and vice versa.
* `matrix.root_charpoly_iff_root_minpoly`: a root of the characteristic polynomial is a root of the
  minimal polynomial and vice versa. Note that the minimaly polynomial is that of the endomorphism.
  To get the linear map of the matrix use `minpoly.minpoly_alg_equiv`.

## TODO

The proofs of `det_eq_prod_roots_charpoly_of_splits` and
`trace_eq_sum_roots_charpoly_of_splits` closely resemble
`norm_gen_eq_prod_roots` and `trace_gen_eq_sum_roots` respectively, but the
dependencies are not general enough to unify them. We should refactor
`polynomial.prod_roots_eq_coeff_zero_of_monic_of_split` and
`polynomial.sum_roots_eq_next_coeff_of_monic_of_split` to assume splitting over an arbitrary map.

In mathlib hermitian matrices have special eigenvalue definitionsin `linear_algebra.matrix.spectrum`
Further linkage is needed to make (`has_eigenvalue`, `root_charpoly`) work transparently with
`matrix.is_hermitian.eigenvalues`. The definitions in `linear_map.is_symmetric` are in terms of
`module.End.has_eigenvalue` (and hence should be usable without considerable issues).
-/
variables {n : Type*} [fintype n] [decidable_eq n]
variables {R : Type*} [field R]
variables {A : matrix n n R}

open matrix polynomial
open linear_map module.End
open_locale matrix big_operators

namespace matrix

lemma det_eq_prod_roots_charpoly_of_splits (hAps : A.charpoly.splits (ring_hom.id R)) :
  A.det = (matrix.charpoly A).roots.prod :=
begin
  rw [det_eq_sign_charpoly_coeff, ← (charpoly_nat_degree_eq_dim A),
    polynomial.prod_roots_eq_coeff_zero_of_monic_of_split A.charpoly_monic (hAps),
    ← mul_assoc, ← pow_two, pow_right_comm, neg_one_sq, one_pow, one_mul],
end

lemma trace_eq_sum_roots_charpoly_of_splits (hAps : A.charpoly.splits (ring_hom.id R)) :
  A.trace = (matrix.charpoly A).roots.sum :=
begin
  casesI is_empty_or_nonempty n,
  { rw [matrix.trace, fintype.sum_empty, matrix.charpoly,
      det_eq_one_of_card_eq_zero (fintype.card_eq_zero_iff.2 h), polynomial.roots_one,
      multiset.empty_eq_zero, multiset.sum_zero], },
  { rw [trace_eq_neg_charpoly_coeff, neg_eq_iff_eq_neg,
      ← polynomial.sum_roots_eq_next_coeff_of_monic_of_split A.charpoly_monic (hAps),
      next_coeff, charpoly_nat_degree_eq_dim,
      if_neg (fintype.card_ne_zero : fintype.card n ≠ 0)], },
end
variables (A)

lemma det_eq_prod_roots_charpoly [is_alg_closed R] : A.det = (matrix.charpoly A).roots.prod :=
det_eq_prod_roots_charpoly_of_splits (is_alg_closed.splits A.charpoly)

lemma trace_eq_sum_roots_charpoly [is_alg_closed R] : A.trace = (matrix.charpoly A).roots.sum :=
trace_eq_sum_roots_charpoly_of_splits (is_alg_closed.splits A.charpoly)


lemma root_charpoly_of_has_eigenvalue (A : matrix n n R) (μ : R)
  (heig : has_eigenvalue (matrix.to_lin' A) μ) :
  A.charpoly.is_root μ:=
begin
  have va := has_eigenvalue.exists_has_eigenvector heig,
  have xa : (∃ (v : n → R) (H : v ≠ 0), (μ • 1 - A).mul_vec v = 0),
  { cases va with v hv,
    use v,
    rw [has_eigenvector, mem_eigenspace_iff,to_lin'_apply, and_comm, eq_comm] at hv,
    rwa [sub_mul_vec, smul_mul_vec_assoc, one_mul_vec, sub_eq_zero], },
  rw [matrix.charpoly, is_root, eval_det, mat_poly_equiv_charmatrix,
    eval_sub, eval_C, eval_X, coe_scalar,← (matrix.exists_mul_vec_eq_zero_iff.1 xa)],
end

lemma has_eigenvalue_of_root_charpoly (A : matrix n n R) (μ : R) (h : A.charpoly.is_root μ) :
  has_eigenvalue (matrix.to_lin' A) μ :=
begin
  rw [matrix.charpoly, is_root, eval_det, mat_poly_equiv_charmatrix, eval_sub, eval_C, eval_X,
    coe_scalar] at h,
  dsimp only at h,
  obtain ⟨v, hv_nz, hv⟩ := matrix.exists_mul_vec_eq_zero_iff.2 h,
  rw [sub_mul_vec, smul_mul_vec_assoc, one_mul_vec, sub_eq_zero, eq_comm] at hv,
  rw [has_eigenvalue, submodule.ne_bot_iff],
  use v,
  rw [mem_eigenspace_iff, to_lin'_apply],
  exact ⟨hv, hv_nz⟩,
end

lemma root_charpoly_iff_has_eigenvalue (A : matrix n n R) (μ : R) :
  A.charpoly.is_root μ ↔ has_eigenvalue (matrix.to_lin' A) μ :=
⟨has_eigenvalue_of_root_charpoly _ _, root_charpoly_of_has_eigenvalue _ _⟩

lemma root_charpoly_iff_root_minpoly (A : matrix n n R) (μ : R) :
  (minpoly R (matrix.to_lin' A)).is_root μ ↔ A.charpoly.is_root μ :=
by rw [root_charpoly_iff_has_eigenvalue, has_eigenvalue_iff_is_root]

end matrix
