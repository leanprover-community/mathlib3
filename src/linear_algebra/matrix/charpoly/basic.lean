/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.apply_fun
import ring_theory.matrix_algebra
import ring_theory.polynomial_algebra
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.reindex
import tactic.squeeze

/-!
# Characteristic polynomials and the Cayley-Hamilton theorem

We define characteristic polynomials of matrices and
prove the Cayley–Hamilton theorem over arbitrary commutative rings.

## Main definitions

* `matrix.charpoly` is the characteristic polynomial of a matrix.

## Implementation details

We follow a nice proof from http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
-/

noncomputable theory

universes u v w

open polynomial matrix
open_locale big_operators

variables {R : Type u} [comm_ring R]
variables {n : Type w} [decidable_eq n] [fintype n]

open finset


/--
The "characteristic matrix" of `M : matrix n n R` is the matrix of polynomials $t I - M$.
The determinant of this matrix is the characteristic polynomial.
-/
def charmatrix (M : matrix n n R) : matrix n n (polynomial R) :=
matrix.scalar n (X : polynomial R) - (C : R →+* polynomial R).map_matrix M

@[simp] lemma charmatrix_apply_eq (M : matrix n n R) (i : n) :
  charmatrix M i i = (X : polynomial R) - C (M i i) :=
by simp only [charmatrix, sub_left_inj, pi.sub_apply, scalar_apply_eq,
  ring_hom.map_matrix_apply, map_apply, dmatrix.sub_apply]

@[simp] lemma charmatrix_apply_ne (M : matrix n n R) (i j : n) (h : i ≠ j) :
  charmatrix M i j = - C (M i j) :=
by simp only [charmatrix, pi.sub_apply, scalar_apply_ne _ _ _ h, zero_sub,
  ring_hom.map_matrix_apply, map_apply, dmatrix.sub_apply]

lemma mat_poly_equiv_charmatrix (M : matrix n n R) :
  mat_poly_equiv (charmatrix M) = X - C M :=
begin
  ext k i j,
  simp only [mat_poly_equiv_coeff_apply, coeff_sub, pi.sub_apply],
  by_cases h : i = j,
  { subst h, rw [charmatrix_apply_eq, coeff_sub],
    simp only [coeff_X, coeff_C],
    split_ifs; simp, },
  { rw [charmatrix_apply_ne _ _ _ h, coeff_X, coeff_neg, coeff_C, coeff_C],
    split_ifs; simp [h], }
end

lemma charmatrix_reindex {m : Type v} [decidable_eq m] [fintype m] (e : n ≃ m)
  (M : matrix n n R) : charmatrix (reindex e e M) = reindex e e (charmatrix M) :=
begin
  ext i j x,
  by_cases h : i = j,
  all_goals { simp [h] }
end

/--
The characteristic polynomial of a matrix `M` is given by $\det (t I - M)$.
-/
def matrix.charpoly (M : matrix n n R) : polynomial R :=
(charmatrix M).det

lemma matrix.charpoly_reindex {m : Type v} [decidable_eq m] [fintype m] (e : n ≃ m)
  (M : matrix n n R) : (reindex e e M).charpoly = M.charpoly :=
begin
  unfold matrix.charpoly,
  rw [charmatrix_reindex, matrix.det_reindex_self]
end

/--
The **Cayley-Hamilton Theorem**, that the characteristic polynomial of a matrix,
applied to the matrix itself, is zero.

This holds over any commutative ring.
-/
-- This proof follows http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
theorem matrix.aeval_self_charpoly (M : matrix n n R) :
  aeval M M.charpoly = 0 :=
begin
  -- We begin with the fact $χ_M(t) I = adjugate (t I - M) * (t I - M)$,
  -- as an identity in `matrix n n (polynomial R)`.
  have h : M.charpoly • (1 : matrix n n (polynomial R)) =
    adjugate (charmatrix M) * (charmatrix M) :=
    (adjugate_mul _).symm,
  -- Using the algebra isomorphism `matrix n n (polynomial R) ≃ₐ[R] polynomial (matrix n n R)`,
  -- we have the same identity in `polynomial (matrix n n R)`.
  apply_fun mat_poly_equiv at h,
  simp only [mat_poly_equiv.map_mul,
    mat_poly_equiv_charmatrix] at h,
  -- Because the coefficient ring `matrix n n R` is non-commutative,
  -- evaluation at `M` is not multiplicative.
  -- However, any polynomial which is a product of the form $N * (t I - M)$
  -- is sent to zero, because the evaluation function puts the polynomial variable
  -- to the right of any coefficients, so everything telescopes.
  apply_fun (λ p, p.eval M) at h,
  rw eval_mul_X_sub_C at h,
  -- Now $χ_M (t) I$, when thought of as a polynomial of matrices
  -- and evaluated at some `N` is exactly $χ_M (N)$.
  rw [mat_poly_equiv_smul_one, eval_map] at h,
  -- Thus we have $χ_M(M) = 0$, which is the desired result.
  exact h,
end
