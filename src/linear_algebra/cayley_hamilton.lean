/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import ring_theory.matrix_algebra
import ring_theory.polynomial_algebra
import linear_algebra.nonsingular_inverse

/-!
The Cayley-Hamilton theorem, over a commutative ring.

We use a nice proof from http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
-/

noncomputable theory

universes u v w

open polynomial matrix
open_locale big_operators

variables {R : Type u} [comm_ring R]
variables {n : Type w} [fintype n] [decidable_eq n]

open finset

/--
The "characteristic matrix" of `M : matrix n n R` is the matrix of polynomials $t I - M$.
The determinant of this matrix is the characteristic polynomial.
-/
def characteristic_matrix (M : matrix n n R) : matrix n n (polynomial R) :=
matrix.scalar n (X : polynomial R) - (λ i j, C (M i j))

@[simp] lemma characteristic_matrix_apply_eq (M : matrix n n R) (i : n) :
  characteristic_matrix M i i = (X : polynomial R) - C (M i i) :=
by simp only [characteristic_matrix, sub_left_inj, pi.sub_apply, scalar_apply_eq]

@[simp] lemma characteristic_matrix_apply_ne (M : matrix n n R) (i j : n) (h : i ≠ j) :
  characteristic_matrix M i j = - C (M i j) :=
by simp only [characteristic_matrix, pi.sub_apply, scalar_apply_ne _ _ _ h, zero_sub]

lemma matrix_polynomial_equiv_polynomial_matrix_characteristic_matrix (M : matrix n n R) :
  matrix_polynomial_equiv_polynomial_matrix (characteristic_matrix M) = X - C M :=
begin
  ext k i j,
  simp only [matrix_polynomial_equiv_polynomial_matrix_coeff_apply, coeff_sub, pi.sub_apply],
  by_cases h : i = j,
  { subst h, rw [characteristic_matrix_apply_eq, coeff_sub],
    simp only [coeff_X, coeff_C],
    split_ifs; simp, },
  { rw [characteristic_matrix_apply_ne _ _ _ h, coeff_X, coeff_neg, coeff_C, coeff_C],
    split_ifs; simp [h], }
end

/--
The characteristic polynomial of a matrix `M` is given by $det (t I - M)$.
-/
def characteristic_polynomial (M : matrix n n R) : polynomial R :=
(characteristic_matrix M).det

/--
The Cayley-Hamilton theorem, that the characteristic polynomial of a matrix,
applied to the matrix itself, is zero.

This holds over any commutative ring.
-/
-- This proof follows http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
theorem cayley_hamilton (M : matrix n n R) :
  ((characteristic_polynomial M).map (algebra_map R (matrix n n R))).eval M = 0 :=
begin
  -- We begin with the fact $χ_M(t) I = adjugate (t I - M) * (t I - M)$,
  -- as an identity in `matrix n n (polynomial R)`.
  have h := calc
    (characteristic_polynomial M) • (1 : matrix n n (polynomial R))
         = (characteristic_matrix M).det • (1 : matrix n n (polynomial R)) : rfl
     ... = adjugate (characteristic_matrix M) * (characteristic_matrix M)  : (adjugate_mul _).symm,
  -- Using the algebra isomorphism `matrix n n (polynomial R) ≃ₐ[R] polynomial (matrix n n R)`,
  -- we have the same identity in `polynomial (matrix n n R)`.
  apply_fun matrix_polynomial_equiv_polynomial_matrix at h,
  simp only [matrix_polynomial_equiv_polynomial_matrix.map_mul,
    matrix_polynomial_equiv_polynomial_matrix_characteristic_matrix] at h,
  -- Because the coefficient ring `matrix n n R` is non-commutative,
  -- evaluation at `M` is not multiplicative.
  -- However, any polynomial which is a product of the form $N * (t I - M)$
  -- is sent to zero, because the evaluation function puts the polynomial variable
  -- to the right of any coefficients, so everything telescopes.
  apply_fun (λ p, p.eval M) at h,
  rw eval_mul_X_sub_C at h,
  -- Now $χ_M (t) I$, when thought of as a polynomial of matrices
  -- and evaluated at some `N` is exactly $χ_M (N)$.
  rw matrix_polynomial_equiv_polynomial_matrix_smul_one at h,
  -- Thus we have $χ_M(M) = 0$, which is the desired result.
  exact h,
end
