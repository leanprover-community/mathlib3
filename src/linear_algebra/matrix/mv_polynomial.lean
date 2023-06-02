/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.matrix.determinant
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring

/-!
# Matrices of multivariate polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we prove results about matrices over an mv_polynomial ring.
In particular, we provide `matrix.mv_polynomial_X` which associates every entry of a matrix with a
unique variable.

## Tags

matrix determinant, multivariate polynomial
-/
variables {m n R S : Type*}

namespace matrix

variables (m n R)

/-- The matrix with variable `X (i,j)` at location `(i,j)`. -/
noncomputable def mv_polynomial_X [comm_semiring R] : matrix m n (mv_polynomial (m × n) R) :=
of $ λ i j, mv_polynomial.X (i, j)

-- TODO: set as an equation lemma for `mv_polynomial_X`, see mathlib4#3024
@[simp]
lemma mv_polynomial_X_apply [comm_semiring R] (i j) :
  mv_polynomial_X m n R i j = mv_polynomial.X (i, j) := rfl

variables {m n R S}

/-- Any matrix `A` can be expressed as the evaluation of `matrix.mv_polynomial_X`.

This is of particular use when `mv_polynomial (m × n) R` is an integral domain but `S` is
not, as if the `mv_polynomial.eval₂` can be pulled to the outside of a goal, it can be solved in
under cancellative assumptions. -/
lemma mv_polynomial_X_map_eval₂ [comm_semiring R] [comm_semiring S]
  (f : R →+* S) (A : matrix m n S) :
  (mv_polynomial_X m n R).map (mv_polynomial.eval₂ f $ λ p : m × n, A p.1 p.2) = A :=
ext $ λ i j, mv_polynomial.eval₂_X _ (λ p : m × n, A p.1 p.2) (i, j)

/-- A variant of `matrix.mv_polynomial_X_map_eval₂` with a bundled `ring_hom` on the LHS. -/
lemma mv_polynomial_X_map_matrix_eval [fintype m] [decidable_eq m]
  [comm_semiring R] (A : matrix m m R) :
  (mv_polynomial.eval $ λ p : m × m, A p.1 p.2).map_matrix (mv_polynomial_X m m R) = A :=
mv_polynomial_X_map_eval₂ _ A

variables (R)

/-- A variant of `matrix.mv_polynomial_X_map_eval₂` with a bundled `alg_hom` on the LHS. -/
lemma mv_polynomial_X_map_matrix_aeval [fintype m] [decidable_eq m]
  [comm_semiring R] [comm_semiring S] [algebra R S] (A : matrix m m S) :
  (mv_polynomial.aeval $ λ p : m × m, A p.1 p.2).map_matrix (mv_polynomial_X m m R) = A :=
mv_polynomial_X_map_eval₂ _ A

variables (m R)

/-- In a nontrivial ring, `matrix.mv_polynomial_X m m R` has non-zero determinant. -/
lemma det_mv_polynomial_X_ne_zero [decidable_eq m] [fintype m] [comm_ring R] [nontrivial R] :
  det (mv_polynomial_X m m R) ≠ 0 :=
begin
  intro h_det,
  have := congr_arg matrix.det (mv_polynomial_X_map_matrix_eval (1 : matrix m m R)),
  rw [det_one, ←ring_hom.map_det, h_det, ring_hom.map_zero] at this,
  exact zero_ne_one this,
end

end matrix
