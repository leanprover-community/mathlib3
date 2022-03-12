/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import data.matrix.basic

/-!
# Trace of a matrix

This file defines the trace of a matrix, the linear map
sending a matrix to the sum of its diagonal entries.

See also `linear_algebra.trace` for the trace of an endomorphism.

## Tags

matrix, trace, diagonal

-/

open_locale big_operators
open_locale matrix

namespace matrix

section trace

universes u v w

variables {m : Type*} (n : Type*) {p : Type*}
variables (R : Type*) (M : Type*) [semiring R] [add_comm_monoid M] [module R M]

/--
The diagonal of a square matrix.
-/
def diag : (matrix n n M) →ₗ[R] n → M :=
{ to_fun    := λ A i, A i i,
  map_add'  := by { intros, ext, refl, },
  map_smul' := by { intros, ext, refl, } }

variables {n} {R} {M}

@[simp] lemma diag_apply (A : matrix n n M) (i : n) : diag n R M A i = A i i := rfl

@[simp] lemma diag_one [decidable_eq n] :
  diag n R R 1 = λ i, 1 := by { dunfold diag, ext, simp [one_apply_eq] }

@[simp] lemma diag_transpose (A : matrix n n M) : diag n R M Aᵀ = diag n R M A := rfl

@[simp] lemma diag_col_mul_row (a b : n → R) : diag n R R (col a ⬝ row b) = a * b :=
by { ext, simp [matrix.mul_apply] }

variables (n) (R) (M)

/--
The trace of a square matrix.
-/
def trace [fintype n] : (matrix n n M) →ₗ[R] M :=
{ to_fun    := λ A, ∑ i, diag n R M A i,
  map_add'  := by { intros, apply finset.sum_add_distrib, },
  map_smul' := by { intros, simp [finset.smul_sum], } }

variables {n} {R} {M} [fintype n] [fintype m] [fintype p]

@[simp] lemma trace_diag (A : matrix n n M) : trace n R M A = ∑ i, diag n R M A i := rfl

lemma trace_apply (A : matrix n n M) : trace n R M A = ∑ i, A i i := rfl

@[simp] lemma trace_one [decidable_eq n] :
  trace n R R 1 = fintype.card n :=
have h : trace n R R 1 = ∑ i, diag n R R 1 i := rfl,
by simp_rw [h, diag_one, finset.sum_const, nsmul_one]; refl

@[simp] lemma trace_transpose (A : matrix n n M) : trace n R M Aᵀ = trace n R M A := rfl

@[simp] lemma trace_transpose_mul (A : matrix m n R) (B : matrix n m R) :
  trace n R R (Aᵀ ⬝ Bᵀ) = trace m R R (A ⬝ B) := finset.sum_comm

lemma trace_mul_comm {S : Type v} [comm_semiring S] (A : matrix m n S) (B : matrix n m S) :
  trace m S S (A ⬝ B) = trace n S S (B ⬝ A) :=
by rw [←trace_transpose, ←trace_transpose_mul, transpose_mul]

lemma trace_mul_cycle {S : Type v} [comm_semiring S]
  (A : matrix m n S) (B : matrix n p S) (C : matrix p m S) :
  trace _ S S (A ⬝ B ⬝ C) = trace p S S (C ⬝ A ⬝ B) :=
by rw [trace_mul_comm, matrix.mul_assoc]

lemma trace_mul_cycle' {S : Type v} [comm_semiring S]
  (A : matrix m n S) (B : matrix n p S) (C : matrix p m S) :
  trace _ S S (A ⬝ (B ⬝ C)) = trace p S S (C ⬝ (A ⬝ B)) :=
by rw [←matrix.mul_assoc, trace_mul_comm]

@[simp] lemma trace_col_mul_row (a b : n → R) : trace n R R (col a ⬝ row b) = dot_product a b :=
by simp [dot_product]

/-! ### Special cases for `fin n`

While `simp [fin.sum_univ_succ]` can prove these, we include them for convenience and consistency
with `matrix.det_fin_two` etc.
-/

@[simp] lemma trace_fin_zero (A : matrix (fin 0) (fin 0) R) : trace _ R R A = 0 :=
rfl

lemma trace_fin_one (A : matrix (fin 1) (fin 1) R) : trace _ R R A = A 0 0 :=
add_zero _

lemma trace_fin_two (A : matrix (fin 2) (fin 2) R) : trace _ R R A = A 0 0 + A 1 1 :=
congr_arg ((+) _) (add_zero (A 1 1))

lemma trace_fin_three (A : matrix (fin 3) (fin 3) R) : trace _ R R A = A 0 0 + A 1 1 + A 2 2 :=
by { rw [← add_zero (A 2 2), add_assoc], refl }

end trace

end matrix
