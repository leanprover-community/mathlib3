/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import linear_algebra.matrix.to_lin
import linear_algebra.invariant_basis_number

/-!
# Invertible matrices over a ring with invariant basis number are square.
-/

/-!
It's highly unfortunate that we need to write `comm_semiring R` here,
rather than just `semiring R`.

This is just as true for non-commutative semirings, and for the same reason,
and moreover it's useful: we'd like this result for division rings.

The problem is just that `matrix.to_lin'` requires the `comm_semiring` typeclass,
because when that was written no one was thinking about the noncommutative case.
-/
variables {n m : Type*} [fintype n] [decidable_eq n] [fintype m] [decidable_eq m]
variables {R : Type*} [semiring R] [invariant_basis_number R]

open_locale matrix

def matrix.to_lin'_of_inv' {R : Type*} [semiring R] {m : Type*} {n : Type*} [_inst_2 : fintype n]
[_inst_3 : decidable_eq n] [_inst_4 : fintype m] [_inst_5 : decidable_eq m] {M : matrix m n R} {M' : matrix n m R}
  (h : M ⬝ M' = 1) (h' : M' ⬝ M = 1) : ((m → R) ≃ₗ[R] n → R) := sorry

lemma matrix.square_of_invertible
  (M : matrix n m R) (N : matrix m n R) (h : M ⬝ N = 1) (h' : N ⬝ M = 1) :
  fintype.card n = fintype.card m :=
card_eq_of_lequiv R (matrix.to_lin'_of_inv' h h')
