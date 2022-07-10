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

variables {n m : Type*} [fintype n] [decidable_eq n] [fintype m] [decidable_eq m]
variables {R : Type*} [semiring R] [invariant_basis_number R]

open_locale matrix

lemma matrix.square_of_invertible
  (M : matrix n m R) (N : matrix m n R) (h : M ⬝ N = 1) (h' : N ⬝ M = 1) :
  fintype.card n = fintype.card m :=
card_eq_of_lequiv R (matrix.to_linear_equiv_right'_of_inv h' h)
