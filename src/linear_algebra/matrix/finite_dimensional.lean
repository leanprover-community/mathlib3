/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import data.matrix.basic
import linear_algebra.finite_dimensional

/-!
# The finite-dimensional space of matrices

This file shows that `m` by `n` matrices form a finite-dimensional space,
and proves the `finrank` of that space is equal to `card m * card n`.

## Main definitions

 * `matrix.finite_dimensional`: matrices form a finite dimensional vector space over a field `K`
 * `matrix.finrank_matrix`: the `finrank` of `matrix m n R` is `card m * card n`

## Tags

matrix, finite dimensional, findim, finrank

-/

universes u v

namespace matrix

section finite_dimensional

variables {m n : Type*} [fintype m] [fintype n]
variables {R : Type v} [field R]

instance : finite_dimensional R (matrix m n R) :=
linear_equiv.finite_dimensional (linear_equiv.curry R m n)

/--
The dimension of the space of finite dimensional matrices
is the product of the number of rows and columns.
-/
@[simp] lemma finrank_matrix :
  finite_dimensional.finrank R (matrix m n R) = fintype.card m * fintype.card n :=
by rw [@linear_equiv.finrank_eq R (matrix m n R) _ _ _ _ _ _ (linear_equiv.curry R m n).symm,
       finite_dimensional.finrank_fintype_fun_eq_card, fintype.card_prod]

end finite_dimensional

end matrix
