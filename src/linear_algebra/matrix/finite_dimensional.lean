/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import data.matrix.basic
import linear_algebra.finite_dimensional

/-!
# The finite-dimensional space of matrices

This file shows that `m` by `n` matrices form a finite-dimensional space.
Note that this is proven more generally elsewhere over modules as `module.finite.matrix`; this file
exists only to provide an entry in the instance list for `finite_dimensional`.

## Main definitions

 * `matrix.finite_dimensional`: matrices form a finite dimensional vector space over a field `K`

## Tags

matrix, finite dimensional, findim, finrank

-/

universes u v

namespace matrix

section finite_dimensional

variables {m n : Type*} {R : Type v} [field R]

instance [finite m] [finite n] : finite_dimensional R (matrix m n R) :=
module.finite.matrix

end finite_dimensional

end matrix
