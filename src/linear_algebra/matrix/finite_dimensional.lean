/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import data.matrix.basic
import linear_algebra.finite_dimensional
import linear_algebra.free_module.finite.matrix
import linear_algebra.matrix.to_lin

/-!
# The finite-dimensional space of matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file shows that `m` by `n` matrices form a finite-dimensional space.
Note that this is proven more generally elsewhere over modules as `module.finite.matrix`; this file
exists only to provide an entry in the instance list for `finite_dimensional`.

## Main definitions

 * `matrix.finite_dimensional`: matrices form a finite dimensional vector space over a field `K`
 * `linear_map.finite_dimensional`

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

namespace linear_map

variables {K : Type*} [field K]
variables {V : Type*} [add_comm_group V] [module K V] [finite_dimensional K V]
variables {W : Type*} [add_comm_group W] [module K W] [finite_dimensional K W]

instance finite_dimensional : finite_dimensional K (V →ₗ[K] W) :=
module.finite.linear_map _ _

variables {A : Type*} [ring A] [algebra K A] [module A V] [is_scalar_tower K A V]
  [module A W] [is_scalar_tower K A W]

/-- Linear maps over a `k`-algebra are finite dimensional (over `k`) if both the source and
target are, as they form a subspace of all `k`-linear maps. -/
instance finite_dimensional' : finite_dimensional K (V →ₗ[A] W) :=
finite_dimensional.of_injective (restrict_scalars_linear_map K A V W)
  (restrict_scalars_injective _)

end linear_map
