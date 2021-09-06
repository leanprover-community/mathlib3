/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import linear_algebra.dual
import linear_algebra.finsupp_vector_space
import linear_algebra.finite_dimensional
import linear_algebra.contraction

/-!
# The coevaluation map on finite dimensional vector spaces

Given a finite dimensional vector space `V` over a field `K` this describes the canonical linear map
from `K` to `V ⊗ dual K V` which corresponds to the identity function on `V`.

## Tags

coevaluation, dual module, tensor product

## Future work

* Prove that this is independent of the choice of basis on `V`.
-/
noncomputable theory

section coevaluation
open tensor_product finite_dimensional
open_locale tensor_product big_operators

universes u v

variables (K : Type u) [field K]
variables (V : Type v) [add_comm_group V] [module K V] [finite_dimensional K V]

/-- The coevaluation map is a linear map from a field `K` to a finite dimensional
  vector space `V`. -/
def coevaluation : K →ₗ[K] V ⊗[K] (module.dual K V) :=
  let bV := basis.of_vector_space K V in
  (basis.singleton unit K).constr K $
    λ _, ∑ (i : basis.of_vector_space_index K V), bV i ⊗ₜ[K] bV.coord i

end coevaluation
