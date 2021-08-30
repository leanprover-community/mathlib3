/-
Copyright (c) 2020 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import linear_algebra.dual
import linear_algebra.finsupp_vector_space
import linear_algebra.finite_dimensional
import linear_algebra.contraction

/-!
# The Coevaluation function on finite dimensional vector spaces

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
open_locale tensor_product classical

universes u v

variables (K : Type u) [field K]
variables (V : Type v) [add_comm_group V] [module K V] [finite_dimensional K V]

def coevaluation : K →ₗ[K] V ⊗[K] (module.dual K V) :=
  let bK := basis.of_vector_space K K in
  let bV := basis.of_vector_space K V in
  let bV' := bV.dual_basis in
  let bVV := finsupp.basis.tensor_product bV bV' in
  bK.constr K $ λ x, bVV.repr.symm $ finsupp.of_support_finite (λ i, if i.1 = i.2 then 1 else 0)
   (by { apply set.finite.of_fintype })

end coevaluation
