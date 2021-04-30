/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.basis
import algebra.free_algebra
import linear_algebra.finsupp_vector_space
/-!
# Linear algebra properties of `free_algebra R X`

This file provides a `free_monoid X` basis on the `free_algebra R X`, and uses it to show the
dimension of the algebra is the cardinality of `list X`
-/
namespace free_algebra

@[simps]
noncomputable def basis_free_monoid (R : Type*) (X : Type*) [comm_ring R] :
  basis (free_monoid X) R (free_algebra R X) :=
finsupp.basis_single_one.map
  (equiv_monoid_algebra_free_monoid.symm.to_linear_equiv : _ ≃ₗ[R] free_algebra R X)

lemma dim_eq {K : Type*} {X : Type*} [field K] :
  module.rank K (free_algebra K X) = cardinal.mk (list X) :=
(cardinal.lift_inj.mp (basis_free_monoid K X).mk_eq_dim).symm

end free_algebra
