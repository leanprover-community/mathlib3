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

lemma is_basis_free_monoid (R : Type*) (X : Type*) [comm_ring R] :
  is_basis R (λ x : free_monoid X, free_monoid.lift (ι R) x) :=
begin
  convert (equiv_monoid_algebra_free_monoid.symm.to_linear_equiv : _ ≃ₗ[R] free_algebra R X)
    .is_basis finsupp.is_basis_single_one,
  ext x,
  rw ←one_smul R (free_monoid.lift _ _),
  exact (monoid_algebra.lift_single _ _ _).symm,
end

lemma dim_eq {K : Type*} {X : Type*} [field K] :
  vector_space.dim K (free_algebra K X) = cardinal.mk (list X) :=
(cardinal.lift_inj.mp (is_basis_free_monoid K X).mk_eq_dim).symm

end free_algebra
