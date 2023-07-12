/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import topology.algebra.module.basic
import linear_algebra.determinant

/-!
# The determinant of a continuous linear map.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

namespace continuous_linear_map

/-- The determinant of a continuous linear map, mainly as a convenience device to be able to
write `A.det` instead of `(A : M →ₗ[R] M).det`. -/
@[reducible] noncomputable def det {R : Type*} [comm_ring R]
  {M : Type*} [topological_space M] [add_comm_group M] [module R M] (A : M →L[R] M) : R :=
linear_map.det (A : M →ₗ[R] M)

end continuous_linear_map

namespace continuous_linear_equiv

@[simp] lemma det_coe_symm {R : Type*} [field R]
  {M : Type*} [topological_space M] [add_comm_group M] [module R M] (A : M ≃L[R] M) :
  (A.symm : M →L[R] M).det = (A : M →L[R] M).det ⁻¹ :=
linear_equiv.det_coe_symm A.to_linear_equiv

end continuous_linear_equiv
