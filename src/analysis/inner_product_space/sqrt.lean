/-
Copyright (c) 2022 Hans Parshall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hans Parshall
-/
import analysis.inner_product_space.adjoint
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.spectrum

/-! # The square root of a self-adjoint operator

We define the square root of a self-adjoint operator `T` on a finite-dimensional inner product
space `E` in terms of an orthonormal basis of eigenvectors for `T`.

## TODO

Once `analysis.inner_product_space.spectrum` contains spectral theory for bounded operators, we can
generalize to bounded self-adjoint operators.

-/

variables {𝕜 E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [finite_dimensional 𝕜 E]
  [decidable_eq 𝕜]
variables {n : ℕ} (hn : finite_dimensional.finrank 𝕜 E = n)

namespace inner_product_space
namespace is_self_adjoint

variables {T : E →ₗ[𝕜] E} (hT : is_self_adjoint T)

local notation `evec` := hT.eigenvector_basis hn
local notation `eval` := hT.eigenvalues hn

/-- The square root of a self-adjoint operator `T`.  This definition is only meaningful when `T` has
nonnegative eigenvalues. -/

noncomputable def sqrt : E →ₗ[𝕜] E :=
  basis.constr evec 𝕜 (λ (i : (fin n)), (real.sqrt(eval i) : 𝕜) • (evec i))

lemma sqrt_apply {i : (fin n)} :
  (hT.sqrt hn) (evec i) = (real.sqrt (eval i) : 𝕜) • (evec i) :=
    by simp only [is_self_adjoint.sqrt, (evec).constr_basis]

lemma sqrt_mul_self_eq (hnn : ∀ (i : (fin n)), 0 ≤ eval i) :
  (hT.sqrt hn) * (hT.sqrt hn) = T :=
begin
  apply basis.ext evec,
  intro i,
  simp only [linear_map.mul_apply, inner_product_space.is_self_adjoint.apply_eigenvector_basis,
    is_self_adjoint.sqrt_apply, ring_hom.id_apply, linear_map.map_smulₛₗ, smul_smul],
  norm_cast,
  rw real.mul_self_sqrt (hnn i),
end

lemma sqrt_self_adjoint : is_self_adjoint (hT.sqrt hn) :=
begin
  rw [linear_map.is_self_adjoint_iff_eq_adjoint, linear_map.eq_adjoint_iff_basis (evec) (evec)],
  intros i j,
  simp only [is_self_adjoint.sqrt_apply, inner_smul_left, inner_smul_right, is_R_or_C.conj_of_real,
    is_R_or_C.of_real_inj, mul_eq_mul_right_iff],
  by_cases hij : i = j,
  simp only [hij, true_or, eq_self_iff_true, inner_self_eq_zero],
  have orthonormal_evec : orthonormal 𝕜 evec := is_self_adjoint.eigenvector_basis_orthonormal hT hn,
  rw orthonormal_iff_ite at orthonormal_evec,
  specialize orthonormal_evec i j,
  simp only [orthonormal_evec, ite_eq_right_iff],
  tauto,
end

end is_self_adjoint
end inner_product_space
