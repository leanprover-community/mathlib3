/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import analysis.inner_product_space.adjoint
import analysis.inner_product_space.pi_L2
import linear_algebra.matrix.to_lin

noncomputable theory
open_locale big_operators

variables {𝕜 : Type*} {ι₁ : Type*} {ι₂ : Type*} [is_R_or_C 𝕜]
variables [fintype ι₁] [fintype ι₂] [decidable_eq ι₁] [decidable_eq ι₂]

namespace matrix

local notation `𝓔` := euclidean_space 𝕜

example (f : (ι₁ → 𝕜) →ₗ[𝕜] (ι₂ → 𝕜)) : 𝓔 ι₁ →ₗ[𝕜] 𝓔 ι₂ := f
example : inner_product_space 𝕜 (𝓔 ι₁) := by apply_instance
example (A : matrix ι₂ ι₁ 𝕜) : 𝓔 ι₁ →ₗ[𝕜] 𝓔 ι₂ := A.to_lin'
example (A : 𝓔 ι₁ →ₗ[𝕜] 𝓔 ι₂) : 𝓔 ι₂ →ₗ[𝕜] 𝓔 ι₁ := A.adjoint
example (A : matrix ι₂ ι₁ 𝕜) : 𝓔 ι₂ →ₗ[𝕜] 𝓔 ι₁ :=
  (linear_map.adjoint : (𝓔 ι₁ →ₗ[𝕜] 𝓔 ι₂) ≃ₗ⋆[𝕜] (𝓔 ι₂ →ₗ[𝕜] 𝓔 ι₁)) A.to_lin'

lemma conj_transpose_eq_adjoint (A : matrix ι₂ ι₁ 𝕜) :
  (A.conj_transpose.to_lin' : 𝓔 ι₂ →ₗ[𝕜] 𝓔 ι₁) =
  (linear_map.adjoint : (𝓔 ι₁ →ₗ[𝕜] 𝓔 ι₂) ≃ₗ⋆[𝕜] (𝓔 ι₂ →ₗ[𝕜] 𝓔 ι₁)) A.to_lin' :=
begin
  sorry
end

--local notation `adj_to_lin` := λ v₁ v₂ A, @linear_map.adjoint 𝕜 _ _ _ _ _
--  (finite_dimensional.of_fintype_basis v₁) (finite_dimensional.of_fintype_basis v₂) (to_lin v₁ v₂ A)
--
--lemma conj_transpose_eq_adjoint (A : matrix n m 𝕜) :
--   (to_lin v₂ v₁ A.conj_transpose) = (adj_to_lin v₁ v₂ A) :=
--begin
--  haveI := finite_dimensional.of_fintype_basis v₁,
--  haveI := finite_dimensional.of_fintype_basis v₂,
--  refine (linear_map.eq_adjoint_iff_basis v₂ v₁ _ _).mpr _,
--  intros i j,
--  simp [to_lin_self, inner_sum, sum_inner],
--end
--
--example (A : matrix m n 𝕜) : (to_lin v₁ v₂ A.conj_transpose) = 0 :=
--begin
--  rw [conj_transpose_eq_adjoint],
--end

end matrix
