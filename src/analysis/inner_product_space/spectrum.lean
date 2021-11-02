/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.inner_product_space.rayleigh
import analysis.inner_product_space.pi_L2

/-! # Spectral theory of self-adjoint operators

This file covers the spectral theory of self-adjoint operators on an inner product space.

The first part of the file covers general properties, true without any condition on boundedness or
compactness of the operator or finite-dimensionality of the underlying space, notably:
* `is_self_adjoint.conj_eigenvalue_eq_self`: the eigenvalues are real
* `is_self_adjoint.orthogonal_family_eigenspaces`: the eigenspaces are orthogonal
* `is_self_adjoint.orthogonal_supr_eigenspaces`: the restriction of the operator to the mutual
  orthogonal complement of the eigenspaces has, itself, no eigenvectors

The second part of the file covers properties of self-adjoint operators in finite dimension.  The
definition `is_self_adjoint.diagonalization` provides a linear isometry equivalence from a space
`E` to the direct sum of the eigenspaces of a self-adjoint operator `T` on `E`.  The theorem
`is_self_adjoint.diagonalization_apply_self_apply` states that, when `T` is transferred via this
equivalence to an operator on the direct sum, it acts diagonally.  This is the *diagonalization
theorem* for self-adjoint operators on finite-dimensional inner product spaces.

## TODO

Spectral theory for compact self-adjoint operators, bounded self-adjoint operators.

## Tags

self-adjoint operator, spectral theorem, diagonalization theorem

-/

variables {𝕜 : Type*} [is_R_or_C 𝕜]
variables {E : Type*} [inner_product_space 𝕜 E]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y

local attribute [instance] fact_one_le_two_real

open_locale classical big_operators complex_conjugate
open module.End

namespace is_self_adjoint

variables {T : E →ₗ[𝕜] E} (hT : is_self_adjoint T)
include hT

/-- A self-adjoint operator preserves orthogonal complements of its eigenspaces. -/
lemma invariant_orthogonal_eigenspace (μ : 𝕜) : ∀ v ∈ (eigenspace T μ)ᗮ, T v ∈ (eigenspace T μ)ᗮ :=
begin
  intros v hv w hw,
  have : T w = (μ:𝕜) • w := by rwa mem_eigenspace_iff at hw,
  simp [← hT w, this, inner_smul_left, hv w hw]
end

/-- The eigenvalues of a self-adjoint operator are real. -/
lemma conj_eigenvalue_eq_self {μ : 𝕜} (hμ : has_eigenvalue T μ) : conj μ = μ :=
begin
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_has_eigenvector,
  rw mem_eigenspace_iff at hv₁,
  simpa [hv₂, inner_smul_left, inner_smul_right, hv₁] using hT v v
end

/-- The eigenspaces of a self-adjoint operator are mutually orthogonal. -/
lemma orthogonal_family_eigenspaces : orthogonal_family 𝕜 (eigenspace T) :=
begin
  intros μ ν hμν v hv w hw,
  by_cases hv' : v = 0,
  { simp [hv'] },
  have H := hT.conj_eigenvalue_eq_self (has_eigenvalue_of_has_eigenvector ⟨hv, hv'⟩),
  rw mem_eigenspace_iff at hv hw,
  refine or.resolve_left _ hμν.symm,
  simpa [inner_smul_left, inner_smul_right, hv, hw, H] using (hT v w).symm
end

lemma orthogonal_family_eigenspaces' : orthogonal_family 𝕜 (λ μ : eigenvalues T, eigenspace T μ) :=
hT.orthogonal_family_eigenspaces.comp subtype.coe_injective

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on an inner
product space is an invariant subspace of the operator. -/
lemma orthogonal_supr_eigenspaces_invariant ⦃v : E⦄ (hv : v ∈ (⨆ μ, eigenspace T μ)ᗮ) :
  T v ∈ (⨆ μ, eigenspace T μ)ᗮ :=
begin
  rw ← submodule.infi_orthogonal at ⊢ hv,
  exact T.infi_invariant hT.invariant_orthogonal_eigenspace v hv
end

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on an inner
product space has no eigenvalues. -/
lemma orthogonal_supr_eigenspaces (μ : 𝕜) :
  eigenspace (T.restrict hT.orthogonal_supr_eigenspaces_invariant) μ = ⊥ :=
begin
  set p : submodule 𝕜 E := (⨆ μ, eigenspace T μ)ᗮ,
  refine eigenspace_restrict_eq_bot hT.orthogonal_supr_eigenspaces_invariant _,
  have H₂ : p ≤ (eigenspace T μ)ᗮ := submodule.orthogonal_le (le_supr _ _),
  exact (eigenspace T μ).orthogonal_disjoint.mono_right H₂
end

/-! ### Finite-dimensional theory -/

variables [finite_dimensional 𝕜 E]

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on a
finite-dimensional inner product space is trivial. -/
lemma orthogonal_supr_eigenspaces_eq_bot : (⨆ μ, eigenspace T μ)ᗮ = ⊥ :=
begin
  have hT' : is_self_adjoint _ := hT.restrict_invariant hT.orthogonal_supr_eigenspaces_invariant,
  -- a self-adjoint operator on a nontrivial inner product space has an eigenvalue
  haveI := hT'.subsingleton_of_no_eigenvalue_finite_dimensional hT.orthogonal_supr_eigenspaces,
  exact submodule.eq_bot_of_subsingleton _,
end

lemma orthogonal_supr_eigenspaces_eq_bot' : (⨆ μ : eigenvalues T, eigenspace T μ)ᗮ = ⊥ :=
begin
  convert hT.orthogonal_supr_eigenspaces_eq_bot using 1,
  rw ← supr_ne_bot_subtype (λ μ, eigenspace T μ),
  refl,
end

/-- The eigenspaces of a self-adjoint operator on a finite-dimensional inner product space `E` give
an internal direct sum decomposition of `E`. -/
lemma direct_sum_submodule_is_internal :
  direct_sum.submodule_is_internal (λ μ : eigenvalues T, eigenspace T μ) :=
by convert hT.orthogonal_family_eigenspaces'.submodule_is_internal_iff.mpr
  hT.orthogonal_supr_eigenspaces_eq_bot'

/-- Isometry from an inner product space `E` to the direct sum of the eigenspaces of some
self-adjoint operator `T` on `E`. -/
noncomputable def diagonalization : E ≃ₗᵢ[𝕜] pi_Lp 2 (λ μ : eigenvalues T, eigenspace T μ) :=
hT.direct_sum_submodule_is_internal.isometry_L2_of_orthogonal_family
  hT.orthogonal_family_eigenspaces'

@[simp] lemma diagonalization_symm_apply (w : pi_Lp 2 (λ μ : eigenvalues T, eigenspace T μ)) :
  hT.diagonalization.symm w = ∑ μ, w μ :=
hT.direct_sum_submodule_is_internal.isometry_L2_of_orthogonal_family_symm_apply
  hT.orthogonal_family_eigenspaces' w

/-- *Diagonalization theorem*, *spectral theorem*: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the decomposition of `E` into the
direct sum of the eigenspaces of `T`. -/
lemma diagonalization_apply_self_apply (v : E) (μ : eigenvalues T) :
  hT.diagonalization (T v) μ = (μ : 𝕜) • hT.diagonalization v μ :=
begin
  suffices : ∀ w : pi_Lp 2 (λ μ : eigenvalues T, eigenspace T μ),
    (T (hT.diagonalization.symm w)) = hT.diagonalization.symm (λ μ, (μ : 𝕜) • w μ),
  { simpa [linear_isometry_equiv.symm_apply_apply, -is_self_adjoint.diagonalization_symm_apply]
      using congr_arg (λ w, hT.diagonalization w μ) (this (hT.diagonalization v)) },
  intros w,
  have hwT : ∀ μ : eigenvalues T, T (w μ) = (μ : 𝕜) • w μ,
  { intros μ,
    simpa [mem_eigenspace_iff] using (w μ).prop },
  simp [hwT],
end

end is_self_adjoint
