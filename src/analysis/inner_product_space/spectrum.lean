/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

import analysis.inner_product_space.rayleigh
import analysis.inner_product_space.pi_L2


variables {𝕜 : Type*} [is_R_or_C 𝕜]
variables {E : Type*} [inner_product_space 𝕜 E]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y

open_locale classical big_operators
open module.End

-- move this
lemma foo {ι L : Type*} [complete_lattice L] (V : ι → L) :
  (⨆ i : {i // V i ≠ ⊥}, V i) = ⨆ i, V i :=
begin
  by_cases htriv : ∀ i, V i = ⊥,
  { simp only [htriv, supr_bot] },
  refine le_antisymm (supr_comp_le V _) (supr_le_supr2 _),
  intros i,
  by_cases hi : V i = ⊥,
  { rw hi,
    obtain ⟨i₀, hi₀⟩ := not_forall.mp htriv,
    exact ⟨⟨i₀, hi₀⟩, bot_le⟩ },
  { exact ⟨⟨i, hi⟩, rfl.le⟩ },
end

-- move this
/-- The infimum of a family of invariant submodule of an operator is also an invariant submodule.
-/
lemma linear_map.infi_invariant {ι : Type*} (T : E →ₗ[𝕜] E) {V : ι → submodule 𝕜 E}
  (hT : ∀ i, ∀ v ∈ (V i), T v ∈ V i) :
  ∀ v ∈ infi V, T v ∈ infi V :=
begin
  have : ∀ i, (V i).map T ≤ V i,
  { rintros i - ⟨v, hv, rfl⟩,
    exact hT i v hv },
  suffices : (infi V).map T ≤ infi V,
  { intros v hv,
    exact this ⟨v, hv, rfl⟩ },
  refine le_infi _,
  intros i,
  exact (submodule.map_mono (infi_le V i)).trans (this i),
end

namespace self_adjoint

variables {T : E →ₗ[𝕜] E} (hT : self_adjoint T)
include hT

/-- If a self-adjoint operator preserves a submodule, its restriction to that submodule is
self-adjoint. -/
lemma restrict_invariant {V : submodule 𝕜 E} (hV : ∀ v ∈ V, T v ∈ V) :
  self_adjoint (T.restrict hV) :=
λ v w, hT v w

/-- A self-adjoint operator preserves orthogonal complements of its eigenspaces. -/
lemma invariant_orthogonal_eigenspace (μ : 𝕜) : ∀ v ∈ (eigenspace T μ)ᗮ, T v ∈ (eigenspace T μ)ᗮ :=
begin
  intros v hv w hw,
  have : T w = (μ:𝕜) • w := by rwa mem_eigenspace_iff at hw,
  simp [← hT w, this, inner_smul_left, hv w hw]
end

/-- The eigenvalues of a self-adjoint operator are real. -/
lemma conj_eigenvalue_eq_self {μ : 𝕜} (hμ : has_eigenvalue T μ) :
  is_R_or_C.conj μ = μ :=
begin
  obtain ⟨v, hv₁, hv₂⟩ := hμ.has_eigenvector,
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

/-! ### Finite-dimensional theory -/

variables [finite_dimensional 𝕜 E]

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on a
finite-dimensional inner product space is trivial. -/
lemma orthogonal_supr_eigenspaces : (⨆ μ, eigenspace T μ)ᗮ = ⊥ :=
begin
  suffices : subsingleton (supr (eigenspace T))ᗮ,
  { resetI,
    exact submodule.eq_bot_of_subsingleton },
  rw ← submodule.infi_orthogonal,
  set p : submodule 𝕜 E := ⨅ μ, (eigenspace T μ)ᗮ,
  have hp : ∀ v ∈ p, T v ∈ p := T.infi_invariant hT.invariant_orthogonal_eigenspace,
  have hp_eig : ∀ μ, eigenspace (T.restrict hp) μ = ⊥,-- := λ μ, baz₃ _ _ (infi_le _ _),
  { intros μ,
    have H₂ : p ≤ (eigenspace T μ)ᗮ := infi_le _ _,
    exact module.End.eigenspace_restrict_eq_bot hp ((eigenspace T μ).orthogonal_disjoint.mono_right H₂) },
  exact (hT.restrict_invariant hp).subsingleton_of_no_eigenvalue_finite_dimensional hp_eig,
end

lemma orthogonal_supr_eigenspaces' : (⨆ μ : eigenvalues T, eigenspace T μ)ᗮ = ⊥ :=
begin
  convert hT.orthogonal_supr_eigenspaces using 1,
  rw ← foo (λ μ, eigenspace T μ),
  refl,
end

/-- The eigenspaces of a self-adjoint operator on a finite-dimensional inner product space `E` give
an internal direct sum decomposition of `E`. -/
lemma direct_sum_submodule_is_internal :
  direct_sum.submodule_is_internal (λ μ : eigenvalues T, eigenspace T μ) :=
by convert hT.orthogonal_family_eigenspaces'.submodule_is_internal_iff.mpr
  hT.orthogonal_supr_eigenspaces'

/-- Isometry from an inner product space `E` to the direct sum of the eigenspaces of some
self-adjoint operator `T` on `E`. -/
noncomputable def diagonalization :
  E ≃ₗᵢ[𝕜] pi_Lp 2 one_le_two (λ μ : eigenvalues T, eigenspace T μ) :=
hT.direct_sum_submodule_is_internal.isometry_L2_of_orthogonal_family
  hT.orthogonal_family_eigenspaces'

@[simp] lemma diagonalization_symm_apply
  (w : pi_Lp 2 one_le_two (λ μ : eigenvalues T, eigenspace T μ)) :
  hT.diagonalization.symm w = ∑ μ, w μ :=
hT.direct_sum_submodule_is_internal.isometry_L2_of_orthogonal_family_symm_apply
  hT.orthogonal_family_eigenspaces' w

/-- *Diagonalization theorem*, *spectral theorem*: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the decomposition of `E` into the
direct sum of the eigenspaces of `T`. -/
lemma diagonalization_apply_self_apply (v : E) (μ : eigenvalues T) :
  hT.diagonalization (T v) μ = (μ : 𝕜) • hT.diagonalization v μ :=
begin
  suffices : ∀ w : pi_Lp 2 one_le_two (λ μ : eigenvalues T, eigenspace T μ),
    (T (hT.diagonalization.symm w)) = hT.diagonalization.symm (λ μ, (μ : 𝕜) • w μ),
  { simpa [linear_isometry_equiv.symm_apply_apply, -self_adjoint.diagonalization_symm_apply]
      using congr_arg (λ w, hT.diagonalization w μ) (this (hT.diagonalization v)) },
  intros w,
  have hwT : ∀ μ : eigenvalues T, T (w μ) = (μ : 𝕜) • w μ,
  { intros μ,
    simpa [mem_eigenspace_iff] using (w μ).prop },
  simp [hwT],
end

end self_adjoint
