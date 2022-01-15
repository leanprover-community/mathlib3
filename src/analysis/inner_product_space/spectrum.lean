/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.inner_product_space.rayleigh
import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.l2

/-! # Spectral theory of self-adjoint operators

This file covers the spectral theory of self-adjoint operators on an inner product space.

The first part of the file covers general properties, true without any condition on boundedness or
compactness of the operator or finite-dimensionality of the underlying space, notably:
* `is_self_adjoint.conj_eigenvalue_eq_self`: the eigenvalues are real
* `is_self_adjoint.orthogonal_family_eigenspaces`: the eigenspaces are orthogonal
* `is_self_adjoint.orthogonal_supr_eigenspaces`: the restriction of the operator to the mutual
  orthogonal complement of the eigenspaces has, itself, no eigenvectors

The second part of the file covers properties of self-adjoint operators in finite dimension.
Letting `T` be a self-adjoint operator on a finite-dimensional inner product space `T`,
* The definition `is_self_adjoint.diagonalization` provides a linear isometry equivalence `E` to
  the direct sum of the eigenspaces of `T`.  The theorem
  `is_self_adjoint.diagonalization_apply_self_apply` states that, when `T` is transferred via this
  equivalence to an operator on the direct sum, it acts diagonally.
* The definition `is_self_adjoint.eigenvector_basis` provides an orthonormal basis for `E`
  consisting of eigenvectors of `T`, with `is_self_adjoint.eigenvalues` giving the corresponding
  list of eigenvalues, as real numbers.  The definition `is_self_adjoint.diagonalization_basis`
  gives the associated linear isometry equivalence from `E` to Euclidean space, and the theorem
  `is_self_adjoint.diagonalization_basis_apply_self_apply` states that, when `T` is transferred via
  this equivalence to an operator on Euclidean space, it acts diagonally.

These are forms of the *diagonalization theorem* for self-adjoint operators on finite-dimensional
inner product spaces.

## TODO

Spectral theory for compact self-adjoint operators, bounded self-adjoint operators.

## Tags

self-adjoint operator, spectral theorem, diagonalization theorem

-/

variables {𝕜 : Type*} [is_R_or_C 𝕜] [dec_𝕜 : decidable_eq 𝕜]
variables {E : Type*} [inner_product_space 𝕜 E] [cplt : complete_space E]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y

local attribute [instance] fact_one_le_two_real fact_one_le_two_ennreal

open_locale big_operators complex_conjugate
open module.End

namespace inner_product_space
namespace is_self_adjoint

-- follows by expressing the eigenspace as the kernel of a operator, since kernel is closed
-- move this
instance [complete_space E] {T : E →ₗ[𝕜] E} (μ : 𝕜) : complete_space (eigenspace T μ) := sorry

variables {T : E →ₗ[𝕜] E} (hT : is_self_adjoint T)
include hT

/-- A self-adjoint operator preserves orthogonal complements of its eigenspaces. -/
lemma invariant_orthogonal_eigenspace (μ : 𝕜) (v : E) (hv : v ∈ (eigenspace T μ)ᗮ) :
  T v ∈ (eigenspace T μ)ᗮ :=
begin
  intros w hw,
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
lemma orthogonal_family_eigenspaces :
  @orthogonal_family 𝕜 _ _ _ _ (λ μ, eigenspace T μ) _ (λ μ, (eigenspace T μ).subtypeₗᵢ) :=
begin
  rintros μ ν hμν ⟨v, hv⟩ ⟨w, hw⟩,
  by_cases hv' : v = 0,
  { simp [hv'] },
  have H := hT.conj_eigenvalue_eq_self (has_eigenvalue_of_has_eigenvector ⟨hv, hv'⟩),
  rw mem_eigenspace_iff at hv hw,
  refine or.resolve_left _ hμν.symm,
  simpa [inner_smul_left, inner_smul_right, hv, hw, H] using (hT v w).symm
end

lemma orthogonal_family_eigenspaces' :
  @orthogonal_family 𝕜 _ _ _ _ (λ μ : eigenvalues T, eigenspace T μ) _
    (λ μ, (eigenspace T μ).subtypeₗᵢ) :=
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

section
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
show (⨆ μ : {μ // (eigenspace T μ) ≠ ⊥}, eigenspace T μ)ᗮ = ⊥,
by rw [supr_ne_bot_subtype, hT.orthogonal_supr_eigenspaces_eq_bot]

include dec_𝕜

/-- The eigenspaces of a self-adjoint operator on a finite-dimensional inner product space `E` give
an internal direct sum decomposition of `E`. -/
lemma direct_sum_submodule_is_internal :
  direct_sum.submodule_is_internal (λ μ : eigenvalues T, eigenspace T μ) :=
hT.orthogonal_family_eigenspaces'.submodule_is_internal_iff.mpr
  hT.orthogonal_supr_eigenspaces_eq_bot'

section version1

/-- Isometry from an inner product space `E` to the direct sum of the eigenspaces of some
self-adjoint operator `T` on `E`. -/
noncomputable def diagonalization : E ≃ₗᵢ[𝕜] pi_Lp 2 (λ μ : eigenvalues T, eigenspace T μ) :=
hT.direct_sum_submodule_is_internal.isometry_L2_of_orthogonal_family
  hT.orthogonal_family_eigenspaces'

@[simp] lemma diagonalization_symm_apply (w : pi_Lp 2 (λ μ : eigenvalues T, eigenspace T μ)) :
  hT.diagonalization.symm w = ∑ μ, w μ :=
hT.direct_sum_submodule_is_internal.isometry_L2_of_orthogonal_family_symm_apply
  hT.orthogonal_family_eigenspaces' w

/-- *Diagonalization theorem*, *spectral theorem*; version 1: A self-adjoint operator `T` on a
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

end version1

section version2
variables {n : ℕ} (hn : finite_dimensional.finrank 𝕜 E = n)

/-- A choice of orthonormal basis of eigenvectors for self-adjoint operator `T` on a
finite-dimensional inner product space `E`.

TODO Postcompose with a permutation so that these eigenvectors are listed in increasing order of
eigenvalue. -/
noncomputable def eigenvector_basis : basis (fin n) 𝕜 E :=
hT.direct_sum_submodule_is_internal.subordinate_orthonormal_basis hn

lemma eigenvector_basis_orthonormal : orthonormal 𝕜 (hT.eigenvector_basis hn) :=
hT.direct_sum_submodule_is_internal.subordinate_orthonormal_basis_orthonormal hn
  hT.orthogonal_family_eigenspaces'

/-- The sequence of real eigenvalues associated to the standard orthonormal basis of eigenvectors
for a self-adjoint operator `T` on `E`.

TODO Postcompose with a permutation so that these eigenvalues are listed in increasing order. -/
noncomputable def eigenvalues (i : fin n) : ℝ :=
@is_R_or_C.re 𝕜 _ $ hT.direct_sum_submodule_is_internal.subordinate_orthonormal_basis_index hn i

lemma has_eigenvector_eigenvector_basis (i : fin n) :
  has_eigenvector T (hT.eigenvalues hn i) (hT.eigenvector_basis hn i) :=
begin
  let v : E := hT.eigenvector_basis hn i,
  let μ : 𝕜 := hT.direct_sum_submodule_is_internal.subordinate_orthonormal_basis_index hn i,
  change has_eigenvector T (is_R_or_C.re μ) v,
  have key : has_eigenvector T μ v,
  { have H₁ : v ∈ eigenspace T μ,
    { exact hT.direct_sum_submodule_is_internal.subordinate_orthonormal_basis_subordinate hn i },
    have H₂ : v ≠ 0 := (hT.eigenvector_basis_orthonormal hn).ne_zero i,
    exact ⟨H₁, H₂⟩ },
  have re_μ : ↑(is_R_or_C.re μ) = μ,
  { rw ← is_R_or_C.eq_conj_iff_re,
    exact hT.conj_eigenvalue_eq_self (has_eigenvalue_of_has_eigenvector key) },
  simpa [re_μ] using key,
end

attribute [irreducible] eigenvector_basis eigenvalues

@[simp] lemma apply_eigenvector_basis (i : fin n) :
  T (hT.eigenvector_basis hn i) = (hT.eigenvalues hn i : 𝕜) • hT.eigenvector_basis hn i :=
mem_eigenspace_iff.mp (hT.has_eigenvector_eigenvector_basis hn i).1

/-- An isometry from an inner product space `E` to Euclidean space, induced by a choice of
orthonormal basis of eigenvectors for a self-adjoint operator `T` on `E`. -/
noncomputable def diagonalization_basis : E ≃ₗᵢ[𝕜] euclidean_space 𝕜 (fin n) :=
(hT.eigenvector_basis hn).isometry_euclidean_of_orthonormal (hT.eigenvector_basis_orthonormal hn)

@[simp] lemma diagonalization_basis_symm_apply (w : euclidean_space 𝕜 (fin n)) :
  (hT.diagonalization_basis hn).symm w = ∑ i, w i • hT.eigenvector_basis hn i :=
by simp [diagonalization_basis]

/-- *Diagonalization theorem*, *spectral theorem*; version 2: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the identification of `E` with
Euclidean space induced by an orthonormal basis of eigenvectors of `T`. -/
lemma diagonalization_basis_apply_self_apply (v : E) (i : fin n) :
  hT.diagonalization_basis hn (T v) i = hT.eigenvalues hn i * hT.diagonalization_basis hn v i :=
begin
  suffices : ∀ w : euclidean_space 𝕜 (fin n),
    T ((hT.diagonalization_basis hn).symm w)
    = (hT.diagonalization_basis hn).symm (λ i, hT.eigenvalues hn i * w i),
  { simpa [-diagonalization_basis_symm_apply] using
      congr_arg (λ v, hT.diagonalization_basis hn v i) (this (hT.diagonalization_basis hn v)) },
  intros w,
  simp [mul_comm, mul_smul],
end

end version2
end

/-! ### Theory for compact operators -/

variables (hT_cpct : compact_map T)
include cplt hT_cpct

/-- The mutual orthogonal complement of the eigenspaces of a compact self-adjoint operator on an
inner product space is trivial. -/
lemma orthogonal_supr_eigenspaces_eq_bot_of_compact : (⨆ μ, eigenspace T μ)ᗮ = ⊥ :=
begin
  have hT' : is_self_adjoint _ := hT.restrict_invariant hT.orthogonal_supr_eigenspaces_invariant,
  have hT_cpct' : compact_map _ :=
    hT_cpct.restrict_invariant hT.orthogonal_supr_eigenspaces_invariant sorry,
  -- a self-adjoint operator on a nontrivial inner product space has an eigenvalue
  haveI := hT'.subsingleton_of_no_eigenvalue_of_compact hT_cpct' hT.orthogonal_supr_eigenspaces,
  exact submodule.eq_bot_of_subsingleton _,
end

include dec_𝕜

lemma supr_eigenspaces_dense : (supr (eigenspace T)).topological_closure = ⊤ :=
begin
  rw ← submodule.orthogonal_orthogonal_eq_closure,
  rw submodule.orthogonal_eq_top_iff,
  exact hT.orthogonal_supr_eigenspaces_eq_bot_of_compact hT_cpct
end

/-- Isometry from a Hilbert space `E` to the Hilbert sum of the eigenspaces of some compact
self-adjoint operator `T` on `E`. -/
noncomputable def diagonalization' : E ≃ₗᵢ[𝕜] lp (λ μ, eigenspace T μ) 2 :=
hT.orthogonal_family_eigenspaces.linear_isometry_equiv begin
  convert hT.supr_eigenspaces_dense hT_cpct,
  ext i,
  simp
end

@[simp] lemma diagonalization_symm_apply' (w : lp (λ μ, eigenspace T μ) 2) :
  (hT.diagonalization' hT_cpct).symm w = ∑' μ, w μ :=
orthogonal_family.linear_isometry_equiv_symm_apply _ _ _

lemma has_sum_diagonalization_symm (w : lp (λ μ, eigenspace T μ) 2) :
  has_sum (λ μ, (w μ : E)) ((hT.diagonalization' hT_cpct).symm w) :=
orthogonal_family.has_sum_linear_isometry_equiv_symm  _ _ _

@[simp] lemma diagonalization_apply_dfinsupp_sum_single [decidable_eq E]
  (w : Π₀ μ, eigenspace T μ) :
  (hT.diagonalization' hT_cpct (w.sum (λ i v, (v : E))) : Π μ, eigenspace T μ) = w :=
begin
  have : (⨆ (i : 𝕜), (eigenspace T i).subtypeₗᵢ.to_linear_map.range).topological_closure = ⊤,
  { convert hT.supr_eigenspaces_dense hT_cpct,
    ext1 μ,
    simp },
  convert hT.orthogonal_family_eigenspaces.linear_isometry_equiv_apply_dfinsupp_sum_single this w
end

local attribute [-instance] char_p.subsingleton unique.subsingleton is_empty.subsingleton

/-- **Spectral theorem**; version 1: A compact self-adjoint operator `T` on a Hilbert space `E` acts
diagonally on the decomposition of `E` into the direct sum of the eigenspaces of `T`. -/
lemma diagonalization_apply_self_apply' (v : E) (μ : 𝕜) :
  hT.diagonalization' hT_cpct (T v) μ = (μ : 𝕜) • hT.diagonalization' hT_cpct v μ :=
begin
  classical,
  set F := (hT.diagonalization' hT_cpct).to_linear_isometry.to_linear_map,
  show F (T v) μ = μ • F v μ,
  have : dense_range (coe : supr (eigenspace T) → E),
  { simpa [dense_range_iff_closure_range] using
      congr_arg (coe : submodule 𝕜 E → set E) (supr_eigenspaces_dense hT hT_cpct) },
  refine this.induction_on v _ _,
  { -- have := continuous_linear_map.is_closed_ker
    sorry },
  { rintros ⟨w, hw⟩,
    rw submodule.mem_supr_iff_exists_dfinsupp' at hw,
    obtain ⟨W, rfl⟩ := hw,
    let eig_coe : Π μ : 𝕜, eigenspace T μ → E := λ μ, (coe : eigenspace T μ → E),
    have H : ∀ W : Π₀ ν, eigenspace T ν, F (W.sum eig_coe) μ = W μ,
    { intros W,
      rw ← hT.diagonalization_apply_dfinsupp_sum_single hT_cpct W,
      congr },
    let f : Π μ : 𝕜, eigenspace T μ →ₗ[𝕜] eigenspace T μ := λ μ, μ • linear_map.id,
    calc F (T (W.sum eig_coe)) μ
        = F (W.sum (λ μ, T ∘ (coe : eigenspace T μ → E))) μ : by simp
    ... = F (W.sum (λ μ, eig_coe μ ∘ f μ)) μ : by
    { congr,
      ext μ v,
      obtain ⟨v, hv⟩ := v,
      dsimp [f],
      rwa mem_eigenspace_iff at hv }
    ... = F ((dfinsupp.map_range.linear_map f W).sum eig_coe) μ : by
    { congr' 2,
      dsimp [eig_coe],
      rw dfinsupp.sum_map_range_index ,
      simp }
    ... = (dfinsupp.map_range.linear_map f W) μ : H _
    ... = μ • W μ : by simp
    ... = μ • F (W.sum eig_coe) μ : by rw H, }
end

end is_self_adjoint
end inner_product_space
