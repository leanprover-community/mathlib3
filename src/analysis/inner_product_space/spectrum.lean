/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Frédéric Dupuis
-/
import algebra.star.self_adjoint
import analysis.complex.polynomial
import analysis.inner_product_space.adjoint
import analysis.inner_product_space.l2_space
import analysis.inner_product_space.rayleigh
import analysis.inner_product_space.pi_L2

/-! # Spectral theory of normal and self-adjoint operators

This file covers the spectral theory of normal and self-adjoint operators on an inner product space.

The first part of the file covers general properties, true without any condition on boundedness or
compactness of the operator or finite-dimensionality of the underlying space, notably:
* `inner_product_space.is_normal.orthogonal_family_eigenspaces`: the eigenspaces are orthogonal
* `inner_product_space.is_normal.orthogonal_supr_eigenspaces`: the restriction of the operator to
  the mutual orthogonal complement of the eigenspaces has, itself, no eigenvectors
* `inner_product_space.is_self_adjoint.conj_eigenvalue_eq_self`: the eigenvalues are real

The second and third parts of the file cover, respectively, properties of normal operators over `ℂ`
in finite dimension, and properties of self-adjoint operators over `[is_R_or_C 𝕜]` in finite
dimension. Letting `T` be a normal (respectively, self-adjoint) operator on a finite-dimensional
inner product space `T`,
* The definition `is_star_normal.diagonalization` (resp. `self_adjoint.diagonalization`) provides a
  linear isometry equivalence from `E` to the direct sum of the eigenspaces of `T`.  The theorem
  `is_star_normal.diagonalization_apply_self_apply` (resp.
  `self_adjoint.diagonalization_apply_self_apply`) states that, when `T` is transferred via this
  equivalence to an operator on the direct sum, it acts diagonally.
* The definition `is_star_normal.eigenvector_basis` (resp. `self_adjoint.eigenvector_basis`)
  provides an orthonormal basis for `E` consisting of eigenvectors of `T`, with
  `is_star_normal.eigenvalues` (resp. `self_adjoint.eigenvalues`) giving the corresponding
  list of eigenvalues, as complex (resp. real) numbers.  The definition
  `is_star_normal.diagonalization_basis` (resp. `self_adjoint.diagonalization_basis`) gives the
  associated linear isometry equivalence from `E` to Euclidean space, and the theorem
  `is_star_normal.diagonalization_basis_apply_self_apply` (resp.
  `self_adjoint.diagonalization_basis_apply_self_apply`) states that, when `T` is transferred via
  this equivalence to an operator on Euclidean space, it acts diagonally.

The fourth part of the file covers properties of compact self-adjoint operators over `[is_R_or_C 𝕜]`
on Hilbert spaces in possibly infinite dimension. Letting `T` be a self-adjoint operator on a
Hilbert space `T`,
* The definition `self_adjoint.diagonalization'` provides a
  linear isometry equivalence from `E` to the Hilbert sum of the eigenspaces of `T`.  The theorem
  `self_adjoint.diagonalization_apply_self_apply'` states that, when `T` is transferred via this
  equivalence to an operator on the Hilbert sum, it acts diagonally.

These are forms of the **spectral theorem**/**diagonalization theorem** for self-adjoint/normal
operators on Hilbert spaces.

## TODO

Spectral theory for compact normal operators, bounded normal/self-adjoint operators.

## Tags

self-adjoint operator, normal operator, spectral theorem, diagonalization theorem

-/

variables {𝕜 : Type*} [is_R_or_C 𝕜] [dec_𝕜 : decidable_eq 𝕜]
variables {E : Type*} [inner_product_space 𝕜 E]
variables {F : Type*} [inner_product_space ℂ F]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y
local postfix `†`:std.prec.max_plus := linear_map.adjoint

open_locale big_operators complex_conjugate
open module.End inner_product_space

-- move this to general eigentheory file
lemma subsingleton_of_no_eigenvalue_finite_dimensional {K : Type*} [field K] [is_alg_closed K]
  {V : Type*} [add_comm_group V] [module K V] [finite_dimensional K V] (T : module.End K V)
  (hT' : ∀ μ : K, T.eigenspace μ = ⊥) :
  subsingleton V :=
(subsingleton_or_nontrivial V).resolve_right
  (λ h, by exactI absurd (hT' _) (classical.some_spec $ exists_eigenvalue T))

-- move this
instance [complete_space E] {T : E →L[𝕜] E} (μ : 𝕜) :
  complete_space (eigenspace (T : E →ₗ[𝕜] E) μ) :=
(T - μ • continuous_linear_map.id 𝕜 E).is_closed_ker.complete_space_coe

-- typeclass inference can't find this unassisted
-- move this
noncomputable instance pi_Lp_submodule.normed_space {ι : Type*} [fintype ι] {E : Type*}
  [normed_group E] [normed_space 𝕜 E] (K : ι → submodule 𝕜 E) :
  normed_space 𝕜 (pi_Lp 2 (λ i, K i)) :=
@pi_Lp.normed_space ι 2 _ (λ i, K i) _ 𝕜 _ _ (λ i, (K i).normed_space)

-- typeclass inference can't find this unassisted
-- move this
noncomputable instance lp_submodule.normed_space {ι : Type*} {E : Type*} [normed_group E]
  [normed_space 𝕜 E] (K : ι → submodule 𝕜 E) :
  normed_space 𝕜 (lp (λ i, K i) 2) :=
@lp.normed_space ι (λ i, K i) 2 _ 𝕜 _ (λ i, (K i).normed_space) _

namespace inner_product_space

namespace is_normal

variables {T : E →ₗ[𝕜] E} (hT : is_normal T)
include hT

lemma adjoint_apply_mem_eigenspace_of_mem_eigenspace (μ : 𝕜) (v : E) (hv : v ∈ eigenspace T μ) :
  hT.adjoint v ∈ eigenspace T μ :=
mem_eigenspace_iff.mpr $
calc _ = (T * hT.adjoint) v     : linear_map.mul_apply T hT.adjoint v
    ... = (hT.adjoint * T) v    : by rw [hT.adjoint_comm_self]
    ... = hT.adjoint (T v)      : linear_map.mul_apply hT.adjoint T v
    ... = hT.adjoint (μ • v)    : by rw [mem_eigenspace_iff.mp hv]
    ... = μ • (hT.adjoint v)    : by simp only [ring_hom.id_apply, linear_map.map_smulₛₗ]

/-- An eigenvector of a normal operator is also an eigenvector of its adjoint. -/
lemma mem_eigenspace_adjoint (μ : 𝕜) (v : E) (hv : v ∈ eigenspace T μ) :
  v ∈ eigenspace hT.adjoint (conj μ) :=
begin
  rw [mem_eigenspace_iff],
  let v' : eigenspace T μ := ⟨v, hv⟩,
  let Tdagv' : eigenspace T μ := ⟨hT.adjoint v,
                                  adjoint_apply_mem_eigenspace_of_mem_eigenspace hT μ v hv⟩,
  have : Tdagv' = (conj μ) • v',
  { refine ext_inner_left 𝕜 (λ w, _),
    dsimp [inner],
    rw [hT.adjoint_inner_right, mem_eigenspace_iff.mp w.prop, inner_smul_left,
        inner_smul_right] },
  rwa subtype.ext_iff_val at this,
end

/-- A normal operator preserves orthogonal complements of its eigenspaces. -/
lemma invariant_orthogonal_eigenspace (μ : 𝕜) (v : E) (hv : v ∈ (eigenspace T μ)ᗮ) :
  T v ∈ (eigenspace T μ)ᗮ :=
λ w hw, by rw [←hT.adjoint_inner_left,
               hv (hT.adjoint w) (adjoint_apply_mem_eigenspace_of_mem_eigenspace hT μ w hw)]

/-- The eigenspaces of a normal operator are mutually orthogonal. -/
lemma orthogonal_family_eigenspaces :
  @orthogonal_family 𝕜 _ _ _ _ (λ μ, eigenspace T μ) _ (λ μ, (eigenspace T μ).subtypeₗᵢ) :=
begin
  rintros μ ν hμν ⟨v, hv⟩ ⟨w, hw⟩,
  by_cases hv' : v = 0,
  { simp [hv'] },
  rw mem_eigenspace_iff at hw,
  have hv' := mem_eigenspace_adjoint hT μ v hv,
  rw mem_eigenspace_iff at hv',
  refine or.resolve_left _ hμν.symm,
  have h₁ : ⟪v, T w⟫ = ν * ⟪v, w⟫ := by rw [hw, inner_smul_right],
  have h₂ : ⟪v, T w⟫ = μ * ⟪v, w⟫ := by rw [←hT.adjoint_inner_left, hv', inner_smul_left,
                                            is_R_or_C.conj_conj],
  rw [h₁] at h₂,
  exact mul_eq_mul_right_iff.mp h₂,
end

lemma orthogonal_family_eigenspaces' :
  @orthogonal_family 𝕜 _ _ _ _ (λ μ : eigenvalues T, eigenspace T μ) _
    (λ μ, (eigenspace T μ).subtypeₗᵢ) :=
(orthogonal_family_eigenspaces hT).comp subtype.coe_injective

/-- The mutual orthogonal complement of the eigenspaces of a normal operator on an inner
product space is an invariant subspace of the operator. -/
lemma orthogonal_supr_eigenspaces_invariant ⦃v : E⦄ (hv : v ∈ (⨆ μ, eigenspace T μ)ᗮ) :
  T v ∈ (⨆ μ, eigenspace T μ)ᗮ :=
begin
  rw ← submodule.infi_orthogonal at ⊢ hv,
  exact T.infi_invariant (invariant_orthogonal_eigenspace hT) v hv
end

/-- The mutual orthogonal complement of the eigenspaces of a normal operator on an inner
product space has no eigenvalues. -/
lemma orthogonal_supr_eigenspaces (μ : 𝕜) :
  eigenspace (T.restrict (orthogonal_supr_eigenspaces_invariant hT)) μ = ⊥ :=
begin
  set p : submodule 𝕜 E := (⨆ μ, eigenspace T μ)ᗮ,
  refine eigenspace_restrict_eq_bot (orthogonal_supr_eigenspaces_invariant hT) _,
  have H₂ : p ≤ (eigenspace T μ)ᗮ := submodule.orthogonal_le (le_supr _ _),
  exact (eigenspace T μ).orthogonal_disjoint.mono_right H₂
end

end is_normal

namespace is_self_adjoint

/-- The eigenvalues of a self-adjoint operator are real. -/
lemma conj_eigenvalue_eq_self {T : E →ₗ[𝕜] E} (hT : is_self_adjoint T) {μ : 𝕜}
  (hμ : has_eigenvalue T μ) :
  conj μ = μ :=
begin
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_has_eigenvector,
  rw mem_eigenspace_iff at hv₁,
  simpa [hv₂, inner_smul_left, inner_smul_right, hv₁] using hT v v
end

end is_self_adjoint

end inner_product_space

namespace is_star_normal

/-! ### Finite-dimensional theory for normal operators -/

variables [finite_dimensional ℂ F] {T : F →ₗ[ℂ] F} (hT : is_star_normal T)
include hT

/-- The mutual orthogonal complement of the eigenspaces of a normal operator on a
finite-dimensional inner product space is trivial. -/
lemma orthogonal_supr_eigenspaces_eq_bot : (⨆ μ, eigenspace T μ)ᗮ = ⊥ :=
begin
  let T' := T.restrict hT.is_normal.orthogonal_supr_eigenspaces_invariant,
  -- an operator on a nontrivial inner product space has an eigenvalue
  haveI := (subsingleton_of_no_eigenvalue_finite_dimensional T')
    hT.is_normal.orthogonal_supr_eigenspaces,
  exact submodule.eq_bot_of_subsingleton _,
end

lemma orthogonal_supr_eigenspaces_eq_bot' : (⨆ μ : eigenvalues T, eigenspace T μ)ᗮ = ⊥ :=
show (⨆ μ : {μ // (eigenspace T μ) ≠ ⊥}, eigenspace T μ)ᗮ = ⊥,
by rw [supr_ne_bot_subtype, orthogonal_supr_eigenspaces_eq_bot hT]

/-- The eigenspaces of a normal operator on a finite-dimensional inner product space `F` give
an internal direct sum decomposition of `F`. -/
lemma direct_sum_submodule_is_internal [decidable_eq (eigenvalues T)] :
  direct_sum.submodule_is_internal (λ μ : eigenvalues T, eigenspace T μ) :=
hT.is_normal.orthogonal_family_eigenspaces'.submodule_is_internal_iff.mpr
  hT.orthogonal_supr_eigenspaces_eq_bot'

section version1

variable [decidable_eq (eigenvalues T)]

/-- Isometry from an inner product space `F` to the direct sum of the eigenspaces of some
normal operator `T` on `F`. -/
noncomputable def diagonalization :
  F ≃ₗᵢ[ℂ] pi_Lp 2 (λ μ : eigenvalues T, eigenspace T μ) :=
hT.direct_sum_submodule_is_internal.isometry_L2_of_orthogonal_family
  hT.is_normal.orthogonal_family_eigenspaces'

@[simp] lemma diagonalization_symm_apply  (w : pi_Lp 2 (λ μ : eigenvalues T, eigenspace T μ)) :
  (diagonalization hT).symm w = ∑ μ, w μ :=
hT.direct_sum_submodule_is_internal.isometry_L2_of_orthogonal_family_symm_apply
  hT.is_normal.orthogonal_family_eigenspaces' w

/-- **Diagonalization theorem**, **spectral theorem**; version 1: A normal operator `T` on a
finite-dimensional inner product space `F` acts diagonally on the decomposition of `F` into the
direct sum of the eigenspaces of `T`. -/
lemma diagonalization_apply_self_apply (v : F) (μ : eigenvalues T) :
  hT.diagonalization (T v) μ = (μ : ℂ) • hT.diagonalization v μ :=
begin
  suffices : ∀ w : pi_Lp 2 (λ μ : eigenvalues T, eigenspace T μ),
    (T ((diagonalization hT).symm w)) = (diagonalization hT).symm (λ μ, (μ : ℂ) • w μ),
  { simpa [linear_isometry_equiv.symm_apply_apply, -diagonalization_symm_apply]
      using congr_arg (λ w, hT.diagonalization w μ) (this (hT.diagonalization v)) },
  intros w,
  have hwT : ∀ μ : eigenvalues T, T (w μ) = (μ : ℂ) • w μ,
  { intros μ,
    simpa [mem_eigenspace_iff] using (w μ).prop },
  simp [hwT],
end

end version1

section version2
variables {n : ℕ} (hn : finite_dimensional.finrank ℂ F = n) [decidable_eq (eigenvalues T)]

/-- A choice of orthonormal basis of eigenvectors for normal operator `T` on a
finite-dimensional inner product space `E`. -/
noncomputable def eigenvector_basis : basis (fin n) ℂ F :=
hT.direct_sum_submodule_is_internal.subordinate_orthonormal_basis hn

lemma eigenvector_basis_orthonormal : orthonormal ℂ (eigenvector_basis hT hn) :=
hT.direct_sum_submodule_is_internal.subordinate_orthonormal_basis_orthonormal hn
  hT.is_normal.orthogonal_family_eigenspaces'

/-- The sequence of eigenvalues associated to the standard orthonormal basis of eigenvectors
for a normal operator `T` on `E`. -/
noncomputable def eigenvalues (i : fin n) : ℂ :=
hT.direct_sum_submodule_is_internal.subordinate_orthonormal_basis_index hn i

lemma has_eigenvector_eigenvector_basis (i : fin n) :
  has_eigenvector T (hT.eigenvalues hn i) (hT.eigenvector_basis hn i) :=
begin
  let v : F := eigenvector_basis hT hn i,
  let μ : ℂ := (direct_sum_submodule_is_internal hT).subordinate_orthonormal_basis_index hn i,
  change has_eigenvector T μ v,
  have H₁ : v ∈ eigenspace T μ,
  { exact (direct_sum_submodule_is_internal hT).subordinate_orthonormal_basis_subordinate hn i },
  have H₂ : v ≠ 0 := ((eigenvector_basis_orthonormal hT) hn).ne_zero i,
  exact ⟨H₁, H₂⟩,
end

attribute [irreducible] eigenvector_basis eigenvalues

@[simp] lemma apply_eigenvector_basis (i : fin n) :
  T (hT.eigenvector_basis hn i) = (hT.eigenvalues hn i : ℂ) • hT.eigenvector_basis hn i :=
mem_eigenspace_iff.mp (has_eigenvector_eigenvector_basis hT hn i).1

/-- An isometry from an inner product space `F` to Euclidean space, induced by a choice of
orthonormal basis of eigenvectors for a normal operator `T` on `F`. -/
noncomputable def diagonalization_basis : F ≃ₗᵢ[ℂ] euclidean_space ℂ (fin n) :=
(hT.eigenvector_basis hn).isometry_euclidean_of_orthonormal (hT.eigenvector_basis_orthonormal hn)

@[simp] lemma diagonalization_basis_symm_apply (w : euclidean_space ℂ (fin n)) :
  (hT.diagonalization_basis hn).symm w = ∑ i, w i • hT.eigenvector_basis hn i :=
by simp [diagonalization_basis]

/-- **Diagonalization theorem**, **spectral theorem**; version 2: A normal operator `T` on a
finite-dimensional inner product space `F` acts diagonally on the identification of `F` with
Euclidean space induced by an orthonormal basis of eigenvectors of `T`. -/
lemma diagonalization_basis_apply_self_apply (v : F) (i : fin n) :
  hT.diagonalization_basis hn (T v) i = eigenvalues hT hn i * hT.diagonalization_basis hn v i :=
begin
  suffices : ∀ w : euclidean_space ℂ (fin n),
    T ((diagonalization_basis hT hn).symm w)
    = (diagonalization_basis hT hn).symm (λ i, eigenvalues hT hn i * w i),
  { simpa [-diagonalization_basis_symm_apply] using
      congr_arg (λ v, diagonalization_basis hT hn v i) (this (diagonalization_basis hT hn v)) },
  intros w,
  simp [mul_comm, mul_smul],
end

end version2

end is_star_normal

namespace self_adjoint

/-! ### Finite-dimensional theory for self-adjoint operators -/

variables [finite_dimensional 𝕜 E]
variables {T : E →ₗ[𝕜] E} (hT : T ∈ self_adjoint (E →ₗ[𝕜] E))
include hT

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on a
finite-dimensional inner product space is trivial. -/
lemma orthogonal_supr_eigenspaces_eq_bot : (⨆ μ, eigenspace T μ)ᗮ = ⊥ :=
begin
  have hT' : is_self_adjoint T := T.mem_self_adjoint_iff_is_self_adjoint.mp hT,
  have hT'' : is_self_adjoint _ := hT'.restrict_invariant
    hT'.is_normal.orthogonal_supr_eigenspaces_invariant,
  -- a self-adjoint operator on a nontrivial inner product space has an eigenvalue
  haveI := hT''.subsingleton_of_no_eigenvalue_finite_dimensional
    hT'.is_normal.orthogonal_supr_eigenspaces,
  exact submodule.eq_bot_of_subsingleton _,
end

lemma orthogonal_supr_eigenspaces_eq_bot' : (⨆ μ : eigenvalues T, eigenspace T μ)ᗮ = ⊥ :=
show (⨆ μ : {μ // (eigenspace T μ) ≠ ⊥}, eigenspace T μ)ᗮ = ⊥,
by rw [supr_ne_bot_subtype, orthogonal_supr_eigenspaces_eq_bot hT]

include dec_𝕜

/-- The eigenspaces of a self-adjoint operator on a finite-dimensional inner product space `E` give
an internal direct sum decomposition of `E`. -/
lemma direct_sum_submodule_is_internal :
  direct_sum.submodule_is_internal (λ μ : eigenvalues T, eigenspace T μ) :=
(linear_map.is_normal_of_mem_self_adjoint
  hT).orthogonal_family_eigenspaces'.submodule_is_internal_iff.mpr
  (orthogonal_supr_eigenspaces_eq_bot' hT)

section version1

/-- Isometry from an inner product space `E` to the direct sum of the eigenspaces of some
self-adjoint operator `T` on `E`. -/
noncomputable def diagonalization : E ≃ₗᵢ[𝕜] pi_Lp 2 (λ μ : eigenvalues T, eigenspace T μ) :=
(direct_sum_submodule_is_internal hT).isometry_L2_of_orthogonal_family
  (linear_map.is_normal_of_mem_self_adjoint hT).orthogonal_family_eigenspaces'

@[simp] lemma diagonalization_symm_apply (w : pi_Lp 2 (λ μ : eigenvalues T, eigenspace T μ)) :
  (diagonalization hT).symm w = ∑ μ, w μ :=
(direct_sum_submodule_is_internal hT).isometry_L2_of_orthogonal_family_symm_apply
  (linear_map.is_normal_of_mem_self_adjoint hT).orthogonal_family_eigenspaces' w

/-- **Diagonalization theorem**, **spectral theorem**; version 1: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the decomposition of `E` into the
direct sum of the eigenspaces of `T`. -/
lemma diagonalization_apply_self_apply (v : E) (μ : eigenvalues T) :
  diagonalization hT (T v) μ = (μ : 𝕜) • diagonalization hT v μ :=
begin
  suffices : ∀ w : pi_Lp 2 (λ μ : eigenvalues T, eigenspace T μ),
    (T ((diagonalization hT).symm w)) = (diagonalization hT).symm (λ μ, (μ : 𝕜) • w μ),
  { simpa only [linear_isometry_equiv.symm_apply_apply, linear_isometry_equiv.apply_symm_apply]
      using congr_arg (λ w, diagonalization hT w μ) (this (diagonalization hT v)) },
  intros w,
  have hwT : ∀ μ : eigenvalues T, T (w μ) = (μ : 𝕜) • w μ,
  { intros μ,
    simpa only [mem_eigenspace_iff] using subtype.prop (w μ) },
  simp only [hwT, diagonalization_symm_apply, linear_map.map_sum, submodule.coe_smul_of_tower],
end

end version1

section version2
variables {n : ℕ} (hn : finite_dimensional.finrank 𝕜 E = n)

/-- A choice of orthonormal basis of eigenvectors for self-adjoint operator `T` on a
finite-dimensional inner product space `E`.

TODO Postcompose with a permutation so that these eigenvectors are listed in increasing order of
eigenvalue. -/
noncomputable def eigenvector_basis : basis (fin n) 𝕜 E :=
(direct_sum_submodule_is_internal hT).subordinate_orthonormal_basis hn

lemma eigenvector_basis_orthonormal : orthonormal 𝕜 (eigenvector_basis hT hn) :=
(direct_sum_submodule_is_internal hT).subordinate_orthonormal_basis_orthonormal hn
  (linear_map.is_normal_of_mem_self_adjoint hT).orthogonal_family_eigenspaces'

/-- The sequence of real eigenvalues associated to the standard orthonormal basis of eigenvectors
for a self-adjoint operator `T` on `E`.

TODO Postcompose with a permutation so that these eigenvalues are listed in increasing order. -/
noncomputable def eigenvalues (i : fin n) : ℝ :=
@is_R_or_C.re 𝕜 _ $ (direct_sum_submodule_is_internal hT).subordinate_orthonormal_basis_index hn i

lemma has_eigenvector_eigenvector_basis (i : fin n) :
  has_eigenvector T (eigenvalues hT hn i) (eigenvector_basis hT hn i) :=
begin
  let v : E := eigenvector_basis hT hn i,
  let μ : 𝕜 := (direct_sum_submodule_is_internal hT).subordinate_orthonormal_basis_index hn i,
  change has_eigenvector T (is_R_or_C.re μ) v,
  have key : has_eigenvector T μ v,
  { have H₁ : v ∈ eigenspace T μ,
    { exact (direct_sum_submodule_is_internal hT).subordinate_orthonormal_basis_subordinate hn i },
    have H₂ : v ≠ 0 := (eigenvector_basis_orthonormal hT hn).ne_zero i,
    exact ⟨H₁, H₂⟩ },
  have re_μ : ↑(is_R_or_C.re μ) = μ,
  { rw ← is_R_or_C.eq_conj_iff_re,
    exact (T.mem_self_adjoint_iff_is_self_adjoint.mp hT).conj_eigenvalue_eq_self
      (has_eigenvalue_of_has_eigenvector key) },
  simpa [re_μ] using key,
end

lemma has_eigenvalue_eigenvalues (i : fin n) : has_eigenvalue T (hT.eigenvalues hn i) :=
    module.End.has_eigenvalue_of_has_eigenvector (hT.has_eigenvector_eigenvector_basis hn i)

attribute [irreducible] eigenvector_basis eigenvalues

@[simp] lemma apply_eigenvector_basis (i : fin n) :
  T (eigenvector_basis hT hn i) = (eigenvalues hT hn i : 𝕜) • eigenvector_basis hT hn i :=
mem_eigenspace_iff.mp (has_eigenvector_eigenvector_basis hT hn i).1

/-- An isometry from an inner product space `E` to Euclidean space, induced by a choice of
orthonormal basis of eigenvectors for a self-adjoint operator `T` on `E`. -/
noncomputable def diagonalization_basis : E ≃ₗᵢ[𝕜] euclidean_space 𝕜 (fin n) :=
(eigenvector_basis hT hn).isometry_euclidean_of_orthonormal (eigenvector_basis_orthonormal hT hn)

@[simp] lemma diagonalization_basis_symm_apply (w : euclidean_space 𝕜 (fin n)) :
  (diagonalization_basis hT hn).symm w = ∑ i, w i • eigenvector_basis hT hn i :=
by simp [diagonalization_basis]

/-- **Diagonalization theorem**, **spectral theorem**; version 2: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the identification of `E` with
Euclidean space induced by an orthonormal basis of eigenvectors of `T`. -/
lemma diagonalization_basis_apply_self_apply (v : E) (i : fin n) :
  diagonalization_basis hT hn (T v) i = eigenvalues hT hn i * diagonalization_basis hT hn v i :=
begin
  suffices : ∀ w : euclidean_space 𝕜 (fin n),
    T ((diagonalization_basis hT hn).symm w)
    = (diagonalization_basis hT hn).symm (λ i, eigenvalues hT hn i * w i),
  { simpa only [linear_isometry_equiv.symm_apply_apply, linear_isometry_equiv.apply_symm_apply]
    using congr_arg (λ v, diagonalization_basis hT hn v i) (this (diagonalization_basis hT hn v)) },
  intros w,
  simp only [mul_comm, mul_smul, diagonalization_basis_symm_apply, linear_map.map_sum,
    linear_map.map_smulₛₗ, ring_hom.id_apply, apply_eigenvector_basis],
end

end version2

end self_adjoint

namespace self_adjoint

/-! ### Theory for compact operators -/

-- note: A compact operator is automatically continuous, i.e. of the form `E →L[𝕜] E`.  In this
-- section we use some facts about continuous linear operators, so we represent `T` as `E →L[𝕜] E`.
-- Is it better to do it this way or to keep `T` of the type `E →ₗ[𝕜] E` and re-prove those facts?
variables [cplt : complete_space E] {T : E →L[𝕜] E} (hT : T ∈ self_adjoint (E →L[𝕜] E))
  (hT_cpct : compact_map T)

-- move this
/-- Restrict domain and codomain of a continuous endomorphism. -/
def _root_.continuous_linear_map.restrict {R : Type*} {M : Type*} [semiring R] [add_comm_monoid M]
  [topological_space M]
  [module R M] (f : M →L[R] M) {p : submodule R M} (hf : ∀ (x : M), x ∈ p → f x ∈ p) :
  ↥p →L[R] ↥p :=
{ cont := begin
    apply continuous_induced_rng,
    exact f.continuous.comp continuous_induced_dom,
  end,
  .. linear_map.restrict (f : M →ₗ[R] M) hf }


include hT hT_cpct cplt

/-- The mutual orthogonal complement of the eigenspaces of a compact self-adjoint operator on an
inner product space is trivial. -/
lemma orthogonal_supr_eigenspaces_eq_bot_of_compact : (⨆ μ, eigenspace (T : E →ₗ[𝕜] E) μ)ᗮ = ⊥ :=
begin
  have hT' : is_self_adjoint (T : E →ₗ[𝕜] E) := T.mem_self_adjoint_iff_is_self_adjoint.mp hT,
  have hT'' : is_self_adjoint (↑(T.restrict hT'.is_normal.orthogonal_supr_eigenspaces_invariant)),
  { convert hT'.restrict_invariant hT'.is_normal.orthogonal_supr_eigenspaces_invariant },
  have hT_cpct' : compact_map _ :=
    hT_cpct.restrict_invariant' hT'.is_normal.orthogonal_supr_eigenspaces_invariant,
  -- a compact self-adjoint operator on a nontrivial inner product space has an eigenvalue
  haveI := hT''.subsingleton_of_no_eigenvalue_of_compact hT_cpct'
    hT'.is_normal.orthogonal_supr_eigenspaces,
  exact submodule.eq_bot_of_subsingleton _,
end

lemma supr_eigenspaces_dense : (supr (eigenspace (T : E →ₗ[𝕜] E))).topological_closure = ⊤ :=
begin
  rw ← submodule.orthogonal_orthogonal_eq_closure,
  rw submodule.orthogonal_eq_top_iff,
  exact orthogonal_supr_eigenspaces_eq_bot_of_compact hT hT_cpct
end

/-- Isometry from a Hilbert space `E` to the Hilbert sum of the eigenspaces of some compact
self-adjoint operator `T` on `E`. -/
noncomputable def diagonalization' :
  E ≃ₗᵢ[𝕜] (lp (λ μ, eigenspace (T : E →ₗ[𝕜] E) μ) 2) :=
(continuous_linear_map.is_normal_of_mem_self_adjoint
  hT).orthogonal_family_eigenspaces.linear_isometry_equiv
  begin
    convert supr_eigenspaces_dense hT hT_cpct,
    ext i,
    simp
  end

@[simp] lemma diagonalization_symm_apply' (w : lp (λ μ, eigenspace (T : E →ₗ[𝕜] E) μ) 2) :
  (diagonalization' hT hT_cpct).symm w = ∑' μ, w μ :=
orthogonal_family.linear_isometry_equiv_symm_apply _ _ _

lemma has_sum_diagonalization_symm (w : lp (λ μ, eigenspace (T : E →ₗ[𝕜] E) μ) 2) :
  has_sum (λ μ, (w μ : E)) ((diagonalization' hT hT_cpct).symm w) :=
orthogonal_family.has_sum_linear_isometry_equiv_symm  _ _ _

include dec_𝕜

@[simp] lemma diagonalization_apply_dfinsupp_sum_single [decidable_eq E]
  (w : Π₀ μ, eigenspace (T : E →ₗ[𝕜] E) μ) :
  (diagonalization' hT hT_cpct (w.sum (λ i v, (v : E))) : Π μ, eigenspace (T : E →ₗ[𝕜] E) μ) = w :=
begin
  have :
    (⨆ (i : 𝕜), (eigenspace (T : E →ₗ[𝕜] E) i).subtypeₗᵢ.to_linear_map.range).topological_closure
    = ⊤,
  { convert supr_eigenspaces_dense hT hT_cpct,
    ext1 μ,
    simp },
  convert (continuous_linear_map.is_normal_of_mem_self_adjoint
    hT).orthogonal_family_eigenspaces.linear_isometry_equiv_apply_dfinsupp_sum_single this w
end

omit dec_𝕜

/-- **Spectral theorem**: A compact self-adjoint operator `T` on a Hilbert space `E`
acts diagonally on the decomposition of `E` into the Hilbert sum of the eigenspaces of `T`. -/
lemma diagonalization_apply_self_apply' (v : E) (μ : 𝕜) :
  diagonalization' hT hT_cpct (T v) μ = (μ : 𝕜) • diagonalization' hT hT_cpct v μ :=
begin
  classical,
  set F := (diagonalization' hT hT_cpct).to_linear_isometry.to_linear_map,
  show F (T v) μ = μ • F v μ,
  have : dense_range (coe : supr (eigenspace (T : E →ₗ[𝕜] E)) → E),
  { simpa only [dense_range_iff_closure_range, subtype.range_coe_subtype]
    using congr_arg coe (supr_eigenspaces_dense hT hT_cpct)   },
  refine this.induction_on v _ _,
  { -- The set of vectors `v : E` at which the desired property holds is a closed subset of `E`
    let φ : E →L[𝕜] lp (λ μ, eigenspace (T : E →ₗ[𝕜] E) μ) 2 :=
      ↑(diagonalization' hT hT_cpct) ∘L (T - μ • continuous_linear_map.id 𝕜 E),
    let P := @lp.proj 𝕜 (λ μ, eigenspace (T : E →ₗ[𝕜] E) μ) 2 _ 𝕜 _
      (λ i, submodule.normed_space _) _ μ,
    convert (P.comp φ).is_closed_ker using 1,
    ext v,
    rw [set_like.mem_coe, set.mem_set_of_eq, ← sub_eq_zero, continuous_linear_map.mem_ker],
    refine eq.congr _ rfl,
    simp only [continuous_linear_map.coe_comp', continuous_linear_map.coe_id',
      continuous_linear_map.coe_smul', continuous_linear_map.coe_sub',
      continuous_linear_map.comp_apply, eq_self_iff_true, function.comp_app, id.def,
      linear_isometry.coe_to_linear_map, linear_isometry_equiv.coe_coe'',
      linear_isometry_equiv.coe_to_linear_isometry, linear_isometry_equiv.map_smul,
      linear_isometry_equiv.map_sub, lp.coe_fn_smul, lp.coe_fn_sub, lp.proj_apply, pi.smul_apply,
      pi.sub_apply, sub_left_inj, φ] },
  { -- We prove the desired property holds for finite sums of eigenvectors, which form a dense
    -- subset of `E`
    rintros ⟨w, hw⟩,
    rw submodule.mem_supr_iff_exists_dfinsupp' at hw,
    obtain ⟨W, rfl⟩ := hw,
    let eig_coe : Π μ : 𝕜, eigenspace (T : E →ₗ[𝕜] E) μ → E := λ μ, (coe : _ → E),
    have H : ∀ W : Π₀ ν, eigenspace (T : E →ₗ[𝕜] E) ν, F (W.sum eig_coe) μ = W μ,
    { intros W,
      rw ← diagonalization_apply_dfinsupp_sum_single hT hT_cpct W,
      congr },
    let f : Π μ : 𝕜, eigenspace (T : E →ₗ[𝕜] E) μ →ₗ[𝕜] _ := λ μ, μ • linear_map.id,
    calc F ((T : E →ₗ[𝕜] E) (W.sum eig_coe)) μ
        = F (W.sum (λ μ, (T : E →ₗ[𝕜] E) ∘ (coe : _ → E))) μ : by
    { congr,
      rw linear_map.map_dfinsupp_sum }
    ... = F (W.sum (λ μ, eig_coe μ ∘ f μ)) μ : by
    { congr,
      ext μ v,
      obtain ⟨v, hv⟩ := v,
      dsimp [f],
      rwa mem_eigenspace_iff at hv }
    ... = F ((dfinsupp.map_range.linear_map f W).sum eig_coe) μ : by
    { congr' 2,
      dsimp [eig_coe],
      rw dfinsupp.sum_map_range_index,
      simp only [submodule.coe_zero, forall_const] }
    ... = (dfinsupp.map_range.linear_map f W) μ : H _
    ... = μ • W μ : by simp
    ... = μ • F (W.sum eig_coe) μ : by rw H, }
end

end self_adjoint
end is_self_adjoint
end inner_product_space

section nonneg

@[simp]
lemma inner_product_apply_eigenvector {μ : 𝕜} {v : E} {T : E →ₗ[𝕜] E}
  (h : v ∈ module.End.eigenspace T μ) : ⟪v, T v⟫ = μ * ∥v∥ ^ 2 :=
by simp only [mem_eigenspace_iff.mp h, inner_smul_right, inner_self_eq_norm_sq_to_K]

lemma eigenvalue_nonneg_of_nonneg {μ : ℝ} {T : E →ₗ[𝕜] E} (hμ : has_eigenvalue T μ)
  (hnn : ∀ (x : E), 0 ≤ is_R_or_C.re ⟪x, T x⟫) : 0 ≤ μ :=
begin
  obtain ⟨v, hv⟩ := hμ.exists_has_eigenvector,
  have hpos : 0 < ∥v∥ ^ 2, by simpa only [sq_pos_iff, norm_ne_zero_iff] using hv.2,
  have : is_R_or_C.re ⟪v, T v⟫ = μ * ∥v∥ ^ 2,
  { exact_mod_cast congr_arg is_R_or_C.re (inner_product_apply_eigenvector hv.1) },
  exact (zero_le_mul_right hpos).mp (this ▸ hnn v),
end

lemma eigenvalue_pos_of_pos {μ : ℝ} {T : E →ₗ[𝕜] E} (hμ : has_eigenvalue T μ)
  (hnn : ∀ (x : E), 0 < is_R_or_C.re ⟪x, T x⟫) : 0 < μ :=
begin
  obtain ⟨v, hv⟩ := hμ.exists_has_eigenvector,
  have hpos : 0 < ∥v∥ ^ 2, by simpa only [sq_pos_iff, norm_ne_zero_iff] using hv.2,
  have : is_R_or_C.re ⟪v, T v⟫ = μ * ∥v∥ ^ 2,
  { exact_mod_cast congr_arg is_R_or_C.re (inner_product_apply_eigenvector hv.1) },
  exact (zero_lt_mul_right hpos).mp (this ▸ hnn v),
end

end nonneg
