/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.inner_product_space.adjoint
import analysis.inner_product_space.spectrum

/-!
# Positive operators

In this file we define positive operators in a Hilbert space. We follow Bourbaki's choice
of requiring self adjointness in the definition.

## Main definitions

for linear maps:
* `is_positive` : a linear map is positive if it is symmetric and `∀ x, 0 ≤ re ⟪T x, x⟫`

for continuous linear maps:
* `is_positive` : a continuous linear map is positive if it is self adjoint and
  `∀ x, 0 ≤ re ⟪T x, x⟫`

## Main statements

for linear maps:
* `linear_map.is_positive.conj_adjoint` : if `T : E →ₗ[𝕜] E` and `E` is a finite-dimensional space,
  then for any `S : E →ₗ[𝕜] F`, we have `S.comp (T.comp S.adjoint)` is also positive.

for continuous linear maps:
* `continuous_linear_map.is_positive.conj_adjoint` : if `T : E →L[𝕜] E` is positive,
  then for any `S : E →L[𝕜] F`, `S ∘L T ∘L S†` is also positive.
* `continuous_linear_map.is_positive_iff_complex` : in a ***complex*** hilbert space,
  checking that `⟪T x, x⟫` is a nonnegative real number for all `x` suffices to prove that
  `T` is positive

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

Positive operator
-/
open inner_product_space is_R_or_C
open_locale inner_product complex_conjugate

variables {𝕜 E F : Type*} [is_R_or_C 𝕜]
  [normed_add_comm_group E] [normed_add_comm_group F]
  [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

namespace linear_map

/-- `T` is (semi-definite) **positive** if `T` is symmetric
and `∀ x : V, 0 ≤ re ⟪T x, x⟫` -/
def is_positive (T : E →ₗ[𝕜] E) : Prop :=
T.is_symmetric ∧ ∀ x : E, 0 ≤ re ⟪T x, x⟫

protected lemma is_positive.is_symmetric {T : E →ₗ[𝕜] E} (hT : is_positive T) :
  T.is_symmetric :=
hT.1

lemma is_positive.inner_nonneg_left {T : E →ₗ[𝕜] E} (hT : is_positive T) (x : E) :
  0 ≤ re ⟪T x, x⟫ :=
hT.2 x

lemma is_positive.inner_nonneg_right {T : E →ₗ[𝕜] E} (hT : is_positive T) (x : E) :
  0 ≤ re ⟪x, T x⟫ :=
by { rw inner_re_symm, exact hT.2 x, }

lemma is_positive_zero : (0 : E →ₗ[𝕜] E).is_positive :=
begin
  refine ⟨is_symmetric_zero, λ x, _⟩,
  simp_rw [zero_apply, inner_re_zero_left],
end

lemma is_positive_one : (1 : E →ₗ[𝕜] E).is_positive :=
⟨is_symmetric_id, λ x, inner_self_nonneg⟩

lemma is_positive.add {S T : E →ₗ[𝕜] E} (hS : S.is_positive) (hT : T.is_positive) :
  (S + T).is_positive :=
begin
  refine ⟨is_symmetric.add hS.1 hT.1, λ x, _⟩,
  rw [add_apply, inner_add_left, map_add],
  exact add_nonneg (hS.2 _) (hT.2 _),
end

/-- a linear projection onto `U` along its complement `V` is positive if
and only if `U` and `V` are orthogonal -/
lemma linear_proj_is_positive_iff {U V : submodule 𝕜 E} (hUV : is_compl U V) :
  (U.subtype.comp (U.linear_proj_of_is_compl V hUV)).is_positive ↔ U ⟂ V :=
begin
  split,
  { intros h u hu v hv,
    let a : U := ⟨u, hu⟩,
    let b : V := ⟨v, hv⟩,
    have hau : u = a := rfl,
    have hbv : v = b := rfl,
    rw [hau, ← submodule.linear_proj_of_is_compl_apply_left hUV a,
      ← submodule.subtype_apply _, ← comp_apply, ← h.1 _ _, comp_apply, hbv,
      submodule.linear_proj_of_is_compl_apply_right hUV b, map_zero, inner_zero_left], },
  { intro h,
    have : (U.subtype.comp (U.linear_proj_of_is_compl V hUV)).is_symmetric,
    { intros x y,
      nth_rewrite 0 ← submodule.linear_proj_add_linear_proj_of_is_compl_eq_self hUV y,
      nth_rewrite 1 ← submodule.linear_proj_add_linear_proj_of_is_compl_eq_self hUV x,
      simp_rw [inner_add_right, inner_add_left, comp_apply, submodule.subtype_apply _,
        ← submodule.coe_inner, submodule.is_ortho_iff_inner_eq.mp h _
          (submodule.coe_mem _) _ (submodule.coe_mem _),
        submodule.is_ortho_iff_inner_eq.mp h.symm _
          (submodule.coe_mem _) _ (submodule.coe_mem _)], },
    refine ⟨this, _⟩,
    intros x,
    rw [comp_apply, submodule.subtype_apply, ← submodule.linear_proj_of_is_compl_idempotent,
      ← submodule.subtype_apply, ← comp_apply, this ((U.linear_proj_of_is_compl V hUV) x) _],
    exact inner_self_nonneg, },
end

open_locale nnreal

/-- the spectrum of a positive linear map is non-negative -/
lemma is_positive.nonneg_spectrum [finite_dimensional 𝕜 E] {T : E →ₗ[𝕜] E} (h : T.is_positive) :
  spectrum 𝕜 T ⊆ set.range (algebra_map ℝ≥0 𝕜) :=
begin
  cases h with hT h,
  intros μ hμ,
  rw [set.mem_range, nnreal.exists],
  simp_rw [← module.End.has_eigenvalue_iff_mem_spectrum] at hμ,
  have : ↑(re μ) = μ,
  { simp_rw [← eq_conj_iff_re],
    exact is_symmetric.conj_eigenvalue_eq_self hT hμ, },
  rw ← this at hμ,
  simp_rw [hT _] at h,
  exact ⟨re μ, eigenvalue_nonneg_of_nonneg hμ h, this⟩,
end

section complex

/-- for spaces `V` over `ℂ`, it suffices to define positivity with
`0 ≤ ⟪T v, v⟫_ℂ` for all `v ∈ V` -/
lemma is_positive_iff_complex {V : Type*} [normed_add_comm_group V]
  [inner_product_space ℂ V] (T : V →ₗ[ℂ] V) :
  T.is_positive ↔ ∀ v : V, ↑(re ⟪T v, v⟫_ℂ) = ⟪T v, v⟫_ℂ ∧ 0 ≤ re ⟪T v, v⟫_ℂ :=
by simp_rw [is_positive, is_symmetric_iff_inner_map_self_real, inner_conj_symm,
     ← eq_conj_iff_re, inner_conj_symm, ← forall_and_distrib]

end complex

lemma is_positive.conj_adjoint [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 F]
  (T : E →ₗ[𝕜] E) (S : E →ₗ[𝕜] F) (h : T.is_positive) :
  (S.comp (T.comp S.adjoint)).is_positive :=
begin
  split,
  intros u v,
  simp_rw [comp_apply, ← adjoint_inner_left _ (T _), ← adjoint_inner_right _ (T _)],
  exact h.1 _ _,
  intros v,
  simp_rw [comp_apply, ← adjoint_inner_right _ (T _)],
  exact h.2 _,
end

lemma is_positive.adjoint_conj [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 F]
  (T : E →ₗ[𝕜] E) (S : F →ₗ[𝕜] E) (h : T.is_positive) :
  (S.adjoint.comp (T.comp S)).is_positive :=
begin
  split,
  intros u v,
  simp_rw [comp_apply, adjoint_inner_left, adjoint_inner_right],
  exact h.1 _ _,
  intros v,
  simp_rw [comp_apply, adjoint_inner_left],
  exact h.2 _,
end

end linear_map


namespace continuous_linear_map

open continuous_linear_map

variables [complete_space E] [complete_space F]

lemma is_positive_iff (T : E →L[𝕜] E) :
  (T : E →ₗ[𝕜] E).is_positive ↔ is_self_adjoint T ∧ ∀ x, 0 ≤ T.re_apply_inner_self x :=
by simp_rw [linear_map.is_positive, continuous_linear_map.coe_coe,
     is_self_adjoint_iff_is_symmetric, re_apply_inner_self_apply T]

lemma is_positive.is_self_adjoint {T : E →L[𝕜] E} (hT : (T : E →ₗ[𝕜] E).is_positive) :
  is_self_adjoint T :=
((is_positive_iff T).mp hT).1

lemma is_positive.adjoint {T : E →L[𝕜] E} (hT : (T : E →ₗ[𝕜] E).is_positive) :
  (T.adjoint : E →ₗ[𝕜] E).is_positive :=
by { rw [(is_positive.is_self_adjoint hT).adjoint_eq], exact hT, }

lemma is_positive.conj_adjoint {T : E →L[𝕜] E}
  (hT : (T : E →ₗ[𝕜] E).is_positive) (S : E →L[𝕜] F) :
  (S ∘L T ∘L S† : F →ₗ[𝕜] F).is_positive :=
begin
  rw is_positive_iff,
  refine ⟨(is_positive.is_self_adjoint hT).conj_adjoint S, λ x, _⟩,
  rw [re_apply_inner_self, comp_apply, ← adjoint_inner_right],
  exact hT.inner_nonneg_left _,
end

lemma is_positive.adjoint_conj {T : E →L[𝕜] E}
  (hT : (T : E →ₗ[𝕜] E).is_positive) (S : F →L[𝕜] E) :
  (S† ∘L T ∘L S : F →ₗ[𝕜] F).is_positive :=
begin
  nth_rewrite 1 ← adjoint_adjoint S,
  exact is_positive.conj_adjoint hT _,
end

lemma is_positive.conj_orthogonal_projection (U : submodule 𝕜 E) {T : E →L[𝕜] E}
  (hT : (T : E →ₗ[𝕜] E).is_positive) [complete_space U] :
  (U.subtypeL ∘L orthogonal_projection U ∘L T ∘L U.subtypeL ∘L
    orthogonal_projection U : E →ₗ[𝕜] E).is_positive :=
begin
  have := is_positive.conj_adjoint hT (U.subtypeL ∘L orthogonal_projection U),
  rwa (orthogonal_projection_is_self_adjoint U).adjoint_eq at this,
end

lemma is_positive.orthogonal_projection_comp {T : E →L[𝕜] E}
  (hT : T.is_positive) (U : submodule 𝕜 E) [complete_space U] :
  (orthogonal_projection U ∘L T ∘L U.subtypeL).is_positive :=
begin
  have := is_positive.conj_adjoint hT (orthogonal_projection U : E →L[𝕜] U),
  rwa [U.adjoint_orthogonal_projection] at this,
end

end continuous_linear_map

lemma orthogonal_projection_is_positive [complete_space E] (U : submodule 𝕜 E) [complete_space U] :
  (U.subtypeL ∘L (orthogonal_projection U) : E →ₗ[𝕜] E).is_positive :=
begin
  rw [continuous_linear_map.coe_comp, orthogonal_projection_coe_linear_map_eq_linear_proj,
    submodule.coe_subtypeL, linear_map.linear_proj_is_positive_iff],
  exact submodule.is_ortho_orthogonal_right _,
end
