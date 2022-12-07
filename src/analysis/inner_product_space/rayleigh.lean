/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Frédéric Dupuis
-/
import analysis.inner_product_space.calculus
import analysis.inner_product_space.dual
import analysis.inner_product_space.adjoint
import analysis.calculus.lagrange_multipliers
import linear_algebra.eigenspace

/-!
# The Rayleigh quotient

The Rayleigh quotient of a self-adjoint operator `T` on an inner product space `E` is the function
`λ x, ⟪T x, x⟫ / ‖x‖ ^ 2`.

The main results of this file are `is_self_adjoint.has_eigenvector_of_is_max_on` and
`is_self_adjoint.has_eigenvector_of_is_min_on`, which state that if `E` is complete, and if the
Rayleigh quotient attains its global maximum/minimum over some sphere at the point `x₀`, then `x₀`
is an eigenvector of `T`, and the `supr`/`infi` of `λ x, ⟪T x, x⟫ / ‖x‖ ^ 2` is the corresponding
eigenvalue.

The corollaries `is_self_adjoint.has_eigenvalue_supr_of_finite_dimensional` and
`is_self_adjoint.has_eigenvalue_supr_of_finite_dimensional` state that if `E` is finite-dimensional
and nontrivial, then `T` has some (nonzero) eigenvectors with eigenvalue the `supr`/`infi` of
`λ x, ⟪T x, x⟫ / ‖x‖ ^ 2`.

## TODO

A slightly more elaborate corollary is that if `E` is complete and `T` is a compact operator, then
`T` has some (nonzero) eigenvector with eigenvalue either `⨆ x, ⟪T x, x⟫ / ‖x‖ ^ 2` or
`⨅ x, ⟪T x, x⟫ / ‖x‖ ^ 2` (not necessarily both).

-/

variables {𝕜 : Type*} [is_R_or_C 𝕜]
variables {E : Type*} [inner_product_space 𝕜 E]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y
open_locale nnreal

open module.End metric

namespace continuous_linear_map
variables (T : E →L[𝕜] E)
local notation `rayleigh_quotient` := λ x : E, T.re_apply_inner_self x / ‖(x:E)‖ ^ 2

lemma rayleigh_smul (x : E) {c : 𝕜} (hc : c ≠ 0) :
  rayleigh_quotient (c • x) = rayleigh_quotient x :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  have : ‖c‖ ≠ 0 := by simp [hc],
  have : ‖x‖ ≠ 0 := by simp [hx],
  field_simp [norm_smul, T.re_apply_inner_self_smul],
  ring
end

lemma image_rayleigh_eq_image_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
  rayleigh_quotient '' {0}ᶜ = rayleigh_quotient '' (sphere 0 r) :=
begin
  ext a,
  split,
  { rintros ⟨x, (hx : x ≠ 0), hxT⟩,
    have : ‖x‖ ≠ 0 := by simp [hx],
    let c : 𝕜 := ↑‖x‖⁻¹ * r,
    have : c ≠ 0 := by simp [c, hx, hr.ne'],
    refine ⟨c • x, _, _⟩,
    { field_simp [norm_smul, is_R_or_C.norm_eq_abs, abs_of_nonneg hr.le] },
    { rw T.rayleigh_smul x this,
      exact hxT } },
  { rintros ⟨x, hx, hxT⟩,
    exact ⟨x, ne_zero_of_mem_sphere hr.ne' ⟨x, hx⟩, hxT⟩ },
end

lemma supr_rayleigh_eq_supr_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
  (⨆ x : {x : E // x ≠ 0}, rayleigh_quotient x) = ⨆ x : sphere (0:E) r, rayleigh_quotient x :=
show (⨆ x : ({0} : set E)ᶜ, rayleigh_quotient x) = _,
by simp only [←@Sup_image' _ _ _ _ rayleigh_quotient, T.image_rayleigh_eq_image_rayleigh_sphere hr]

lemma infi_rayleigh_eq_infi_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
  (⨅ x : {x : E // x ≠ 0}, rayleigh_quotient x) = ⨅ x : sphere (0:E) r, rayleigh_quotient x :=
show (⨅ x : ({0} : set E)ᶜ, rayleigh_quotient x) = _,
by simp only [←@Inf_image' _ _ _ _ rayleigh_quotient, T.image_rayleigh_eq_image_rayleigh_sphere hr]

end continuous_linear_map

namespace is_self_adjoint

section real
variables {F : Type*} [inner_product_space ℝ F]

lemma _root_.linear_map.is_symmetric.has_strict_fderiv_at_re_apply_inner_self
  {T : F →L[ℝ] F} (hT : (T : F →ₗ[ℝ] F).is_symmetric) (x₀ : F) :
  has_strict_fderiv_at T.re_apply_inner_self (_root_.bit0 (innerSL (T x₀) : F →L[ℝ] ℝ)) x₀ :=
begin
  convert T.has_strict_fderiv_at.inner (has_strict_fderiv_at_id x₀),
  ext y,
  simp_rw [_root_.bit0, continuous_linear_map.comp_apply, continuous_linear_map.add_apply,
    innerSL_apply, fderiv_inner_clm_apply, id.def, continuous_linear_map.prod_apply,
    continuous_linear_map.id_apply, hT.apply_clm x₀ y, real_inner_comm _ x₀],
end

variables [complete_space F] {T : F →L[ℝ] F}
local notation `rayleigh_quotient` := λ x : F, T.re_apply_inner_self x / ‖(x:F)‖ ^ 2

lemma linearly_dependent_of_is_local_extr_on (hT : is_self_adjoint T)
  {x₀ : F} (hextr : is_local_extr_on T.re_apply_inner_self (sphere (0:F) ‖x₀‖) x₀) :
  ∃ a b : ℝ, (a, b) ≠ 0 ∧ a • x₀ + b • T x₀ = 0 :=
begin
  have H : is_local_extr_on T.re_apply_inner_self {x : F | ‖x‖ ^ 2 = ‖x₀‖ ^ 2} x₀,
  { convert hextr,
    ext x,
    simp [dist_eq_norm] },
  -- find Lagrange multipliers for the function `T.re_apply_inner_self` and the
  -- hypersurface-defining function `λ x, ‖x‖ ^ 2`
  obtain ⟨a, b, h₁, h₂⟩ := is_local_extr_on.exists_multipliers_of_has_strict_fderiv_at_1d H
    (has_strict_fderiv_at_norm_sq x₀) (hT.is_symmetric.has_strict_fderiv_at_re_apply_inner_self x₀),
  refine ⟨a, b, h₁, _⟩,
  apply (inner_product_space.to_dual_map ℝ F).injective,
  simp only [linear_isometry.map_add, linear_isometry.map_smul, linear_isometry.map_zero],
  change a • innerSL x₀ + b • innerSL (T x₀) = 0,
  apply smul_right_injective (F →L[ℝ] ℝ) (two_ne_zero : (2:ℝ) ≠ 0),
  simpa only [_root_.bit0, add_smul, smul_add, one_smul, add_zero] using h₂
end

lemma eq_smul_self_of_is_local_extr_on_real (hT : is_self_adjoint T)
  {x₀ : F} (hextr : is_local_extr_on T.re_apply_inner_self (sphere (0:F) ‖x₀‖) x₀) :
  T x₀ = (rayleigh_quotient x₀) • x₀ :=
begin
  obtain ⟨a, b, h₁, h₂⟩ := hT.linearly_dependent_of_is_local_extr_on hextr,
  by_cases hx₀ : x₀ = 0,
  { simp [hx₀] },
  by_cases hb : b = 0,
  { have : a ≠ 0 := by simpa [hb] using h₁,
    refine absurd _ hx₀,
    apply smul_right_injective F this,
    simpa [hb] using h₂ },
  let c : ℝ := - b⁻¹ * a,
  have hc : T x₀ = c • x₀,
  { have : b * (b⁻¹ * a) = a := by field_simp [mul_comm],
    apply smul_right_injective F hb,
    simp [c, eq_neg_of_add_eq_zero_left h₂, ← mul_smul, this] },
  convert hc,
  have : ‖x₀‖ ≠ 0 := by simp [hx₀],
  field_simp,
  simpa [inner_smul_left, real_inner_self_eq_norm_mul_norm, sq] using congr_arg (λ x, ⟪x, x₀⟫_ℝ) hc,
end

end real

section complete_space
variables [complete_space E] {T : E →L[𝕜] E}
local notation `rayleigh_quotient` := λ x : E, T.re_apply_inner_self x / ‖(x:E)‖ ^ 2

lemma eq_smul_self_of_is_local_extr_on (hT : is_self_adjoint T) {x₀ : E}
  (hextr : is_local_extr_on T.re_apply_inner_self (sphere (0:E) ‖x₀‖) x₀) :
  T x₀ = (↑(rayleigh_quotient x₀) : 𝕜) • x₀ :=
begin
  letI := inner_product_space.is_R_or_C_to_real 𝕜 E,
  let hSA := hT.is_symmetric.restrict_scalars.to_self_adjoint.prop,
  exact hSA.eq_smul_self_of_is_local_extr_on_real hextr,
end

/-- For a self-adjoint operator `T`, a local extremum of the Rayleigh quotient of `T` on a sphere
centred at the origin is an eigenvector of `T`. -/
lemma has_eigenvector_of_is_local_extr_on (hT : is_self_adjoint T) {x₀ : E}
  (hx₀ : x₀ ≠ 0) (hextr : is_local_extr_on T.re_apply_inner_self (sphere (0:E) ‖x₀‖) x₀) :
  has_eigenvector (T : E →ₗ[𝕜] E) ↑(rayleigh_quotient x₀) x₀ :=
begin
  refine ⟨_, hx₀⟩,
  rw module.End.mem_eigenspace_iff,
  exact hT.eq_smul_self_of_is_local_extr_on hextr
end

/-- For a self-adjoint operator `T`, a maximum of the Rayleigh quotient of `T` on a sphere centred
at the origin is an eigenvector of `T`, with eigenvalue the global supremum of the Rayleigh
quotient. -/
lemma has_eigenvector_of_is_max_on (hT : is_self_adjoint T) {x₀ : E}
  (hx₀ : x₀ ≠ 0) (hextr : is_max_on T.re_apply_inner_self (sphere (0:E) ‖x₀‖) x₀) :
  has_eigenvector (T : E →ₗ[𝕜] E) ↑(⨆ x : {x : E // x ≠ 0}, rayleigh_quotient x) x₀ :=
begin
  convert hT.has_eigenvector_of_is_local_extr_on hx₀ (or.inr hextr.localize),
  have hx₀' : 0 < ‖x₀‖ := by simp [hx₀],
  have hx₀'' : x₀ ∈ sphere (0:E) (‖x₀‖) := by simp,
  rw T.supr_rayleigh_eq_supr_rayleigh_sphere hx₀',
  refine is_max_on.supr_eq hx₀'' _,
  intros x hx,
  dsimp,
  have : ‖x‖ = ‖x₀‖ := by simpa using hx,
  rw this,
  exact div_le_div_of_le (sq_nonneg ‖x₀‖) (hextr hx)
end

/-- For a self-adjoint operator `T`, a minimum of the Rayleigh quotient of `T` on a sphere centred
at the origin is an eigenvector of `T`, with eigenvalue the global infimum of the Rayleigh
quotient. -/
lemma has_eigenvector_of_is_min_on (hT : is_self_adjoint T) {x₀ : E}
  (hx₀ : x₀ ≠ 0) (hextr : is_min_on T.re_apply_inner_self (sphere (0:E) ‖x₀‖) x₀) :
  has_eigenvector (T : E →ₗ[𝕜] E) ↑(⨅ x : {x : E // x ≠ 0}, rayleigh_quotient x) x₀ :=
begin
  convert hT.has_eigenvector_of_is_local_extr_on hx₀ (or.inl hextr.localize),
  have hx₀' : 0 < ‖x₀‖ := by simp [hx₀],
  have hx₀'' : x₀ ∈ sphere (0:E) (‖x₀‖) := by simp,
  rw T.infi_rayleigh_eq_infi_rayleigh_sphere hx₀',
  refine is_min_on.infi_eq hx₀'' _,
  intros x hx,
  dsimp,
  have : ‖x‖ = ‖x₀‖ := by simpa using hx,
  rw this,
  exact div_le_div_of_le (sq_nonneg ‖x₀‖) (hextr hx)
end

end complete_space

end is_self_adjoint

section finite_dimensional
variables [finite_dimensional 𝕜 E] [_i : nontrivial E] {T : E →ₗ[𝕜] E}

namespace linear_map

namespace is_symmetric

include _i

/-- The supremum of the Rayleigh quotient of a symmetric operator `T` on a nontrivial
finite-dimensional vector space is an eigenvalue for that operator. -/
lemma has_eigenvalue_supr_of_finite_dimensional (hT : T.is_symmetric) :
  has_eigenvalue T ↑(⨆ x : {x : E // x ≠ 0}, is_R_or_C.re ⟪T x, x⟫ / ‖(x:E)‖ ^ 2) :=
begin
  haveI := finite_dimensional.proper_is_R_or_C 𝕜 E,
  let T' := hT.to_self_adjoint,
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0,
  have H₁ : is_compact (sphere (0:E) ‖x‖) := is_compact_sphere _ _,
  have H₂ : (sphere (0:E) ‖x‖).nonempty := ⟨x, by simp⟩,
  -- key point: in finite dimension, a continuous function on the sphere has a max
  obtain ⟨x₀, hx₀', hTx₀⟩ :=
    H₁.exists_forall_ge H₂ T'.val.re_apply_inner_self_continuous.continuous_on,
  have hx₀ : ‖x₀‖ = ‖x‖ := by simpa using hx₀',
  have : is_max_on T'.val.re_apply_inner_self (sphere 0 ‖x₀‖) x₀,
  { simpa only [← hx₀] using hTx₀ },
  have hx₀_ne : x₀ ≠ 0,
  { have : ‖x₀‖ ≠ 0 := by simp only [hx₀, norm_eq_zero, hx, ne.def, not_false_iff],
    simpa [← norm_eq_zero, ne.def] },
  exact has_eigenvalue_of_has_eigenvector (T'.prop.has_eigenvector_of_is_max_on hx₀_ne this)
end

/-- The infimum of the Rayleigh quotient of a symmetric operator `T` on a nontrivial
finite-dimensional vector space is an eigenvalue for that operator. -/
lemma has_eigenvalue_infi_of_finite_dimensional (hT : T.is_symmetric) :
  has_eigenvalue T ↑(⨅ x : {x : E // x ≠ 0}, is_R_or_C.re ⟪T x, x⟫ / ‖(x:E)‖ ^ 2) :=
begin
  haveI := finite_dimensional.proper_is_R_or_C 𝕜 E,
  let T' := hT.to_self_adjoint,
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0,
  have H₁ : is_compact (sphere (0:E) ‖x‖) := is_compact_sphere _ _,
  have H₂ : (sphere (0:E) ‖x‖).nonempty := ⟨x, by simp⟩,
  -- key point: in finite dimension, a continuous function on the sphere has a min
  obtain ⟨x₀, hx₀', hTx₀⟩ :=
    H₁.exists_forall_le H₂ T'.val.re_apply_inner_self_continuous.continuous_on,
  have hx₀ : ‖x₀‖ = ‖x‖ := by simpa using hx₀',
  have : is_min_on T'.val.re_apply_inner_self (sphere 0 ‖x₀‖) x₀,
  { simpa only [← hx₀] using hTx₀ },
  have hx₀_ne : x₀ ≠ 0,
  { have : ‖x₀‖ ≠ 0 := by simp only [hx₀, norm_eq_zero, hx, ne.def, not_false_iff],
    simpa [← norm_eq_zero, ne.def] },
  exact has_eigenvalue_of_has_eigenvector (T'.prop.has_eigenvector_of_is_min_on hx₀_ne this)
end

omit _i

lemma subsingleton_of_no_eigenvalue_finite_dimensional
  (hT : T.is_symmetric) (hT' : ∀ μ : 𝕜, module.End.eigenspace (T : E →ₗ[𝕜] E) μ = ⊥) :
  subsingleton E :=
(subsingleton_or_nontrivial E).resolve_right
  (λ h, by exactI absurd (hT' _) hT.has_eigenvalue_supr_of_finite_dimensional)

end is_symmetric

end linear_map

end finite_dimensional
