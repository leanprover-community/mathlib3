/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.inner_product_space.calculus
import analysis.inner_product_space.dual
import analysis.calculus.lagrange_multipliers
import linear_algebra.eigenspace

/-!
# The Rayleigh quotient

-/
variables {𝕜 : Type*} [is_R_or_C 𝕜]
variables {E : Type*} [inner_product_space 𝕜 E]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

open module.End metric

section real
variables {F : Type*} [inner_product_space ℝ F] [complete_space F] {T : F →L[ℝ] F}

-- move this
lemma has_strict_fderiv_at_norm_sq (x : F) :
  has_strict_fderiv_at (λ x, ∥x∥ ^ 2) (bit0 (inner_right x)) x :=
begin
  convert (has_strict_fderiv_at_id x).inner (has_strict_fderiv_at_id x),
  { ext y,
    simp [norm_sq_eq_inner] },
  { ext y,
    simp [bit0, real_inner_comm] },
end

lemma self_adjoint.linearly_dependent_of_is_local_extr_on (hT : self_adjoint (T : F →ₗ[ℝ] F))
  {x₀ : F} (hextr : is_local_extr_on T.re_apply_inner_self (sphere (0:F) ∥x₀∥) x₀) :
  ∃ a b : ℝ, (a, b) ≠ 0 ∧ a • x₀ + b • T x₀ = 0 :=
begin
  let φ' : F →L[ℝ] ℝ := bit0 (inner_right (T x₀)),
  have hφ' : has_strict_fderiv_at T.re_apply_inner_self φ' x₀,
  { convert T.has_strict_fderiv_at.inner (has_strict_fderiv_at_id x₀),
    ext y,
    simp only [φ', add_left_inj, bit0, continuous_linear_map.add_apply,
      continuous_linear_map.coe_comp', continuous_linear_map.coe_id',
      continuous_linear_map.prod_apply, eq_self_iff_true, fderiv_inner_clm_apply,
      function.comp_app, id.def, inner_right_apply, hT.apply_clm x₀ y, real_inner_comm x₀] },
  obtain ⟨Λ, b, h₁, h₂⟩ := is_local_extr_on.exists_linear_map_of_has_strict_fderiv_at _
    (has_strict_fderiv_at_norm_sq x₀) hφ',
  refine ⟨Λ 1, b, _, _⟩,
  { contrapose! h₁,
    simp only [prod.mk_eq_zero] at ⊢ h₁,
    refine ⟨linear_map.ext (λ x, _), h₁.2⟩,
    simpa [h₁.1] using Λ.map_smul x 1 },
  { apply (inner_product_space.to_dual_map F).injective,
    ext x,
    have : (Λ ⟪x₀, x⟫_ℝ + Λ ⟪x₀, x⟫_ℝ) + (b * ⟪T x₀, x⟫_ℝ + b * ⟪T x₀, x⟫_ℝ) = 0,
    { simpa only [φ', bit0, inner_right_apply, algebra.id.smul_eq_mul,
      continuous_linear_map.add_apply, linear_map.map_add, mul_add] using h₂ x },
    simp only [continuous_linear_map.zero_apply, algebra.id.smul_eq_mul,
      inner_product_space.to_dual_map_apply, linear_isometry.map_add, linear_isometry.map_smul,
      continuous_linear_map.add_apply, pi.smul_apply, linear_isometry.map_zero,
      continuous_linear_map.coe_smul'],
    have : Λ ⟪x₀, x⟫_ℝ = ⟪x₀, x⟫_ℝ * Λ 1,
    { simpa only [mul_one, algebra.id.smul_eq_mul] using Λ.map_smul ⟪x₀, x⟫_ℝ (1:ℝ) },
    linarith },
  convert hextr,
  ext x,
  simp [dist_eq_norm]
end

lemma self_adjoint.eq_smul_self_of_is_local_extr_on_real (hT : self_adjoint (T : F →ₗ[ℝ] F))
  {x₀ : F} (hextr : is_local_extr_on T.re_apply_inner_self (sphere (0:F) ∥x₀∥) x₀) :
  T x₀ = (T.re_apply_inner_self x₀ / ∥x₀∥ ^ 2) • x₀ :=
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
    simp [c, ← neg_eq_of_add_eq_zero h₂, ← mul_smul, this] },
  convert hc,
  have : ∥x₀∥ ≠ 0 := by simp [hx₀],
  field_simp,
  simpa [inner_smul_left, real_inner_self_eq_norm_sq, sq] using congr_arg (λ x, ⟪x, x₀⟫_ℝ) hc,
end

end real

section complete_space
variables [complete_space E] {T : E →L[𝕜] E}

lemma self_adjoint.eq_smul_self_of_is_local_extr_on (hT : self_adjoint (T : E →ₗ[𝕜] E)) {x₀ : E}
  (hextr : is_local_extr_on T.re_apply_inner_self (sphere (0:E) ∥x₀∥) x₀) :
  T x₀ = (↑(T.re_apply_inner_self x₀ / ∥x₀∥ ^ 2) : 𝕜) • x₀ :=
begin
  letI := inner_product_space.is_R_or_C_to_real 𝕜 E,
  letI : is_scalar_tower ℝ 𝕜 E := restrict_scalars.is_scalar_tower _ _ _,
  let S : E →L[ℝ] E :=
    @continuous_linear_map.restrict_scalars 𝕜 E E _ _ _ _ _ _ _ ℝ _ _ _ _ T,
  have hSA : self_adjoint (S : E →ₗ[ℝ] E) := λ x y, by
  { have := hT x y,
    simp only [continuous_linear_map.coe_coe] at this,
    simp only [real_inner_eq_re_inner, this, continuous_linear_map.coe_restrict_scalars,
      continuous_linear_map.coe_coe, linear_map.coe_restrict_scalars_eq_coe] },
  exact self_adjoint.eq_smul_self_of_is_local_extr_on_real hSA hextr,
end

/-- For a self-adjoint operator `T`, a local extremum of the Rayleigh quotient of `T` on a sphere
centred at the origin is an eigenvector of `T`. -/
lemma self_adjoint.has_eigenvector_of_is_local_extr_on (hT : self_adjoint (T : E →ₗ[𝕜] E)) {x₀ : E}
  (hx₀ : x₀ ≠ 0) (hextr : is_local_extr_on T.re_apply_inner_self (sphere (0:E) ∥x₀∥) x₀) :
  has_eigenvector (T : E →ₗ[𝕜] E) ↑(T.re_apply_inner_self x₀ / ∥x₀∥ ^ 2) x₀ :=
begin
  refine ⟨_, hx₀⟩,
  rw module.End.mem_eigenspace_iff,
  exact hT.eq_smul_self_of_is_local_extr_on hextr
end

end complete_space

section finite_dimensional
variables [finite_dimensional 𝕜 E] [nontrivial E]

/-- A self-adjoint operator on a nontrivial finite-dimensional vector space has a real eigenvalue.
-/
lemma self_adjoint.has_eigenvalue_of_finite_dimensional {T : E →ₗ[𝕜] E} (hT : self_adjoint T) :
  ∃ c : ℝ, has_eigenvalue T c :=
begin
  let T' : E →L[𝕜] E := T.to_continuous_linear_map,
  have hT' : self_adjoint (T' : E →ₗ[𝕜] E) := hT,
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0,
  have H₁ : is_compact (sphere (0:E) ∥x∥) := is_compact_sphere _ _,
  have H₂ : (sphere (0:E) ∥x∥).nonempty := ⟨x, by simp⟩,
  obtain ⟨x₀, hx₀', hTx₀⟩ :=
    H₁.exists_forall_ge H₂ T'.re_apply_inner_self_continuous.continuous_on,
  have hx₀ : ∥x₀∥ = ∥x∥ := by simpa using hx₀',
  have : is_local_max_on T'.re_apply_inner_self (sphere 0 ∥x₀∥) x₀,
  { simp only [← hx₀] at hTx₀,
    exact is_max_on.localize hTx₀ },
  have hx₀_ne : x₀ ≠ 0,
  { have : ∥x₀∥ ≠ 0 := by simp only [hx₀, norm_eq_zero, hx, ne.def, not_false_iff],
    simpa [← norm_eq_zero, ne.def] },
  use (T'.re_apply_inner_self x₀) / ∥x₀∥ ^ 2,
  exact has_eigenvalue_of_has_eigenvector
    (hT'.has_eigenvector_of_is_local_extr_on hx₀_ne (or.inr this))
end

end finite_dimensional
