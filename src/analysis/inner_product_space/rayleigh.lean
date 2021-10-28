/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Frédéric Dupuis
-/
import analysis.inner_product_space.calculus
import analysis.inner_product_space.dual
import analysis.calculus.lagrange_multipliers
import linear_algebra.eigenspace

/-!
# The Rayleigh quotient

The Rayleigh quotient of a self-adjoint operator `T` on an inner product space `E` is the function
`λ x, ⟪T x, x⟫ / ∥x∥ ^ 2`.

The main results of this file are `self_adjoint.has_eigenvector_of_is_max_on` and
`self_adjoint.has_eigenvector_of_is_min_on`, which state that if `E` is complete, and if the
Rayleigh quotient attains its global maximum/minimum over some sphere at the point `x₀`, then `x₀`
is an eigenvector of `T`, and the `supr`/`infi` of `λ x, ⟪T x, x⟫ / ∥x∥ ^ 2` is the corresponding
eigenvalue.

The corollaries `self_adjoint.has_eigenvalue_supr_of_finite_dimensional` and
`self_adjoint.has_eigenvalue_supr_of_finite_dimensional` state that if `E` is finite-dimensional
and nontrivial, then `T` has some (nonzero) eigenvectors with eigenvalue the `supr`/`infi` of
`λ x, ⟪T x, x⟫ / ∥x∥ ^ 2`.

## TODO

A slightly more elaborate corollary is that if `E` is complete and `T` is a compact operator, then
`T` has some (nonzero) eigenvector with eigenvalue either `⨆ x, ⟪T x, x⟫ / ∥x∥ ^ 2` or
`⨅ x, ⟪T x, x⟫ / ∥x∥ ^ 2` (not necessarily both).

-/

variables {𝕜 : Type*} [is_R_or_C 𝕜]
variables {E : Type*} [inner_product_space 𝕜 E]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y
open_locale nnreal

open module.End metric

namespace continuous_linear_map
variables (T : E →L[𝕜] E)

lemma rayleigh_smul (x : E) {c : 𝕜} (hc : c ≠ 0) :
  T.re_apply_inner_self (c • x) / ∥(c • x:E)∥ ^ 2 = T.re_apply_inner_self x / ∥(x:E)∥ ^ 2 :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  have : ∥c∥ ≠ 0 := by simp [hc],
  have : ∥x∥ ≠ 0 := by simp [hx],
  field_simp [norm_smul, T.re_apply_inner_self_smul],
  ring
end

lemma image_rayleigh_eq_image_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
  (λ x : E, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2) '' {0}ᶜ
  = (λ x : E, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2) '' (sphere 0 r) :=
begin
  ext x,
  split,
  { rintros ⟨a, (ha : a ≠ 0), haT⟩,
    have : ∥a∥ ≠ 0 := by simp [ha],
    let c : 𝕜 := ↑∥a∥⁻¹ * r,
    have : c ≠ 0 := by simp [c, ha, hr.ne'],
    refine ⟨c • a, _, _⟩,
    { field_simp [norm_smul, is_R_or_C.norm_eq_abs, abs_of_nonneg hr.le] },
    convert haT using 1,
    simp [T.rayleigh_smul a this] },
  { rintros ⟨a, ha, haT⟩,
    exact ⟨a, nonzero_of_mem_sphere hr ⟨a, ha⟩, haT⟩ },
end

lemma supr_rayleigh_eq_supr_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
  (⨆ x : {x : E // x ≠ 0}, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2)
  = ⨆ x : sphere (0:E) r, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2 :=
begin
  let F : E → ℝ := λ x, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2,
  change (⨆ x : ({0} : set E)ᶜ, F x) = (⨆ x : sphere (0:E) r, F x),
  simp only [csupr_set, T.image_rayleigh_eq_image_rayleigh_sphere hr],
end

lemma infi_rayleigh_eq_infi_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
  (⨅ x : {x : E // x ≠ 0}, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2)
  = ⨅ x : sphere (0:E) r, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2 :=
begin
  let F : E → ℝ := λ x, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2,
  change (⨅ x : ({0} : set E)ᶜ, F x) = (⨅ x : sphere (0:E) r, F x),
  simp only [cinfi_set, T.image_rayleigh_eq_image_rayleigh_sphere hr],
end

end continuous_linear_map

namespace self_adjoint

section real
variables {F : Type*} [inner_product_space ℝ F] [complete_space F] {T : F →L[ℝ] F}

lemma linearly_dependent_of_is_local_extr_on (hT : self_adjoint (T : F →ₗ[ℝ] F))
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
  -- find Lagrange multipliers for the function `T.re_apply_inner_self` and the
  -- hypersurface-defining function `λ x, ∥x∥ ^ 2`
  obtain ⟨Λ, b, h₁, h₂⟩ := is_local_extr_on.exists_linear_map_of_has_strict_fderiv_at _
    (has_strict_fderiv_at_norm_sq x₀) hφ',
  refine ⟨Λ 1, b, _, _⟩,
  { contrapose! h₁,
    simp only [prod.mk_eq_zero] at ⊢ h₁,
    refine ⟨linear_map.ext (λ x, _), h₁.2⟩,
    simpa [h₁.1] using Λ.map_smul x 1 },
  { apply (inner_product_space.to_dual_map ℝ F).injective,
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

lemma eq_smul_self_of_is_local_extr_on_real (hT : self_adjoint (T : F →ₗ[ℝ] F))
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

lemma eq_smul_self_of_is_local_extr_on (hT : self_adjoint (T : E →ₗ[𝕜] E)) {x₀ : E}
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
  exact eq_smul_self_of_is_local_extr_on_real hSA hextr,
end

/-- For a self-adjoint operator `T`, a local extremum of the Rayleigh quotient of `T` on a sphere
centred at the origin is an eigenvector of `T`. -/
lemma has_eigenvector_of_is_local_extr_on (hT : self_adjoint (T : E →ₗ[𝕜] E)) {x₀ : E}
  (hx₀ : x₀ ≠ 0) (hextr : is_local_extr_on T.re_apply_inner_self (sphere (0:E) ∥x₀∥) x₀) :
  has_eigenvector (T : E →ₗ[𝕜] E) ↑(T.re_apply_inner_self x₀ / ∥x₀∥ ^ 2) x₀ :=
begin
  refine ⟨_, hx₀⟩,
  rw module.End.mem_eigenspace_iff,
  exact hT.eq_smul_self_of_is_local_extr_on hextr
end

/-- For a self-adjoint operator `T`, a maximum of the Rayleigh quotient of `T` on a sphere centred
at the origin is an eigenvector of `T`, with eigenvalue the global supremum of the Rayleigh
quotient. -/
lemma has_eigenvector_of_is_max_on (hT : self_adjoint (T : E →ₗ[𝕜] E)) {x₀ : E}
  (hx₀ : x₀ ≠ 0) (hextr : is_max_on T.re_apply_inner_self (sphere (0:E) ∥x₀∥) x₀) :
  has_eigenvector (T : E →ₗ[𝕜] E)
    ↑(⨆ x : {x : E // x ≠ 0}, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2) x₀ :=
begin
  convert hT.has_eigenvector_of_is_local_extr_on hx₀ (or.inr hextr.localize),
  have hx₀' : 0 < ∥x₀∥ := by simp [hx₀],
  have hx₀'' : x₀ ∈ sphere (0:E) (∥x₀∥) := by simp,
  rw T.supr_rayleigh_eq_supr_rayleigh_sphere hx₀',
  convert is_max_on.supr_eq hx₀'' _,
  { refl },
  intros x hx,
  dsimp,
  convert div_le_div_of_le (sq_nonneg ∥x₀∥) (hextr hx) using 3,
  simpa using hx,
end

/-- For a self-adjoint operator `T`, a minimum of the Rayleigh quotient of `T` on a sphere centred
at the origin is an eigenvector of `T`, with eigenvalue the global infimum of the Rayleigh
quotient. -/
lemma has_eigenvector_of_is_min_on (hT : self_adjoint (T : E →ₗ[𝕜] E)) {x₀ : E}
  (hx₀ : x₀ ≠ 0) (hextr : is_min_on T.re_apply_inner_self (sphere (0:E) ∥x₀∥) x₀) :
  has_eigenvector (T : E →ₗ[𝕜] E)
    ↑(⨅ x : {x : E // x ≠ 0}, T.re_apply_inner_self x / ∥(x:E)∥ ^ 2) x₀ :=
begin
  convert hT.has_eigenvector_of_is_local_extr_on hx₀ (or.inl hextr.localize),
  have hx₀' : 0 < ∥x₀∥ := by simp [hx₀],
  have hx₀'' : x₀ ∈ sphere (0:E) (∥x₀∥) := by simp,
  rw T.infi_rayleigh_eq_infi_rayleigh_sphere hx₀',
  convert is_min_on.infi_eq hx₀'' _,
  { refl },
  intros x hx,
  dsimp,
  convert div_le_div_of_le (sq_nonneg ∥x₀∥) (hextr hx) using 3,
  simpa using hx,
end

end complete_space

section finite_dimensional
variables [finite_dimensional 𝕜 E] [_i : nontrivial E] {T : E →ₗ[𝕜] E}

include _i

/-- The supremum of the Rayleigh quotient of a self-adjoint operator `T` on a nontrivial
finite-dimensional vector space is an eigenvalue for that operator. -/
lemma has_eigenvalue_supr_of_finite_dimensional (hT : self_adjoint T) :
  has_eigenvalue T ↑(⨆ x : {x : E // x ≠ 0}, is_R_or_C.re ⟪T x, x⟫ / ∥(x:E)∥ ^ 2) :=
begin
  let T' : E →L[𝕜] E := T.to_continuous_linear_map,
  have hT' : self_adjoint (T' : E →ₗ[𝕜] E) := hT,
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0,
  have H₁ : is_compact (sphere (0:E) ∥x∥) := is_compact_sphere _ _,
  have H₂ : (sphere (0:E) ∥x∥).nonempty := ⟨x, by simp⟩,
  -- key point: in finite dimension, a continuous function on the sphere has a max
  obtain ⟨x₀, hx₀', hTx₀⟩ :=
    H₁.exists_forall_ge H₂ T'.re_apply_inner_self_continuous.continuous_on,
  have hx₀ : ∥x₀∥ = ∥x∥ := by simpa using hx₀',
  have : is_max_on T'.re_apply_inner_self (sphere 0 ∥x₀∥) x₀,
  { simpa only [← hx₀] using hTx₀ },
  have hx₀_ne : x₀ ≠ 0,
  { have : ∥x₀∥ ≠ 0 := by simp only [hx₀, norm_eq_zero, hx, ne.def, not_false_iff],
    simpa [← norm_eq_zero, ne.def] },
  convert has_eigenvalue_of_has_eigenvector (hT'.has_eigenvector_of_is_max_on hx₀_ne this)
end

/-- The infimum of the Rayleigh quotient of a self-adjoint operator `T` on a nontrivial
finite-dimensional vector space is an eigenvalue for that operator. -/
lemma has_eigenvalue_infi_of_finite_dimensional (hT : self_adjoint T) :
  has_eigenvalue T ↑(⨅ x : {x : E // x ≠ 0}, is_R_or_C.re ⟪T x, x⟫ / ∥(x:E)∥ ^ 2) :=
begin
  let T' : E →L[𝕜] E := T.to_continuous_linear_map,
  have hT' : self_adjoint (T' : E →ₗ[𝕜] E) := hT,
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0,
  have H₁ : is_compact (sphere (0:E) ∥x∥) := is_compact_sphere _ _,
  have H₂ : (sphere (0:E) ∥x∥).nonempty := ⟨x, by simp⟩,
  -- key point: in finite dimension, a continuous function on the sphere has a min
  obtain ⟨x₀, hx₀', hTx₀⟩ :=
    H₁.exists_forall_le H₂ T'.re_apply_inner_self_continuous.continuous_on,
  have hx₀ : ∥x₀∥ = ∥x∥ := by simpa using hx₀',
  have : is_min_on T'.re_apply_inner_self (sphere 0 ∥x₀∥) x₀,
  { simpa only [← hx₀] using hTx₀ },
  have hx₀_ne : x₀ ≠ 0,
  { have : ∥x₀∥ ≠ 0 := by simp only [hx₀, norm_eq_zero, hx, ne.def, not_false_iff],
    simpa [← norm_eq_zero, ne.def] },
  convert has_eigenvalue_of_has_eigenvector (hT'.has_eigenvector_of_is_min_on hx₀_ne this)
end

omit _i

lemma subsingleton_of_no_eigenvalue_finite_dimensional
  (hT : self_adjoint T) (hT' : ∀ μ : 𝕜, module.End.eigenspace (T : E →ₗ[𝕜] E) μ = ⊥) :
  subsingleton E :=
(subsingleton_or_nontrivial E).resolve_right
  (λ h, by exactI absurd (hT' _) hT.has_eigenvalue_supr_of_finite_dimensional)

end finite_dimensional

end self_adjoint
