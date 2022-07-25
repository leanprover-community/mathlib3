/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.convex.strict_convex_space
import analysis.normed_space.linear_isometry

/-!
# (Strict) convexity and linear isometries

In this file we prove some basic lemmas about (strict) convexity and linear isometries.
-/

open function set metric
open_locale convex

variables {E E' F F' : Type*}
  [seminormed_add_comm_group E] [normed_space ℝ E]
  [seminormed_add_comm_group F] [normed_space ℝ F]
  [normed_add_comm_group E'] [normed_space ℝ E']
  [normed_add_comm_group F'] [normed_space ℝ F']

lemma strict_convex.linear_isometry_preimage {s : set F} (hs : strict_convex ℝ s)
  (e : E' →ₗᵢ[ℝ] F) :
  strict_convex ℝ (e ⁻¹' s) :=
hs.linear_preimage _ e.continuous e.injective

@[simp] lemma linear_isometry_equiv.strict_convex_preimage {s : set F} (e : E ≃ₗᵢ[ℝ] F) :
  strict_convex ℝ (e ⁻¹' s) ↔ strict_convex ℝ s :=
⟨λ h, left_inverse.preimage_preimage e.right_inv s ▸
    h.linear_preimage e.symm.to_linear_isometry.to_linear_map e.symm.continuous e.symm.injective,
  λ h, h.linear_preimage e.to_linear_isometry.to_linear_map e.continuous e.injective⟩

@[simp] lemma linear_isometry_equiv.strict_convex_image {s : set E} (e : E ≃ₗᵢ[ℝ] F) :
  strict_convex ℝ (e '' s) ↔ strict_convex ℝ s :=
by rw [e.image_eq_preimage, e.symm.strict_convex_preimage]

lemma linear_isometry_equiv.strict_convex_space_iff (e : E' ≃ₗᵢ[ℝ] F') :
  strict_convex_space ℝ E' ↔ strict_convex_space ℝ F' :=
by simp only [strict_convex_space_def, ← map_zero e, ← e.image_closed_ball, e.strict_convex_image]

lemma linear_isometry.strict_convex_space_range_iff (e : E' →ₗᵢ[ℝ] F') :
  strict_convex_space ℝ e.to_linear_map.range ↔ strict_convex_space ℝ E' :=
e.equiv_range.strict_convex_space_iff.symm

instance linear_isometry.strict_convex_space_range [strict_convex_space ℝ E'] (e : E' →ₗᵢ[ℝ] F') :
  strict_convex_space ℝ e.to_linear_map.range :=
e.strict_convex_space_range_iff.mpr ‹_›

/-- A vector subspace of a strict convex space is a strict convex space. This instance has priority
900 to make sure that instances like `linear_isometry.strict_convex_space_range` are tried before
this one.  -/
@[priority 900]
instance submodule.strict_convex_space [strict_convex_space ℝ E'] (p : submodule ℝ E') :
  strict_convex_space ℝ p :=
begin
  refine ⟨λ r hr, _⟩,
  rw [← p.subtypeₗᵢ.isometry.preimage_closed_ball],
  exact (strict_convex_closed_ball _ _ _).linear_isometry_preimage _
end
