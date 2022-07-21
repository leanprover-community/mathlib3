import analysis.convex.topology
import analysis.convex.strict
import analysis.normed_space.linear_isometry

/-!
-/

open function set metric
open_locale convex

/-! ### Normed vector space -/

variables {E E' F : Type*} [semi_normed_group E] [normed_space ℝ E]
  [normed_group E'] [normed_space ℝ E']
  [semi_normed_group F] [normed_space ℝ F]

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
