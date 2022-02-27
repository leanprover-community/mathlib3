/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.normed.group.completion
import analysis.normed_space.operator_norm
import topology.algebra.uniform_mul_action

/-!
# Normed space structure on the completion of a normed space

If `E` is a normed space over `𝕜`, then so is `uniform_space.completion E`. In this file we provide
necessary instances and define `uniform_space.completion.to_complₗᵢ` - coercion
`E → uniform_space.completion E` as a bundled linear isometry.
-/

noncomputable theory

namespace uniform_space
namespace completion

variables (𝕜 E : Type*) [normed_field 𝕜] [normed_group E] [normed_space 𝕜 E]

@[priority 100]
instance normed_space.to_has_uniform_continuous_const_smul :
  has_uniform_continuous_const_smul 𝕜 E :=
⟨λ c, (lipschitz_with_smul c).uniform_continuous⟩

instance : normed_space 𝕜 (completion E) :=
{ smul := (•),
  norm_smul_le := λ c x, induction_on x
    (is_closed_le (continuous_const_smul _).norm (continuous_const.mul continuous_norm)) $
    λ y, by simp only [← coe_smul, norm_coe, norm_smul],
  .. completion.module 𝕜 E }

variables {𝕜 E}

/-- Embedding of a normed space to its completion as a linear isometry. -/
def to_complₗᵢ : E →ₗᵢ[𝕜] completion E :=
{ to_fun := coe,
  map_smul' := coe_smul,
  norm_map' := norm_coe,
  .. to_compl }

@[simp] lemma coe_to_complₗᵢ : ⇑(to_complₗᵢ : E →ₗᵢ[𝕜] completion E) = coe := rfl

/-- Embedding of a normed space to its completion as a continuous linear map. -/
def to_complL : E →L[𝕜] completion E :=
to_complₗᵢ.to_continuous_linear_map

@[simp] lemma coe_to_complL : ⇑(to_complL : E →L[𝕜] completion E) = coe := rfl

@[simp] lemma norm_to_complL {𝕜 E : Type*} [nondiscrete_normed_field 𝕜]
  [normed_group E] [normed_space 𝕜 E] [nontrivial E] : ∥(to_complL : E →L[𝕜] completion E)∥ = 1 :=
(to_complₗᵢ : E →ₗᵢ[𝕜] completion E).norm_to_continuous_linear_map

end completion
end uniform_space
