/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.normed.group.completion
import analysis.normed_space.operator_norm
import topology.algebra.uniform_ring

/-!
# Normed space structure on the completion of a normed space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If `E` is a normed space over `𝕜`, then so is `uniform_space.completion E`. In this file we provide
necessary instances and define `uniform_space.completion.to_complₗᵢ` - coercion
`E → uniform_space.completion E` as a bundled linear isometry.

We also show that if `A` is a normed algebra over `𝕜`, then so is `uniform_space.completion A`.

TODO: Generalise the results here from the concrete `completion` to any `abstract_completion`.
-/

noncomputable theory

namespace uniform_space
namespace completion

variables (𝕜 E : Type*) [normed_field 𝕜] [normed_add_comm_group E] [normed_space 𝕜 E]

@[priority 100]
instance normed_space.to_has_uniform_continuous_const_smul :
  has_uniform_continuous_const_smul 𝕜 E :=
⟨λ c, (lipschitz_with_smul c).uniform_continuous⟩

instance : normed_space 𝕜 (completion E) :=
{ smul := (•),
  norm_smul_le := λ c x, induction_on x
    (is_closed_le (continuous_const_smul _).norm (continuous_const.mul continuous_norm)) $
    λ y, by simp only [← coe_smul, norm_coe, norm_smul],
  .. completion.module }

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

@[simp] lemma norm_to_complL {𝕜 E : Type*} [nontrivially_normed_field 𝕜] [normed_add_comm_group E]
  [normed_space 𝕜 E] [nontrivial E] : ‖(to_complL : E →L[𝕜] completion E)‖ = 1 :=
(to_complₗᵢ : E →ₗᵢ[𝕜] completion E).norm_to_continuous_linear_map

section algebra

variables (𝕜) (A : Type*)

instance [semi_normed_ring A] : normed_ring (completion A) :=
{ dist_eq := λ x y,
  begin
    apply completion.induction_on₂ x y; clear x y,
    { refine is_closed_eq (completion.uniform_continuous_extension₂ _).continuous _,
      exact continuous.comp completion.continuous_extension continuous_sub },
    { intros x y,
      rw [← completion.coe_sub, norm_coe, completion.dist_eq, dist_eq_norm] }
  end,
  norm_mul := λ x y,
  begin
    apply completion.induction_on₂ x y; clear x y,
    { exact is_closed_le (continuous.comp (continuous_norm) continuous_mul) (continuous.comp
        real.continuous_mul (continuous.prod_map continuous_norm continuous_norm)) },
    { intros x y,
      simp only [← coe_mul, norm_coe], exact norm_mul_le x y, }
  end,
  ..completion.ring,
  ..completion.metric_space }

instance [semi_normed_comm_ring A] [normed_algebra 𝕜 A] [has_uniform_continuous_const_smul 𝕜 A] :
  normed_algebra 𝕜 (completion A) :=
{ norm_smul_le := λ r x,
  begin
    apply completion.induction_on x; clear x,
    { exact is_closed_le (continuous.comp (continuous_norm) (continuous_const_smul r))
      (continuous.comp (continuous_mul_left _) continuous_norm), },
    { intros x,
      simp only [← coe_smul, norm_coe], exact norm_smul_le r x }
  end,
  ..completion.algebra A 𝕜}

end algebra

end completion
end uniform_space
