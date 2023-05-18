/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import analysis.normed_space.finite_dimension
import measure_theory.group.measure.basic

/-!
# Measures on Groups

We develop some properties of measures on (topological) groups

* We define properties on measures: measures that are left or right invariant w.r.t. multiplication.
* We define the measure `μ.inv : A ↦ μ(A⁻¹)` and show that it is right invariant iff
  `μ` is left invariant.
* We define a class `is_haar_measure μ`, requiring that the measure `μ` is left-invariant, finite
  on compact sets, and positive on open sets.

We also give analogues of all these notions in the additive world.
-/

noncomputable theory

open_locale nnreal ennreal pointwise big_operators topology
open has_inv set function measure_theory.measure filter

variables {𝕜 G H : Type*} [measurable_space G] [measurable_space H]

namespace measure_theory

section haar

namespace measure

section

variables [group G] [topological_space G] (μ : measure G) [is_haar_measure μ]

/- The above instance applies in particular to show that an additive Haar measure on a nontrivial
finite-dimensional real vector space has no atom. -/
example {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [nontrivial E]
  [finite_dimensional ℝ E] [measurable_space E] [borel_space E] (μ : measure E)
  [is_add_haar_measure μ] :
  has_no_atoms μ := by apply_instance

end

variables [nontrivially_normed_field 𝕜] [topological_space G] [topological_space H]
  [add_comm_group G] [add_comm_group H] [topological_add_group G] [topological_add_group H]
  [module 𝕜 G] [module 𝕜 H] (μ : measure G) [is_add_haar_measure μ] [borel_space G] [borel_space H]
  [t2_space H]

instance map_continuous_linear_equiv.is_add_haar_measure (e : G ≃L[𝕜] H) :
  is_add_haar_measure (μ.map e) :=
e.to_add_equiv.is_add_haar_measure_map _ e.continuous e.symm.continuous

variables [complete_space 𝕜] [t2_space G] [finite_dimensional 𝕜 G] [has_continuous_smul 𝕜 G]
  [has_continuous_smul 𝕜 H]

instance map_linear_equiv.is_add_haar_measure (e : G ≃ₗ[𝕜] H) : is_add_haar_measure (μ.map e) :=
map_continuous_linear_equiv.is_add_haar_measure _ e.to_continuous_linear_equiv

end measure
end haar

end measure_theory
