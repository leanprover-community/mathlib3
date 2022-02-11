/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.integral.bochner
import measure_theory.group.measure

/-!
# Integration on Groups

We develop properties of integrals with a group as domain.
This file contains properties about integrability, Lebesgue integration and Bochner integration.
-/

namespace measure_theory

open measure topological_space
open_locale ennreal

variables {𝕜 G E : Type*} [measurable_space G] {μ : measure G}
variables [normed_group E] [second_countable_topology E] [normed_space ℝ E] [complete_space E]
  [measurable_space E] [borel_space E]

section measurable_mul

variables [group G] [has_measurable_mul G]

/-- Translating a function by left-multiplication does not change its `lintegral` with respect to
a left-invariant measure. -/
@[to_additive]
lemma lintegral_mul_left_eq_self [is_mul_left_invariant μ] (f : G → ℝ≥0∞) (g : G) :
  ∫⁻ x, f (g * x) ∂μ = ∫⁻ x, f x ∂μ :=
begin
  convert (lintegral_map_equiv f $ measurable_equiv.mul_left g).symm,
  simp [map_mul_left_eq_self μ g]
end

/-- Translating a function by right-multiplication does not change its `lintegral` with respect to
a right-invariant measure. -/
@[to_additive]
lemma lintegral_mul_right_eq_self [is_mul_right_invariant μ] (f : G → ℝ≥0∞) (g : G) :
  ∫⁻ x, f (x * g) ∂μ = ∫⁻ x, f x ∂μ :=
begin
  convert (lintegral_map_equiv f $ measurable_equiv.mul_right g).symm,
  simp [map_mul_right_eq_self μ g]
end

/-- Translating a function by left-multiplication does not change its integral with respect to a
left-invariant measure. -/
@[to_additive]
lemma integral_mul_left_eq_self [is_mul_left_invariant μ] (f : G → E) (g : G) :
  ∫ x, f (g * x) ∂μ = ∫ x, f x ∂μ :=
begin
  have h_mul : measurable_embedding (λ x, g * x) :=
    (measurable_equiv.mul_left g).measurable_embedding,
  rw [← h_mul.integral_map, map_mul_left_eq_self]
end

/-- Translating a function by right-multiplication does not change its integral with respect to a
right-invariant measure. -/
@[to_additive]
lemma integral_mul_right_eq_self [is_mul_right_invariant μ] (f : G → E) (g : G) :
  ∫ x, f (x * g) ∂μ = ∫ x, f x ∂μ :=
begin
  have h_mul : measurable_embedding (λ x, x * g) :=
    (measurable_equiv.mul_right g).measurable_embedding,
  rw [← h_mul.integral_map, map_mul_right_eq_self]
end

/-- If some left-translate of a function negates it, then the integral of the function with respect
to a left-invariant measure is 0. -/
@[to_additive]
lemma integral_zero_of_mul_left_eq_neg [is_mul_left_invariant μ] {f : G → E} {g : G}
  (hf' : ∀ x, f (g * x) = - f x) :
  ∫ x, f x ∂μ = 0 :=
by simp_rw [← self_eq_neg ℝ E, ← integral_neg, ← hf', integral_mul_left_eq_self]

/-- If some right-translate of a function negates it, then the integral of the function with respect
to a right-invariant measure is 0. -/
@[to_additive]
lemma integral_zero_of_mul_right_eq_neg [is_mul_right_invariant μ] {f : G → E} {g : G}
  (hf' : ∀ x, f (x * g) = - f x) :
  ∫ x, f x ∂μ = 0 :=
by simp_rw [← self_eq_neg ℝ E, ← integral_neg, ← hf', integral_mul_right_eq_self]

end measurable_mul


section topological_group

variables [topological_space G] [group G] [topological_group G] [borel_space G]
  [is_mul_left_invariant μ]

/-- For nonzero regular left invariant measures, the integral of a continuous nonnegative function
  `f` is 0 iff `f` is 0. -/
@[to_additive]
lemma lintegral_eq_zero_of_is_mul_left_invariant [regular μ] (hμ : μ ≠ 0)
  {f : G → ℝ≥0∞} (hf : continuous f) :
  ∫⁻ x, f x ∂μ = 0 ↔ f = 0 :=
begin
  haveI := is_open_pos_measure_of_mul_left_invariant_of_regular hμ,
  rw [lintegral_eq_zero_iff hf.measurable, hf.ae_eq_iff_eq μ continuous_zero]
end

end topological_group

end measure_theory
