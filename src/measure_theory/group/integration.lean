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
  [measurable_space E] [borel_space E] {f : G → E} {g : G}

section measurable_mul

variables [group G] [has_measurable_mul G]

--todo
@[simp] lemma map_id' : map (λ x, x) μ = μ := map_id
variables {α : Type*} [measurable_space α]
lemma integral_norm_eq_lintegral_nnnorm {f : α → G} (hf : ae_measurable f μ) :
  ∫ x, ∥f x∥ ∂μ = ennreal.to_real ∫⁻ x, ∥f x∥₊ ∂μ :=
begin
  rw integral_eq_lintegral_of_nonneg_ae _ hf.norm,
  { simp_rw [of_real_norm_eq_coe_nnnorm], },
  { refine ae_of_all _ _, simp_rw [pi.zero_apply, norm_nonneg, imp_true_iff] },
end

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
lemma integral_zero_of_mul_left_eq_neg [is_mul_left_invariant μ] (hf' : ∀ x, f (g * x) = - f x) :
  ∫ x, f x ∂μ = 0 :=
by { refine eq_zero_of_eq_neg ℝ _, simp_rw [← integral_neg, ← hf', integral_mul_left_eq_self] }

/-- If some right-translate of a function negates it, then the integral of the function with respect
to a right-invariant measure is 0. -/
@[to_additive]
lemma integral_zero_of_mul_right_eq_neg [is_mul_right_invariant μ] (hf' : ∀ x, f (x * g) = - f x) :
  ∫ x, f x ∂μ = 0 :=
by { refine eq_zero_of_eq_neg ℝ _, simp_rw [← integral_neg, ← hf', integral_mul_right_eq_self] }

@[to_additive]
lemma integrable.comp_div_left [has_measurable_inv G] [is_inv_invariant μ] [is_mul_left_invariant μ]
  (hf : integrable f μ) (g : G) : integrable (λ t, f (g / t)) μ :=
begin
  rw [← map_mul_right_inv_eq_self μ g⁻¹, integrable_map_measure, function.comp],
  { simp_rw [div_inv_eq_mul, mul_inv_cancel_left], exact hf },
  { refine ae_measurable.comp_measurable _ (measurable_id.const_div g),
    simp_rw [map_map (measurable_id'.const_div g) (measurable_id'.const_mul g⁻¹).inv,
      function.comp, div_inv_eq_mul, mul_inv_cancel_left, map_id'],
    exact hf.ae_measurable },
  exact (measurable_id'.const_mul g⁻¹).inv
end

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
