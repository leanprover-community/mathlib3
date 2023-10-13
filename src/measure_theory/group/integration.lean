/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.integral.bochner
import measure_theory.group.measure
import measure_theory.group.action

/-!
# Integration on Groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We develop properties of integrals with a group as domain.
This file contains properties about integrability, Lebesgue integration and Bochner integration.
-/

namespace measure_theory

open measure topological_space
open_locale ennreal

variables {𝕜 M α G E F : Type*} [measurable_space G]
variables [normed_add_comm_group E] [normed_space ℝ E] [complete_space E] [normed_add_comm_group F]
variables {μ : measure G} {f : G → E} {g : G}

section measurable_inv

variables [group G] [has_measurable_inv G]

@[to_additive]
lemma integrable.comp_inv [is_inv_invariant μ] {f : G → F} (hf : integrable f μ) :
  integrable (λ t, f t⁻¹) μ :=
(hf.mono_measure (map_inv_eq_self μ).le).comp_measurable measurable_inv

@[to_additive]
lemma integral_inv_eq_self (f : G → E) (μ : measure G) [is_inv_invariant μ] :
  ∫ x, f (x⁻¹) ∂μ = ∫ x, f x ∂μ :=
begin
  have h : measurable_embedding (λ x : G, x⁻¹) :=
  (measurable_equiv.inv G).measurable_embedding,
  rw [← h.integral_map, map_inv_eq_self]
end

end measurable_inv

section measurable_mul

variables [group G] [has_measurable_mul G]

/-- Translating a function by left-multiplication does not change its `measure_theory.lintegral`
with respect to a left-invariant measure. -/
@[to_additive "Translating a function by left-addition does not change its
`measure_theory.lintegral` with respect to a left-invariant measure."]
lemma lintegral_mul_left_eq_self [is_mul_left_invariant μ] (f : G → ℝ≥0∞) (g : G) :
  ∫⁻ x, f (g * x) ∂μ = ∫⁻ x, f x ∂μ :=
begin
  convert (lintegral_map_equiv f $ measurable_equiv.mul_left g).symm,
  simp [map_mul_left_eq_self μ g]
end

/-- Translating a function by right-multiplication does not change its `measure_theory.lintegral`
with respect to a right-invariant measure. -/
@[to_additive "Translating a function by right-addition does not change its
`measure_theory.lintegral` with respect to a right-invariant measure."]
lemma lintegral_mul_right_eq_self [is_mul_right_invariant μ] (f : G → ℝ≥0∞) (g : G) :
  ∫⁻ x, f (x * g) ∂μ = ∫⁻ x, f x ∂μ :=
begin
  convert (lintegral_map_equiv f $ measurable_equiv.mul_right g).symm,
  simp [map_mul_right_eq_self μ g]
end

@[simp, to_additive]
lemma lintegral_div_right_eq_self [is_mul_right_invariant μ] (f : G → ℝ≥0∞) (g : G) :
  ∫⁻ x, f (x / g) ∂μ = ∫⁻ x, f x ∂μ :=
by simp_rw [div_eq_mul_inv, lintegral_mul_right_eq_self f g⁻¹]

/-- Translating a function by left-multiplication does not change its integral with respect to a
left-invariant measure. -/
@[simp, to_additive "Translating a function by left-addition does not change its integral with
  respect to a left-invariant measure."]
lemma integral_mul_left_eq_self [is_mul_left_invariant μ] (f : G → E) (g : G) :
  ∫ x, f (g * x) ∂μ = ∫ x, f x ∂μ :=
begin
  have h_mul : measurable_embedding (λ x, g * x) :=
    (measurable_equiv.mul_left g).measurable_embedding,
  rw [← h_mul.integral_map, map_mul_left_eq_self]
end

/-- Translating a function by right-multiplication does not change its integral with respect to a
right-invariant measure. -/
@[simp, to_additive "Translating a function by right-addition does not change its integral with
  respect to a right-invariant measure."]
lemma integral_mul_right_eq_self [is_mul_right_invariant μ] (f : G → E) (g : G) :
  ∫ x, f (x * g) ∂μ = ∫ x, f x ∂μ :=
begin
  have h_mul : measurable_embedding (λ x, x * g) :=
    (measurable_equiv.mul_right g).measurable_embedding,
  rw [← h_mul.integral_map, map_mul_right_eq_self]
end

@[simp, to_additive]
lemma integral_div_right_eq_self [is_mul_right_invariant μ] (f : G → E) (g : G) :
  ∫ x, f (x / g) ∂μ = ∫ x, f x ∂μ :=
by simp_rw [div_eq_mul_inv, integral_mul_right_eq_self f g⁻¹]

/-- If some left-translate of a function negates it, then the integral of the function with respect
to a left-invariant measure is 0. -/
@[to_additive "If some left-translate of a function negates it, then the integral of the function
with respect to a left-invariant measure is 0."]
lemma integral_eq_zero_of_mul_left_eq_neg [is_mul_left_invariant μ] (hf' : ∀ x, f (g * x) = - f x) :
  ∫ x, f x ∂μ = 0 :=
by simp_rw [← self_eq_neg ℝ E, ← integral_neg, ← hf', integral_mul_left_eq_self]

/-- If some right-translate of a function negates it, then the integral of the function with respect
to a right-invariant measure is 0. -/
@[to_additive "If some right-translate of a function negates it, then the integral of the function
with respect to a right-invariant measure is 0."]
lemma integral_eq_zero_of_mul_right_eq_neg [is_mul_right_invariant μ]
  (hf' : ∀ x, f (x * g) = - f x) : ∫ x, f x ∂μ = 0 :=
by simp_rw [← self_eq_neg ℝ E, ← integral_neg, ← hf', integral_mul_right_eq_self]

@[to_additive]
lemma integrable.comp_mul_left {f : G → F} [is_mul_left_invariant μ] (hf : integrable f μ)
  (g : G) : integrable (λ t, f (g * t)) μ :=
(hf.mono_measure (map_mul_left_eq_self μ g).le).comp_measurable $ measurable_const_mul g

@[to_additive]
lemma integrable.comp_mul_right {f : G → F} [is_mul_right_invariant μ] (hf : integrable f μ)
  (g : G) : integrable (λ t, f (t * g)) μ :=
(hf.mono_measure (map_mul_right_eq_self μ g).le).comp_measurable $ measurable_mul_const g

@[to_additive]
lemma integrable.comp_div_right {f : G → F} [is_mul_right_invariant μ] (hf : integrable f μ)
  (g : G) : integrable (λ t, f (t / g)) μ :=
by { simp_rw [div_eq_mul_inv], exact hf.comp_mul_right g⁻¹ }

variables [has_measurable_inv G]

@[to_additive]
lemma integrable.comp_div_left {f : G → F}
  [is_inv_invariant μ] [is_mul_left_invariant μ] (hf : integrable f μ) (g : G) :
  integrable (λ t, f (g / t)) μ :=
((measure_preserving_div_left μ g).integrable_comp hf.ae_strongly_measurable).mpr hf

@[simp, to_additive]
lemma integrable_comp_div_left (f : G → F)
  [is_inv_invariant μ] [is_mul_left_invariant μ] (g : G) :
  integrable (λ t, f (g / t)) μ ↔ integrable f μ :=
begin
  refine ⟨λ h, _, λ h, h.comp_div_left g⟩,
  convert h.comp_inv.comp_mul_left g⁻¹,
  simp_rw [div_inv_eq_mul, mul_inv_cancel_left]
end

@[simp, to_additive]
lemma integral_div_left_eq_self (f : G → E) (μ : measure G) [is_inv_invariant μ]
  [is_mul_left_invariant μ] (x' : G) : ∫ x, f (x' / x) ∂μ = ∫ x, f x ∂μ :=
by simp_rw [div_eq_mul_inv, integral_inv_eq_self (λ x, f (x' * x)) μ,
  integral_mul_left_eq_self f x']

end measurable_mul

section smul

variables [group G] [measurable_space α] [mul_action G α] [has_measurable_smul G α]

@[simp, to_additive]
lemma integral_smul_eq_self {μ : measure α} [smul_invariant_measure G α μ] (f : α → E) {g : G} :
  ∫ x, f (g • x) ∂μ = ∫ x, f x ∂μ :=
begin
  have h : measurable_embedding (λ x : α, g • x) :=
  (measurable_equiv.smul g).measurable_embedding,
  rw [← h.integral_map, map_smul]
end

end smul

section topological_group

variables [topological_space G] [group G] [topological_group G] [borel_space G]
  [is_mul_left_invariant μ]

/-- For nonzero regular left invariant measures, the integral of a continuous nonnegative function
  `f` is 0 iff `f` is 0. -/
@[to_additive "For nonzero regular left invariant measures, the integral of a continuous nonnegative
function `f` is 0 iff `f` is 0."]
lemma lintegral_eq_zero_of_is_mul_left_invariant [regular μ] (hμ : μ ≠ 0)
  {f : G → ℝ≥0∞} (hf : continuous f) :
  ∫⁻ x, f x ∂μ = 0 ↔ f = 0 :=
begin
  haveI := is_open_pos_measure_of_mul_left_invariant_of_regular hμ,
  rw [lintegral_eq_zero_iff hf.measurable, hf.ae_eq_iff_eq μ continuous_zero]
end

end topological_group

end measure_theory
