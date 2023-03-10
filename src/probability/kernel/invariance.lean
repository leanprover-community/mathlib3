/-
Copyright (c) 2023 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.kernel.composition

/-!
# Invariance of measures along a kernel

We define the push-forward of a measure along a kernel which results in another measure. In the
case that the push-forward measure is the same as the original measure, we say that the measure is
invariant with respect to the kernel. This notion is useful if we want to talk about invariant
measures of a Markov kernel.

## Main definitions

* `probability_theory.kernel.map_measure`: the push-forward of a measure along a kernel.
* `probability_theory.kernel.invariant`: invariance of a given measure with respect to a kernel.

## Useful lemmas

* `probability_theory.kernel.comp_apply_eq_map_measure`,
  `probability_theory.kernel.const_map_measure_eq_comp_const`, and
  `probability_theory.kernel.comp_const_apply_eq_map_measure` established the relationship between
  the push-forward measure and the composition of kernels.

-/

open measure_theory

open_locale measure_theory ennreal big_operators probability_theory

namespace probability_theory

variables {α β γ : Type*} {mα : measurable_space α} {mβ : measurable_space β}
  {mγ : measurable_space γ}

include mα mβ

namespace kernel

/-- The push-forward of a measure along a kernel. -/
noncomputable
def map_measure (κ : kernel α β) (μ : measure α) :
  measure β :=
measure.of_measurable (λ s hs, ∫⁻ x, κ x s ∂μ)
  (by simp only [measure_empty, lintegral_const, zero_mul])
  begin
    intros f hf₁ hf₂,
    simp_rw [measure_Union hf₂ hf₁,
      lintegral_tsum (λ i, (kernel.measurable_coe κ (hf₁ i)).ae_measurable)],
  end

@[simp]
lemma map_measure_apply (κ : kernel α β) (μ : measure α) {s : set β} (hs : measurable_set s) :
  map_measure κ μ s = ∫⁻ x, κ x s ∂μ :=
by rw [map_measure, measure.of_measurable_apply s hs]

@[simp]
lemma map_measure_zero (κ : kernel α β) : map_measure κ 0 = 0 :=
begin
  ext1 s hs,
  rw [map_measure_apply κ 0 hs, lintegral_zero_measure, measure.coe_zero, pi.zero_apply],
end

@[simp]
lemma map_measure_add  (κ : kernel α β) (μ ν : measure α) :
  map_measure κ (μ + ν) = map_measure κ μ + map_measure κ ν :=
begin
  ext1 s hs,
  rw [map_measure_apply κ (μ + ν) hs, lintegral_add_measure, measure.coe_add, pi.add_apply,
    map_measure_apply κ μ hs, map_measure_apply κ ν hs],
end

@[simp]
lemma map_measure_smul (κ : kernel α β) (μ : measure α) (r : ℝ≥0∞) :
  map_measure κ (r • μ) = r • map_measure κ μ :=
begin
  ext1 s hs,
  rw [map_measure_apply κ (r • μ) hs, lintegral_smul_measure, measure.coe_smul, pi.smul_apply,
    map_measure_apply κ μ hs, smul_eq_mul],
end

include mγ

lemma comp_apply_eq_map_measure
  (η : kernel β γ) [is_s_finite_kernel η] (κ : kernel α β) [is_s_finite_kernel κ] (a : α) :
  (η ∘ₖ κ) a = map_measure η (κ a) :=
begin
  ext1 s hs,
  rw [comp_apply η κ a hs, map_measure_apply η _ hs],
end

omit mγ

lemma const_map_measure_eq_comp_const (κ : kernel α β) [is_s_finite_kernel κ]
  (μ : measure α) [is_finite_measure μ] :
  const α (map_measure κ μ) = κ ∘ₖ const α μ :=
begin
  ext1 a, ext1 s hs,
  rw [const_apply, map_measure_apply _ _ hs, comp_apply _ _ _ hs, const_apply],
end

lemma comp_const_apply_eq_map_measure (κ : kernel α β) [is_s_finite_kernel κ]
  (μ : measure α) [is_finite_measure μ] (a : α) :
  (κ ∘ₖ const α μ) a = map_measure κ μ :=
by rw [← const_apply (map_measure κ μ) a, const_map_measure_eq_comp_const κ μ]

lemma lintegral_map_measure_eq
  (κ : kernel α β) [is_s_finite_kernel κ] (μ : measure α) [is_finite_measure μ]
  {f : β → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ b, f b ∂(map_measure κ μ) = ∫⁻ a, ∫⁻ b, f b ∂(κ a) ∂μ :=
begin
  by_cases hα : nonempty α,
  { have := const_apply μ hα.some,
    swap, apply_instance,
    conv_rhs { rw [← this]  },
    rw [← lintegral_comp _ _ _ hf, ← comp_const_apply_eq_map_measure κ μ hα.some] },
  { haveI := not_nonempty_iff.1 hα,
    rw [μ.eq_zero_of_is_empty, map_measure_zero, lintegral_zero_measure,
      lintegral_zero_measure] }
end

omit mβ

/-! **Invariant measures of kernels** -/

/-- A measure `μ` is invariant with respect to the kernel `κ` if the push-forward measure of `μ`
along `κ` equals `μ`. -/
def invariant (κ : kernel α α) (μ : measure α) : Prop :=
map_measure κ μ = μ

variables {κ η : kernel α α} {μ : measure α}

lemma invariant.def (hκ : invariant κ μ) : map_measure κ μ = μ := hκ

lemma invariant.comp_const [is_s_finite_kernel κ] [is_finite_measure μ]
  (hκ : invariant κ μ) : (κ ∘ₖ const α μ) = const α μ :=
by rw [← const_map_measure_eq_comp_const κ μ, hκ.def]

lemma invariant.comp [is_s_finite_kernel κ] [is_s_finite_kernel η] [is_finite_measure μ]
  (hκ : invariant κ μ) (hη : invariant η μ) : invariant (κ ∘ₖ η) μ :=
begin
  by_cases hα : nonempty α,
  { simp_rw [invariant, ← comp_const_apply_eq_map_measure (κ ∘ₖ η) μ hα.some, comp_assoc,
      hη.comp_const, hκ.comp_const, const_apply] },
  { haveI := not_nonempty_iff.1 hα,
    exact measure.eq_of_is_empty _ _ },
end

end kernel

end probability_theory
