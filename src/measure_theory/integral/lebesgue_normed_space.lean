/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.integral.lebesgue
import analysis.normed_space.basic

/-! # A lemma about measurability with density under scalar multiplication in normed spaces -/

open measure_theory filter ennreal set
open_locale nnreal ennreal
variables {α β γ δ : Type*} {m : measurable_space α} {μ : measure_theory.measure α}

lemma ae_measurable_with_density_iff {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
  {f : α → ℝ≥0} (hf : measurable f) {g : α → E} :
  ae_measurable g (μ.with_density (λ x, (f x : ℝ≥0∞))) ↔ ae_measurable (λ x, (f x : ℝ) • g x) μ :=
begin
  split,
  { rintros ⟨g', g'meas, hg'⟩,
    have A : measurable_set {x : α | f x ≠ 0} := (hf (measurable_set_singleton 0)).compl,
    refine ⟨λ x, (f x : ℝ) • g' x, hf.coe_nnreal_real.smul g'meas, _⟩,
    apply @ae_of_ae_restrict_of_ae_restrict_compl _ _ _ {x | f x ≠ 0},
    { rw [eventually_eq, ae_with_density_iff hf.coe_nnreal_ennreal] at hg',
      rw ae_restrict_iff' A,
      filter_upwards [hg'],
      assume a ha h'a,
      have : (f a : ℝ≥0∞) ≠ 0, by simpa only [ne.def, coe_eq_zero] using h'a,
      rw ha this },
    { filter_upwards [ae_restrict_mem A.compl],
      assume x hx,
      simp only [not_not, mem_set_of_eq, mem_compl_iff] at hx,
      simp [hx] } },
  { rintros ⟨g', g'meas, hg'⟩,
    refine ⟨λ x, (f x : ℝ)⁻¹ • g' x, hf.coe_nnreal_real.inv.smul g'meas, _⟩,
    rw [eventually_eq, ae_with_density_iff hf.coe_nnreal_ennreal],
    filter_upwards [hg'],
    assume x hx h'x,
    rw [← hx, smul_smul, _root_.inv_mul_cancel, one_smul],
    simp only [ne.def, coe_eq_zero] at h'x,
    simpa only [nnreal.coe_eq_zero, ne.def] using h'x }
end
