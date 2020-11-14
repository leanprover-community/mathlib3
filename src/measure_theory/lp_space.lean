/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rémy Degenne.
-/
import measure_theory.l1_space
import analysis.special_functions.pow

/-!
# ℒp space

This file describes properties of measurable functions with finite seminorm
`(∫⁻ a, (nnnorm (f a))^(p : ℝ) ∂μ) ^ (1/p)` for `p:ℝ` with `1 ≤ p`.

## Main definitions

* `mem_ℒp f p μ` : the function `f` has finite p-seminorm for measure `μ`, for `p:ℝ` such that
                  `hp1 : 1 ≤ p`,

## Notation

* `snorm f p μ` : `(∫⁻ a, (nnnorm (f a)) ^ p ∂μ) ^ (1/p)` for `f : α → F`, where `α` is a
  measurable space and `F` is a normed group.

-/

open measure_theory

noncomputable theory

namespace ℒp_space

variables {α E F: Type*} [measurable_space α] {μ : measure α}
  [measurable_space E] [normed_group E]
  [normed_group F]
  {p : ℝ}

section ℒp_space_definition

/-- The property that `f:α→E` is measurable and `∫⁻ a, (nnnorm (f a)) ^ p ∂μ` is finite -/
def mem_ℒp (f : α → E) (p : ℝ) (μ : measure α) : Prop :=
measurable f ∧ ∫⁻ a, (nnnorm (f a)) ^ p ∂μ < ⊤

/-- `(∫⁻ a, (nnnorm (f a))^p ∂μ) ^ (1/p)`, which is a seminorm on the space of measurable
functions for which this quantity is finite -/
def snorm (f : α → F) (p : ℝ) (μ : measure α) : ennreal := (∫⁻ a, (nnnorm (f a))^p ∂μ) ^ (1/p)

lemma lintegral_rpow_nnnorm_eq_rpow_snorm {f : α → F} (hp0_lt : 0 < p) :
  ∫⁻ a, (nnnorm (f a)) ^ p ∂μ = (snorm f p μ) ^ p :=
begin
  rw [snorm, ←ennreal.rpow_mul, one_div, inv_mul_cancel, ennreal.rpow_one],
  exact (ne_of_lt hp0_lt).symm,
end

end ℒp_space_definition

lemma mem_ℒp_one_iff_integrable {f : α → E} : mem_ℒp f 1 μ ↔ integrable f μ :=
by simp only [integrable, has_finite_integral, mem_ℒp, ennreal.rpow_one, nnreal.coe_one]

section top

lemma snorm_lt_top {f : α → E} (hp0 : 0 ≤ p) (hfp : mem_ℒp f p μ) : snorm f p μ < ⊤ :=
begin
  refine ennreal.rpow_lt_top_of_nonneg _ (ne_of_lt hfp.right),
  rw [one_div, inv_nonneg],
  exact hp0,
end

lemma snorm_ne_top {f : α → E} (hp0 : 0 ≤ p) (hfp : mem_ℒp f p μ) : snorm f p μ ≠ ⊤ :=
ne_of_lt (snorm_lt_top hp0 hfp)

lemma lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top {f : α → F} (hp0_lt : 0 < p)
  (hfp : snorm f p μ < ⊤) :
  ∫⁻ a, (nnnorm (f a)) ^ p ∂μ < ⊤ :=
begin
  rw lintegral_rpow_nnnorm_eq_rpow_snorm hp0_lt,
  exact ennreal.rpow_lt_top_of_nonneg (le_of_lt hp0_lt) (ne_of_lt hfp),
end

lemma mem_ℒp_of_snorm_lt_top {f : α → E} (hp0_lt : 0 < p) (hfm : measurable f)
  (hfp : snorm f p μ < ⊤) :
  mem_ℒp f p μ :=
⟨hfm, lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top hp0_lt hfp⟩

end top

section zero

lemma zero_mem_ℒp (hp0_lt : 0 < p): mem_ℒp (0 : α → E) p μ :=
⟨measurable_zero, by simp [hp0_lt]⟩

@[simp] lemma snorm_zero (hp0_lt : 0 < p) : snorm (0 : α → F) p μ = 0 :=
by simp [snorm, hp0_lt]

end zero

end ℒp_space
