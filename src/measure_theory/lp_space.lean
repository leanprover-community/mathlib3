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
  unfold snorm,
  rw [←ennreal.rpow_mul, one_div, inv_mul_cancel, ennreal.rpow_one],
  symmetry, exact ne_of_lt hp0_lt,
end

end ℒp_space_definition

lemma mem_ℒp_one_iff_integrable : ∀ f : α → E, mem_ℒp f 1 μ ↔ integrable f μ :=
begin
  intro f,
  unfold integrable, unfold has_finite_integral, unfold mem_ℒp,
  simp only [ennreal.rpow_one, nnreal.coe_one],
end

section top

lemma snorm_lt_top {f : α → E} (hp0 : 0 ≤ p) (hfp : mem_ℒp f p μ) : snorm f p μ < ⊤ :=
begin
  unfold snorm,
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
begin
  split,
  exact hfm,
  exact lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top hp0_lt hfp,
end

end top

section zero

lemma lintegral_rpow_nnnorm_zero (hp0_lt : 0 < p) : ∫⁻ a, (nnnorm ((0 : α → F) a))^p ∂μ = 0 :=
begin
  simp_rw pi.zero_apply,
  rw [nnnorm_zero, lintegral_const, mul_eq_zero],
  left,
  exact ennreal.zero_rpow_of_pos hp0_lt,
end

lemma zero_mem_ℒp (hp0_lt : 0 < p): mem_ℒp (0 : α → E) p μ :=
begin
  split,
  exact measurable_zero,
  exact lt_of_le_of_lt (le_of_eq (lintegral_rpow_nnnorm_zero hp0_lt)) with_top.zero_lt_top,
end

lemma snorm_zero (hp0_lt : 0 < p): snorm (0 : α → F) p μ = 0 :=
begin
  have h : ∫⁻ a, (nnnorm ((0 : α → F) a))^(p : ℝ) ∂μ = 0,
  from lintegral_rpow_nnnorm_zero hp0_lt,
  unfold snorm,
  rw [h, ennreal.rpow_eq_zero_iff],
  left,
  split,
  refl,
  rw [one_div, inv_pos], exact hp0_lt,
end

end zero

end ℒp_space
