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

* `snorm f p μ` : `(∫⁻ a, (nnnorm (f a))^(p : ℝ) ∂μ) ^ (1/p)` for `f : α → β`

-/

open measure_theory

noncomputable theory

namespace ℒp_space

variables {α β γ: Type*} [measurable_space α] {μ : measure α}
  [measurable_space β] [normed_group β]
  [normed_group γ]
  {p : ℝ}

section ℒp_space_definition

/-- The property that f belongs to ℒp for measure μ and real p -/
def mem_ℒp (f : α → β) (p : ℝ) (μ : measure α) : Prop :=
measurable f ∧ ∫⁻ a, (nnnorm (f a)) ^ p ∂μ < ⊤

/-- seminorm on ℒp -/
def snorm (f : α → γ) (p : ℝ) (μ : measure α) : ennreal := (∫⁻ a, (nnnorm (f a))^p ∂μ) ^ (1/p)

end ℒp_space_definition

lemma mem_ℒp_one_iff_integrable : ∀ f : α → β, mem_ℒp f 1 μ ↔ integrable f μ :=
begin
  intro f,
  unfold integrable, unfold has_finite_integral, unfold mem_ℒp,
  simp only [ennreal.rpow_one, nnreal.coe_one],
end

section top

lemma snorm_lt_top {f : α → β} (hp0 : 0 ≤ p) (hfp : mem_ℒp f p μ) : snorm f p μ < ⊤ :=
begin
  unfold snorm,
  refine ennreal.rpow_lt_top_of_nonneg _ (ne_of_lt hfp.right),
  rw [one_div, inv_nonneg],
  exact hp0,
end

lemma snorm_ne_top {f : α → β} (hp0 : 0 ≤ p) (hfp : mem_ℒp f p μ) : snorm f p μ ≠ ⊤ :=
ne_of_lt (snorm_lt_top hp0 hfp)

lemma lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top {f : α → γ} (hp0_lt : 0 < p)
  (hfp : snorm f p μ < ⊤) :
  ∫⁻ a, (nnnorm (f a)) ^ p ∂μ < ⊤ :=
begin
  have h_top_eq : (⊤ : ennreal) = ⊤ ^ (1/p),
  { symmetry, rw ennreal.rpow_eq_top_iff, right, split,
    refl,
    simp only [one_div, inv_pos], exact hp0_lt, },
  rw h_top_eq at hfp,
  unfold snorm at hfp,
  have h_seminorm_rpow : ((∫⁻ (a : α), ↑(nnnorm (f a)) ^ p ∂μ) ^ (1 / p))^p < (⊤ ^ (1 / p))^p,
  { exact ennreal.rpow_lt_rpow hfp hp0_lt, },
  rw [←ennreal.rpow_mul, ←ennreal.rpow_mul] at h_seminorm_rpow,
  simp_rw one_div at h_seminorm_rpow,
  simp_rw inv_mul_cancel (ne_of_lt hp0_lt).symm at h_seminorm_rpow,
  simp_rw ennreal.rpow_one at h_seminorm_rpow,
  exact h_seminorm_rpow,
end

lemma mem_ℒp_of_snorm_lt_top {f : α → β} (hp0_lt : 0 < p) (hfm : measurable f)
  (hfp : snorm f p μ < ⊤) :
  mem_ℒp f p μ :=
begin
  split,
  exact hfm,
  exact lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top hp0_lt hfp,
end

end top

section zero

lemma lintegral_rpow_nnnorm_zero (hp0_lt : 0 < p) : ∫⁻ a, (nnnorm ((0 : α → γ) a))^p ∂μ = 0 :=
begin
  simp_rw pi.zero_apply,
  rw [nnnorm_zero, lintegral_const, mul_eq_zero],
  left,
  exact ennreal.zero_rpow_of_pos hp0_lt,
end

lemma zero_mem_ℒp (hp0_lt : 0 < p): mem_ℒp (0 : α → β) p μ :=
begin
  split,
  exact measurable_zero,
  exact lt_of_le_of_lt (le_of_eq (lintegral_rpow_nnnorm_zero hp0_lt)) with_top.zero_lt_top,
end

lemma snorm_zero (hp0_lt : 0 < p): snorm (0 : α → γ) p μ = 0 :=
begin
  have h : ∫⁻ a, (nnnorm ((0 : α → γ) a))^(p : ℝ) ∂μ = 0,
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
