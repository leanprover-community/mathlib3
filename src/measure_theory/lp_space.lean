/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rémy Degenne.
-/
import measure_theory.l1_space
import analysis.special_functions.pow
import analysis.convex.specific_functions

/-!
# ℒp space

This file describes properties of measurable functions with finite seminorm `(∫ ∥f a∥^p ∂μ) ^ (1/p)`
for `p:ℝ` with `1 ≤ p`.

## Main definitions

* `mem_ℒp f p μ` : the function `f` has finite p-seminorm for measure `μ`, for `p:ℝ` such that
                  `hp1 : 1 ≤ p`,

## Notation

* `snorm f p μ` : `(∫ ∥f a∥^p ∂μ) ^ (1/p)` for `f : α → F`, where `α` is a  measurable space and
                  `F` is a normed group.

-/

open measure_theory

noncomputable theory

section measurability_lemmas
variables {α E : Type*} [measurable_space α] [measurable_space E] [normed_group E]
  [opens_measurable_space E]

lemma measurable.rpow_coe_nnnorm {f : α → E} {p : ℝ} (hp0 : 0 ≤ p) (hf : measurable f) :
  measurable (λ (a : α), (nnnorm (f a) : ennreal) ^ p) :=
begin
  simp_rw ennreal.coe_rpow_of_nonneg _ hp0,
  exact (nnreal.measurable_rpow_const.comp (measurable_nnnorm.comp hf)).ennreal_coe,
end

end measurability_lemmas

namespace ℒp_space

variables {α E F : Type*} [measurable_space α] {μ : measure α}
  [measurable_space E] [normed_group E]
  [normed_group F]
  {p : ℝ}

section ℒp_space_definition

/-- The property that `f:α→E` is measurable and `∫ ∥f a∥^p ∂μ` is finite -/
def mem_ℒp (f : α → E) (p : ℝ) (μ : measure α) : Prop :=
measurable f ∧ ∫⁻ a, (nnnorm (f a)) ^ p ∂μ < ⊤

/-- `(∫ ∥f a∥^p ∂μ) ^ (1/p)`, which is a seminorm on the space of measurable functions for which
this quantity is finite -/
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

lemma mem_ℒp.snorm_lt_top {f : α → E} (hp0 : 0 ≤ p) (hfp : mem_ℒp f p μ) : snorm f p μ < ⊤ :=
begin
  refine ennreal.rpow_lt_top_of_nonneg _ (ne_of_lt hfp.right),
  rw [one_div, inv_nonneg],
  exact hp0,
end

lemma mem_ℒp.snorm_ne_top {f : α → E} (hp0 : 0 ≤ p) (hfp : mem_ℒp f p μ) : snorm f p μ ≠ ⊤ :=
ne_of_lt (hfp.snorm_lt_top hp0)

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

lemma zero_mem_ℒp (hp0_lt : 0 < p) : mem_ℒp (0 : α → E) p μ :=
⟨measurable_zero, by simp [hp0_lt]⟩

@[simp] lemma snorm_zero (hp0_lt : 0 < p) : snorm (0 : α → F) p μ = 0 :=
by simp [snorm, hp0_lt]

end zero

@[simp] lemma snorm_neg {f : α → F} : snorm (-f) p μ = snorm f p μ :=
by simp [snorm]


section borel_space
variable [borel_space E]

lemma mem_ℒp.neg_mem_ℒp {f : α → E} (hf : mem_ℒp f p μ) : mem_ℒp (-f) p μ :=
⟨measurable.neg hf.1, by simp [hf.right]⟩


variable [topological_space.second_countable_topology E]

lemma rpow_nnnorm_add_le_const_mul_add_rpow_nnnorm {β} {f g : β → F} (hp1 : 1 ≤ p) (a : β) :
  (nnnorm (f a + g a)) ^ p ≤ 2 ^ (p - 1) * ((nnnorm (f a)) ^ p + (nnnorm (g a)) ^ p):=
begin
  have hp0_lt : 0 < p, from lt_of_lt_of_le zero_lt_one hp1,
  have h_zero_lt_half : (0 : nnreal) < 1 / 2, by simp [zero_lt_one],
  have h_zero_lt_half_rpow : (0 : nnreal) < (1 / 2) ^ p,
  { rw [←nnreal.zero_rpow (ne_of_lt hp0_lt).symm, nnreal.rpow_lt_rpow_iff hp0_lt],
    exact h_zero_lt_half, },
  have h_rw : (1 / 2) ^ p * (2:nnreal) ^ (p - 1) = 1 / 2,
  { rw [nnreal.rpow_sub two_ne_zero, nnreal.div_rpow, nnreal.one_rpow, nnreal.rpow_one,
      ←mul_div_assoc, one_div, inv_mul_cancel],
    simp [two_ne_zero], },
  rw [←mul_le_mul_left h_zero_lt_half_rpow, mul_add, mul_add, ← mul_assoc, ← mul_assoc, h_rw,
    ←nnreal.mul_rpow],
  refine le_trans _ _,
  exact ((1/2) * (nnnorm (f a)) + (1/2) * (nnnorm (g a))) ^ p,
  { refine nnreal.rpow_le_rpow _ (le_of_lt hp0_lt),
    rw [← mul_add, mul_le_mul_left h_zero_lt_half],
    exact nnnorm_add_le (f a) (g a), },
  -- go from nnreal to ℝ to use convexity (which is not defined for nnreal)
  suffices h_R :
    (((1 / (2:nnreal)) * nnnorm (f a) + (1 / (2:nnreal)) * nnnorm (g a)) ^ p).val
    ≤ ((1 / (2:nnreal)) * nnnorm (f a) ^ p + (1 / (2:nnreal)) * nnnorm (g a) ^ p).val,
  from h_R,
  simp only [one_div, nnreal.val_eq_coe, nnreal.coe_inv, nnreal.coe_add, coe_nnnorm,
    nnreal.coe_rpow, nnreal.coe_one, nnreal.coe_bit0, nnreal.coe_mul],
  -- use convexity of rpow
  repeat {rw ←smul_eq_mul},
  refine (convex_on_rpow hp1).right (norm_nonneg (f a)) (norm_nonneg (g a)) _ _ _,
  simp [zero_le_two],
  simp [zero_le_two],
  ring,
end

lemma mem_ℒp.add_mem_ℒp {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) (hp1 : 1 ≤ p) :
  mem_ℒp (f+g) p μ :=
begin
  have hp0 : 0 ≤ p, from le_trans zero_le_one hp1,
  have hp0_sub1 : 0 ≤ p - 1, by { rw sub_nonneg, exact hp1, },
  split,
  { exact measurable.add hf.1 hg.1, },
  simp_rw pi.add_apply,
  refine lt_of_le_of_lt _ _,
  exact ∫⁻ a, (2^(p-1) * (nnnorm (f a) : ennreal) ^ p + 2^(p-1) * (nnnorm (g a) : ennreal) ^ p) ∂ μ,
  { refine lintegral_mono _,
    intro a,
    simp_rw [←@ennreal.coe_two, ennreal.coe_rpow_of_nonneg _ hp0,
      ennreal.coe_rpow_of_nonneg _ hp0_sub1, ←ennreal.coe_mul, ←ennreal.coe_add,
      ennreal.coe_le_coe, ←mul_add],
    exact rpow_nnnorm_add_le_const_mul_add_rpow_nnnorm hp1 a, },
  { rw [lintegral_add, lintegral_const_mul, lintegral_const_mul, ennreal.add_lt_top],
    split; rw ennreal.mul_lt_top_iff; left;
      { split,
        exact ennreal.rpow_lt_top_of_nonneg hp0_sub1 ennreal.coe_ne_top,
        try { exact hf.2, },
        try { exact hg.2, }, },
    -- finish by proving the measurability of all functions involved
    exact hg.left.rpow_coe_nnnorm hp0,
    exact hf.left.rpow_coe_nnnorm hp0,
    exact (ennreal.continuous_const_mul (by simp)).measurable.comp (hf.1.rpow_coe_nnnorm hp0),
    exact (ennreal.continuous_const_mul (by simp)).measurable.comp (hg.1.rpow_coe_nnnorm hp0), },
end

end borel_space

end ℒp_space
