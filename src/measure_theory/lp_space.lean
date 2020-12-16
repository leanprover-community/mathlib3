/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rémy Degenne.
-/
import measure_theory.l1_space
import analysis.mean_inequalities

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

lemma mem_ℒp.neg {f : α → E} (hf : mem_ℒp f p μ) : mem_ℒp (-f) p μ :=
⟨measurable.neg hf.1, by simp [hf.right]⟩

lemma snorm_le_snorm_mul_rpow_measure_univ {p q : ℝ} (hp1 : 1 ≤ p) (hpq : p ≤ q) (μ : measure α)
  {f : α → E} (hf : measurable f) :
  snorm f p μ ≤ snorm f q μ * (μ set.univ) ^ (1/p - 1/q) :=
begin
  have hq1 : 1 ≤ q, from le_trans hp1 hpq,
  by_cases hpq_eq : p = q,
  { rw [hpq_eq, sub_self, ennreal.rpow_zero, mul_one], exact le_refl _, },
  have hpq : p < q, from lt_of_le_of_ne hpq hpq_eq,
  have hp0_lt : 0 < p, from lt_of_lt_of_le zero_lt_one hp1,
  have hp0_ne : p ≠ 0, from (ne_of_lt hp0_lt).symm,
  have hp0 : 0 ≤ p, from le_trans zero_le_one hp1,
  have hq0_lt : 0 < q, from lt_of_lt_of_le zero_lt_one hq1,
  let f_nnreal := λ a, (nnnorm(f a)) ^ p,
  let g_nnreal := λ a:α, (1:nnreal),
  have h_rw : ∫⁻ a, f_nnreal a ∂ μ = ∫⁻ a, ((f_nnreal * g_nnreal) a) ∂ μ,
  from lintegral_congr (λ a, by simp),
  repeat {rw snorm},
  simp_rw [ennreal.coe_rpow_of_nonneg _ hp0, h_rw],
  let p2 := q/p,
  let q2 := p2.conjugate_exponent,
  have hp2q2 : p2.is_conjugate_exponent q2,
  from real.is_conjugate_exponent_conjugate_exponent (by simp [lt_div_iff, hpq, hp0_lt]),
  have hq2 : q2 = q * (q - p)⁻¹,
  { change (q/p)/(q/p - 1) = q * (q - p)⁻¹,
    rw [←div_self hp0_ne, ←sub_div, div_eq_mul_one_div, one_div_div, div_eq_mul_inv, div_eq_mul_inv,
      mul_assoc],
    nth_rewrite 1 ←mul_assoc,
    rw [inv_mul_cancel hp0_ne, one_mul], },
  calc (∫⁻ (a : α), ↑((f_nnreal * g_nnreal) a) ∂μ) ^ (1 / p)
    ≤ ((∫⁻ a, (f_nnreal a)^p2 ∂ μ)^(1/p2)*(∫⁻ a, (g_nnreal a)^q2 ∂ μ)^(1/q2)) ^ (1/p) :
  begin
    refine ennreal.rpow_le_rpow _ (by simp [hp0]),
    exact nnreal.lintegral_mul_le_Lp_mul_Lq hp2q2 hf.nnnorm.nnreal_rpow_const measurable_const,
  end
    ... = (∫⁻ (a : α), ↑(nnnorm (f a)) ^ q ∂μ) ^ (1 / q) * μ set.univ ^ (1 / p - 1 / q) :
  begin
    have hpp2 : p * p2 = q,
    { symmetry, rw [mul_comm, ←div_eq_iff hp0_ne], },
    have h_int_g : ∫⁻ (a : α), ↑(g_nnreal a) ^ q2 ∂μ = μ set.univ, by simp,
    have h_int_f : ∫⁻ (a : α), ↑(f_nnreal a) ^ p2 ∂μ = ∫⁻ (a : α), ↑(nnnorm(f a)) ^ q ∂μ,
    { refine lintegral_congr (λ a, _),
      simp_rw [ennreal.coe_rpow_of_nonneg _ hp2q2.nonneg, ←nnreal.rpow_mul,
        ennreal.coe_rpow_of_nonneg _ (le_of_lt hq0_lt)],
      congr,
      exact hpp2, },
    rw [h_int_g, h_int_f, @ennreal.mul_rpow_of_nonneg _ _ (1/p) (by simp [hp0]), ←ennreal.rpow_mul,
      ←ennreal.rpow_mul],
    have h_rw1 : 1 / p2 * (1 / p) = 1/q, by rw [div_mul_div, one_mul, mul_comm, hpp2],
    have h_rw2 : 1 / q2 * (1 / p) = 1/p - 1/q,
    { rw [div_mul_div, one_mul, div_sub_div _ _ hp0_ne (ne_of_lt hq0_lt).symm, mul_one, one_mul,
        div_eq_iff, mul_comm p q, mul_comm q2 p, div_eq_mul_inv, hq2,
        mul_comm ((q - p) * (q * p)⁻¹) _, ←mul_assoc, ←mul_assoc, mul_assoc, mul_assoc],
      nth_rewrite 1 ←mul_assoc,
      rw [inv_mul_cancel, one_mul, mul_comm p, mul_inv_cancel],
      { simp [hp0_ne, (ne_of_lt hq0_lt).symm], },
      { rw [ne.def, sub_eq_zero], exact (ne_of_lt hpq).symm, },
      { simp [hp0_ne, hp2q2.symm.ne_zero], }, },
    rw [h_rw1, h_rw2],
  end
end

lemma snorm_mono {p q : ℝ} (hp1 : 1 ≤ p) (hpq : p ≤ q) (μ : measure α) [probability_measure μ]
  {f : α → E} (hf : measurable f) :
  snorm f p μ ≤ snorm f q μ :=
begin
  have h_le_μ := snorm_le_snorm_mul_rpow_measure_univ hp1 hpq μ hf,
  rwa [measure_univ, ennreal.one_rpow, mul_one] at h_le_μ,
end

lemma mem_ℒp_of_mem_ℒp_of_le {p q : ℝ} {μ : measure α} [finite_measure μ] {f : α → E}
  (hfq : mem_ℒp f q μ) (hp1 : 1 ≤ p) (hpq : p ≤ q) :
  mem_ℒp f p μ :=
begin
  cases hfq with hfq_m hfq_lt_top,
  split,
  { exact hfq_m, },
  have hp_pos : 0 < p, from lt_of_lt_of_le zero_lt_one hp1,
  have hq_pos : 0 < q, from lt_of_lt_of_le zero_lt_one (le_trans hp1 hpq),
  suffices h_snorm : snorm f p μ < ⊤,
  { have h_top_eq : (⊤ : ennreal) = ⊤ ^ (1/p), by simp [hp_pos],
    rw [snorm, h_top_eq] at h_snorm,
    have h_snorm_pow : ((∫⁻ (a : α), ↑(nnnorm (f a)) ^ p ∂μ) ^ (1/p)) ^ p < (⊤ ^ (1/p)) ^ p,
    from ennreal.rpow_lt_rpow h_snorm hp_pos,
    rw [←ennreal.rpow_mul, ←ennreal.rpow_mul] at h_snorm_pow,
    simpa [(ne_of_lt hp_pos).symm] using h_snorm_pow, },
  calc snorm f p μ
      ≤ snorm f q μ * (μ set.univ) ^ (1/p - 1/q) :
    snorm_le_snorm_mul_rpow_measure_univ hp1 hpq μ hfq_m
  ... < ⊤ :
  begin
    rw ennreal.mul_lt_top_iff,
    left,
    split,
    { exact mem_ℒp.snorm_lt_top (le_of_lt hq_pos) ⟨hfq_m, hfq_lt_top⟩, },
    { refine ennreal.rpow_lt_top_of_nonneg _ (measure_ne_top μ set.univ),
      rwa [le_sub, sub_zero, one_div, one_div, inv_le_inv hq_pos hp_pos], },
  end
end

lemma mem_ℒp.integrable (hp1 : 1 ≤ p) {f : α → E} [finite_measure μ] (hfp : mem_ℒp f p μ) :
  integrable f μ :=
begin
  rw ←mem_ℒp_one_iff_integrable,
  exact mem_ℒp_of_mem_ℒp_of_le hfp (le_refl 1) hp1,
end

section second_countable_topology
variable [topological_space.second_countable_topology E]

lemma mem_ℒp.add {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) (hp1 : 1 ≤ p) :
  mem_ℒp (f+g) p μ :=
begin
  have hp0_lt : 0 < p, from lt_of_lt_of_le zero_lt_one hp1,
  have hp0 : 0 ≤ p, from le_of_lt hp0_lt,
  split,
  { exact measurable.add hf.1 hg.1, },
  simp_rw [pi.add_apply, ennreal.coe_rpow_of_nonneg _ hp0],
  have h_nnnorm_add_le : ∫⁻ (a : α), ↑(nnnorm (f a + g a) ^ p) ∂μ
    ≤ ∫⁻ a, ↑((nnnorm (f a) + nnnorm (g a)) ^ p) ∂μ,
  { refine lintegral_mono_nnreal (λ a, _),
    exact nnreal.rpow_le_rpow (nnnorm_add_le (f a) (g a)) (le_of_lt hp0_lt), },
  refine lt_of_le_of_lt h_nnnorm_add_le _,
  simp_rw [←ennreal.coe_rpow_of_nonneg _ hp0, ennreal.coe_add],
  let f_nnnorm := (λ a : α, (nnnorm (f a) : ennreal)),
  let g_nnnorm := (λ a : α, (nnnorm (g a) : ennreal)),
  change ∫⁻ (a : α), ((f_nnnorm + g_nnnorm) a) ^ p ∂μ < ⊤,
  exact ennreal.lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top hf.1.nnnorm.ennreal_coe hf.2
    hg.1.nnnorm.ennreal_coe hg.2 hp1,
end

end second_countable_topology

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 E]

lemma mem_ℒp.smul (f : α → E) (c : 𝕜) (hp_pos : 0 < p) (hfp : mem_ℒp f p μ) :
  mem_ℒp (c • f) p μ :=
begin
  have hp0 : 0 ≤ p, from le_of_lt hp_pos,
  split,
  { exact measurable.const_smul hfp.1 c, },
  simp_rw [pi.smul_apply, nnnorm_smul, ennreal.coe_mul, ennreal.mul_rpow_of_nonneg _ _ hp0],
  rw lintegral_const_mul _ hfp.1.nnnorm.ennreal_coe.ennreal_rpow_const,
  exact ennreal.mul_lt_top (ennreal.rpow_lt_top_of_nonneg hp0 ennreal.coe_ne_top) hfp.2,
end

end normed_space

end borel_space

end ℒp_space
