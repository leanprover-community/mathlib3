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

/-- The property that `f:α→E` is ae_measurable and `∫ ∥f a∥^p ∂μ` is finite -/
def mem_ℒp (f : α → E) (p : ℝ) (μ : measure α) : Prop :=
ae_measurable f μ ∧ ∫⁻ a, (nnnorm (f a)) ^ p ∂μ < ⊤

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

lemma mem_ℒp_of_snorm_lt_top {f : α → E} (hp0_lt : 0 < p) (hfm : ae_measurable f μ)
  (hfp : snorm f p μ < ⊤) : mem_ℒp f p μ :=
⟨hfm, lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top hp0_lt hfp⟩

end top

section zero

@[simp] lemma snorm_exponent_zero {f : α → F} : snorm f 0 μ = 1 :=
by rw [snorm, div_zero, ennreal.rpow_zero]

lemma zero_mem_ℒp_of_pos (hp_pos : 0 < p) : mem_ℒp (0 : α → E) p μ :=
⟨measurable_zero.ae_measurable, by simp [hp_pos]⟩

lemma zero_mem_ℒp_of_nonneg [finite_measure μ] (hp0 : 0 ≤ p) : mem_ℒp (0 : α → E) p μ :=
begin
  by_cases h0 : p = 0,
  { rw h0,
    split,
    { exact measurable_zero.ae_measurable, },
    { simp [measure_lt_top μ set.univ], }, },
  { rw ←ne.def at h0,
    exact zero_mem_ℒp_of_pos (lt_of_le_of_ne hp0 h0.symm), },
end

@[simp] lemma snorm_zero (hp0_lt : 0 < p) : snorm (0 : α → F) p μ = 0 :=
by simp [snorm, hp0_lt]

@[simp] lemma snorm_zero' (hp0_ne : p ≠ 0) (hμ : μ ≠ 0) : snorm (0 : α → F) p μ = 0 :=
begin
  cases le_or_lt 0 p with hp0 hp_neg,
  { exact snorm_zero (lt_of_le_of_ne hp0 hp0_ne.symm), },
  { rw [snorm, ennreal.rpow_eq_zero_iff],
    simp [hμ, hp_neg], },
end

/-- When `μ = 0`, we have `∫ f^p ∂μ = 0`. `snorm f p μ` is then `0`, `1` or `⊤` depending on `p`. -/
lemma snorm_measure_zero_of_pos {f : α → F} (hp_pos : 0 < p) : snorm f p 0 = 0 :=
by simp [snorm, hp_pos]

/-- When `μ = 0`, we have `∫ f^p ∂μ = 0`. `snorm f p μ` is then `0`, `1` or `⊤` depending on `p`. -/
lemma snorm_measure_zero_of_exponent_zero {f : α → F} : snorm f 0 0 = 1 := by simp [snorm]

/-- When `μ = 0`, we have `∫ f^p ∂μ = 0`. `snorm f p μ` is then `0`, `1` or `⊤` depending on `p`. -/
lemma snorm_measure_zero_of_neg {f : α → F} (hp_neg : p < 0) : snorm f p 0 = ⊤ :=
by simp [snorm, hp_neg]

end zero

lemma snorm_const (c : F) (hp_pos : 0 < p) :
  snorm (λ x : α , c) p μ = (nnnorm c : ennreal) * (μ set.univ) ^ (1/p) :=
begin
  rw [snorm, lintegral_const, @ennreal.mul_rpow_of_nonneg _ _ (1/p) (by simp [le_of_lt hp_pos])],
  congr,
  rw ←ennreal.rpow_mul,
  suffices hp_cancel : p * (1/p) = 1, by rw [hp_cancel, ennreal.rpow_one],
  rw [one_div, mul_inv_cancel (ne_of_lt hp_pos).symm],
end

lemma snorm_const' [finite_measure μ] (c : F) (hc_ne_zero : c ≠ 0) (hp_ne_zero : p ≠ 0) :
  snorm (λ x : α , c) p μ = (nnnorm c : ennreal) * (μ set.univ) ^ (1/p) :=
begin
  rw [snorm, lintegral_const, ennreal.mul_rpow_of_ne_top _ (measure_ne_top μ set.univ)],
  { congr,
    rw ←ennreal.rpow_mul,
    suffices hp_cancel : p * (1/p) = 1, by rw [hp_cancel, ennreal.rpow_one],
    rw [one_div, mul_inv_cancel hp_ne_zero], },
  { rw [ne.def, ennreal.rpow_eq_top_iff, auto.not_or_eq, auto.not_and_eq, auto.not_and_eq],
    split,
    { left,
      rwa [ennreal.coe_eq_zero, nnnorm_eq_zero], },
    { exact or.inl ennreal.coe_ne_top, }, },
end

lemma snorm_const_of_probability_measure (c : F) (hp_pos : 0 < p) [probability_measure μ] :
  snorm (λ x : α , c) p μ = (nnnorm c : ennreal) :=
by simp [snorm_const c hp_pos, measure_univ]

lemma mem_ℒp_const (c : E) (h : c ≠ 0 ∨ 0 ≤ p) [finite_measure μ] : mem_ℒp (λ a:α, c) p μ :=
begin
  split,
  { exact measurable_const.ae_measurable, },
  dsimp only,
  rw lintegral_const,
  refine ennreal.mul_lt_top _ (measure_lt_top μ set.univ),
  rw [lt_top_iff_ne_top, ne.def, ennreal.rpow_eq_top_iff, auto.not_or_eq, auto.not_and_eq,
    auto.not_and_eq],
  split,
  { rw [ennreal.coe_eq_zero, nnnorm_eq_zero],
    push_neg,
    exact h, },
  { exact or.inl ennreal.coe_ne_top, },
end

lemma mem_ℒp_const_of_nonneg (c : E) (hp0 : 0 ≤ p) [finite_measure μ] : mem_ℒp (λ a:α, c) p μ :=
mem_ℒp_const c (or.inr hp0)

lemma mem_ℒp_const_of_ne_zero (c : E) (hc : c ≠ 0) [finite_measure μ] : mem_ℒp (λ a:α, c) p μ :=
mem_ℒp_const c (or.inl hc)

lemma snorm_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) :
  snorm f p μ = snorm g p μ :=
begin
  suffices h_no_pow : ∫⁻ a, (nnnorm (f a)) ^ p ∂μ = ∫⁻ a, (nnnorm (g a)) ^ p ∂μ,
  { simp_rw [snorm, h_no_pow], },
  exact lintegral_congr_ae
    (filter.eventually.mp hfg (filter.eventually_of_forall (λ x hx, by simp [*]))),
end

lemma mem_ℒp.ae_eq {f g : α → E} (hfg : f =ᵐ[μ] g) (hf_Lp : mem_ℒp f p μ) :
  mem_ℒp g p μ :=
begin
  split,
  { cases hf_Lp.1 with f' hf',
    use f',
    exact ⟨hf'.1, ae_eq_trans hfg.symm hf'.2⟩, },
  have h_eq : ∫⁻ (a : α), (nnnorm (g a)) ^ p ∂μ = ∫⁻ (a : α), (nnnorm (f a)) ^ p ∂μ,
  from lintegral_congr_ae
    (filter.eventually.mp hfg (filter.eventually_of_forall (λ x hx, by simp [hx]))),
  rw h_eq,
  exact hf_Lp.2,
end

lemma mem_ℒp_congr_ae {f g : α → E} (hfg : f =ᵐ[μ] g) :
  mem_ℒp f p μ ↔ mem_ℒp g p μ :=
⟨λ h, h.ae_eq hfg, λ h, h.ae_eq hfg.symm⟩

section opens_measurable_space
variable [opens_measurable_space E]

lemma snorm_eq_zero_of_ae_zero {f : α → F} (hp0_lt : 0 < p) (hf_zero : f =ᵐ[μ] 0) :
  snorm f p μ = 0 :=
by rw [snorm_congr_ae hf_zero, snorm_zero hp0_lt]

lemma snorm_eq_zero_of_ae_zero' (hp0_ne : p ≠ 0) (hμ : μ ≠ 0) {f : α → F} (hf_zero : f =ᵐ[μ] 0) :
  snorm f p μ = 0 :=
by rw [snorm_congr_ae hf_zero, snorm_zero' hp0_ne hμ]

lemma ae_eq_zero_of_snorm_eq_zero {f : α → E} (hp0 : 0 ≤ p) (hf : ae_measurable f μ)
  (h : snorm f p μ = 0) :
  f =ᵐ[μ] 0 :=
begin
  rw [snorm, ennreal.rpow_eq_zero_iff] at h,
  cases h,
  { rw lintegral_eq_zero_iff' hf.nnnorm.ennreal_coe.ennreal_rpow_const at h,
    refine filter.eventually.mp h.left (filter.eventually_of_forall (λ x hx, _)),
    rw [pi.zero_apply, ennreal.rpow_eq_zero_iff] at hx,
    cases hx,
    { cases hx with hx _,
      rwa [←ennreal.coe_zero, ennreal.coe_eq_coe, nnnorm_eq_zero] at hx, },
    { exfalso,
      exact ennreal.coe_ne_top hx.left, }, },
  { exfalso,
    rw [one_div, inv_lt_zero] at h,
    linarith, },
end

lemma snorm_eq_zero_iff (hp0_lt : 0 < p) {f : α → E} (hf : ae_measurable f μ) :
  snorm f p μ = 0 ↔ f =ᵐ[μ] 0 :=
⟨ae_eq_zero_of_snorm_eq_zero (le_of_lt hp0_lt) hf, snorm_eq_zero_of_ae_zero hp0_lt⟩

end opens_measurable_space

@[simp] lemma snorm_neg {f : α → F} : snorm (-f) p μ = snorm f p μ :=
by simp [snorm]

section borel_space
variable [borel_space E]

lemma mem_ℒp.neg {f : α → E} (hf : mem_ℒp f p μ) : mem_ℒp (-f) p μ :=
⟨ae_measurable.neg hf.1, by simp [hf.right]⟩

lemma snorm_le_snorm_mul_rpow_measure_univ {p q : ℝ} (hp0_lt : 0 < p) (hpq : p ≤ q) (μ : measure α)
  {f : α → E} (hf : ae_measurable f μ) :
  snorm f p μ ≤ snorm f q μ * (μ set.univ) ^ (1/p - 1/q) :=
begin
  have hq0_lt : 0 < q, from lt_of_lt_of_le hp0_lt hpq,
  by_cases hpq_eq : p = q,
  { rw [hpq_eq, sub_self, ennreal.rpow_zero, mul_one],
    exact le_refl _, },
  have hpq : p < q, from lt_of_le_of_ne hpq hpq_eq,
  let g := λ a : α, (1 : ennreal),
  have h_rw : ∫⁻ a, ↑(nnnorm (f a))^p ∂ μ = ∫⁻ a, (nnnorm (f a) * (g a))^p ∂ μ,
  from lintegral_congr (λ a, by simp),
  repeat {rw snorm},
  rw h_rw,
  let r := p * q / (q - p),
  have hpqr : 1/p = 1/q + 1/r,
  { field_simp [(ne_of_lt hp0_lt).symm,
      (ne_of_lt hq0_lt).symm],
    ring, },
  calc (∫⁻ (a : α), (↑(nnnorm (f a)) * g a) ^ p ∂μ) ^ (1/p)
      ≤ (∫⁻ (a : α), ↑(nnnorm (f a)) ^ q ∂μ) ^ (1/q) * (∫⁻ (a : α), (g a) ^ r ∂μ) ^ (1/r) :
    ennreal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hf.nnnorm.ennreal_coe
      ae_measurable_const
  ... = (∫⁻ (a : α), ↑(nnnorm (f a)) ^ q ∂μ) ^ (1/q) * μ set.univ ^ (1/p - 1/q) :
    by simp [hpqr],
end

lemma snorm_le_snorm_of_exponent_le {p q : ℝ} (hp0_lt : 0 < p) (hpq : p ≤ q) (μ : measure α)
  [probability_measure μ] {f : α → E} (hf : ae_measurable f μ) :
  snorm f p μ ≤ snorm f q μ :=
begin
  have h_le_μ := snorm_le_snorm_mul_rpow_measure_univ hp0_lt hpq μ hf,
  rwa [measure_univ, ennreal.one_rpow, mul_one] at h_le_μ,
end

lemma mem_ℒp.mem_ℒp_of_exponent_le {p q : ℝ} {μ : measure α} [finite_measure μ] {f : α → E}
  (hfq : mem_ℒp f q μ) (hp_pos : 0 < p) (hpq : p ≤ q) :
  mem_ℒp f p μ :=
begin
  cases hfq with hfq_m hfq_lt_top,
  split,
  { exact hfq_m, },
  have hq_pos : 0 < q, from lt_of_lt_of_le  hp_pos hpq,
  suffices h_snorm : snorm f p μ < ⊤,
  { have h_top_eq : (⊤ : ennreal) = ⊤ ^ (1/p), by simp [hp_pos],
    rw [snorm, h_top_eq] at h_snorm,
    have h_snorm_pow : ((∫⁻ (a : α), ↑(nnnorm (f a)) ^ p ∂μ) ^ (1/p)) ^ p < (⊤ ^ (1/p)) ^ p,
    from ennreal.rpow_lt_rpow h_snorm hp_pos,
    rw [←ennreal.rpow_mul, ←ennreal.rpow_mul] at h_snorm_pow,
    simpa [(ne_of_lt hp_pos).symm] using h_snorm_pow, },
  calc snorm f p μ
      ≤ snorm f q μ * (μ set.univ) ^ (1/p - 1/q) :
    snorm_le_snorm_mul_rpow_measure_univ hp_pos hpq μ hfq_m
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
  exact hfp.mem_ℒp_of_exponent_le zero_lt_one hp1,
end

lemma snorm_add_le {f g : α → E} (hf : ae_measurable f μ) (hg : ae_measurable g μ) (hp1 : 1 ≤ p) :
  snorm (f + g) p μ ≤ snorm f p μ + snorm g p μ :=
calc (∫⁻ a, ↑(nnnorm ((f + g) a)) ^ p ∂μ) ^ (1 / p)
    ≤ (∫⁻ a, (((λ a, (nnnorm (f a) : ennreal))
        + (λ a, (nnnorm (g a) : ennreal))) a) ^ p ∂μ) ^ (1 / p) :
begin
  refine @ennreal.rpow_le_rpow _ _ (1/p) _ (by simp [le_trans zero_le_one hp1]),
  refine lintegral_mono (λ a, ennreal.rpow_le_rpow _ (le_trans zero_le_one hp1)),
  simp [←ennreal.coe_add, nnnorm_add_le],
end
... ≤ snorm f p μ + snorm g p μ :
  ennreal.lintegral_Lp_add_le hf.nnnorm.ennreal_coe hg.nnnorm.ennreal_coe hp1

section second_countable_topology
variable [topological_space.second_countable_topology E]

lemma mem_ℒp.add {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) (hp1 : 1 ≤ p) :
  mem_ℒp (f+g) p μ :=
begin
  have hp0_lt : 0 < p, from lt_of_lt_of_le zero_lt_one hp1,
  have hp0 : 0 ≤ p, from le_of_lt hp0_lt,
  split,
  { exact ae_measurable.add hf.1 hg.1, },
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

lemma mem_ℒp.sub {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) (hp1 : 1 ≤ p) :
  mem_ℒp (f-g) p μ :=
by { rw sub_eq_add_neg, exact hf.add hg.neg hp1 }

end second_countable_topology

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 E]

lemma mem_ℒp.const_smul {f : α → E} (hfp : mem_ℒp f p μ) (c : 𝕜) (hp0 : 0 ≤ p) :
  mem_ℒp (c • f) p μ :=
begin
  split,
  { exact ae_measurable.const_smul hfp.1 c, },
  simp_rw [pi.smul_apply, nnnorm_smul, ennreal.coe_mul, ennreal.mul_rpow_of_nonneg _ _ hp0],
  rw lintegral_const_mul'' _ hfp.1.nnnorm.ennreal_coe.ennreal_rpow_const,
  exact ennreal.mul_lt_top (ennreal.rpow_lt_top_of_nonneg hp0 ennreal.coe_ne_top) hfp.2,
end

lemma snorm_const_smul {f : α → E} (hf : ae_measurable f μ) (c : 𝕜) (hp0_lt : 0 < p) :
  snorm (c • f) p μ = (nnnorm c : ennreal) * snorm f p μ :=
begin
  rw snorm,
  simp_rw [pi.smul_apply, nnnorm_smul, ennreal.coe_mul],
  simp_rw ennreal.mul_rpow_of_nonneg _ _ (le_of_lt hp0_lt),
  suffices h_integral : ∫⁻ a, ↑(nnnorm c) ^ p * ↑(nnnorm (f a)) ^ p ∂μ
    = (nnnorm c : ennreal)^p * ∫⁻ a, (nnnorm (f a)) ^ p ∂μ,
  { apply_fun (λ x, x ^ (1/p)) at h_integral,
    rw [h_integral, @ennreal.mul_rpow_of_nonneg _ _ (1/p) (by simp [le_of_lt hp0_lt])],
    congr,
    simp_rw [←ennreal.rpow_mul, one_div, mul_inv_cancel (ne_of_lt hp0_lt).symm,
      ennreal.rpow_one], },
  rw lintegral_const_mul'' _ hf.nnnorm.ennreal_coe.ennreal_rpow_const,
end

lemma snorm_smul_le_mul_snorm [measurable_space 𝕜] [opens_measurable_space 𝕜] {q r : ℝ}
  {f : α → E} (hf : ae_measurable f μ) {φ : α → 𝕜} (hφ : ae_measurable φ μ)
  (hp0_lt : 0 < p) (hpq : p < q) (hpqr : 1/p = 1/q + 1/r) :
  snorm (φ • f) p μ ≤ snorm φ q μ * snorm f r μ :=
begin
  rw snorm,
  simp_rw [pi.smul_apply', nnnorm_smul, ennreal.coe_mul],
  exact ennreal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hφ.nnnorm.ennreal_coe
    hf.nnnorm.ennreal_coe,
end

end normed_space

end borel_space

end ℒp_space
