/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rémy Degenne.
-/
import measure_theory.ess_sup
import measure_theory.l1_space
import analysis.mean_inequalities
import data.finset.intervals

/-!
# ℒp space and Lp space

This file describes properties of almost everywhere measurable functions with finite seminorm,
denoted by `snorm f p μ` and defined for `p:ℝ≥0∞` as `0` if `p=0`, `(∫ ∥f a∥^p ∂μ) ^ (1/p)` for
`0 < p < ∞` and `ess_sup ∥f∥ μ` for `p=∞`.

The Prop-valued `mem_ℒp f p μ` states that a function `f : α → E` has finite seminorm.
The space `Lp α E p μ` is the subtype of elements of `α →ₘ[μ] E` (see ae_eq_fun) such that
`snorm f p μ` is finite. For `1 ≤ p`, `snorm` defines a norm and Lp is a metric space.

TODO: prove that Lp is complete.

## Main definitions

* `snorm' f p μ` : `(∫ ∥f a∥^p ∂μ) ^ (1/p)` for `f : α → F` and `p : ℝ`, where `α` is a  measurable
  space and `F` is a normed group.
* `snorm_ess_sup f μ` : seminorm in `ℒ∞`, equal to the essential supremum `ess_sup ∥f∥ μ`.
* `snorm f p μ` : for `p : ℝ≥0∞`, seminorm in `ℒp`, equal to `0` for `p=0`, to `snorm' f p μ`
  for `0 < p < ∞` and to `snorm_ess_sup f μ` for `p = ∞`.

* `mem_ℒp f p μ` : property that the function `f` is almost everywhere measurable and has finite
  p-seminorm for measure `μ` (`snorm f p μ < ∞`)
* `Lp E p μ` : elements of `α →ₘ[μ] E` (see ae_eq_fun) such that `snorm f p μ` is finite. Defined
  as an `add_subgroup` of `α →ₘ[μ] E`.

-/

noncomputable theory

<<<<<<< Updated upstream
open_locale ennreal
=======
open_locale big_operators classical
>>>>>>> Stashed changes

namespace measure_theory

section ℒp

variables {α E F : Type*} [measurable_space α] {μ : measure α}
  [measurable_space E] [normed_group E]
  [normed_group F]
  {p : ℝ} {q : ℝ≥0∞}

section ℒp_space_definition

/-- `(∫ ∥f a∥^p ∂μ) ^ (1/p)`, which is a seminorm on the space of measurable functions for which
this quantity is finite -/
def snorm' (f : α → F) (p : ℝ) (μ : measure α) : ℝ≥0∞ := (∫⁻ a, (nnnorm (f a))^p ∂μ) ^ (1/p)

/-- seminorm for `ℒ∞`, equal to the essential supremum of `∥f∥`. -/
def snorm_ess_sup (f : α → F) (μ : measure α) := ess_sup (λ x, (nnnorm (f x) : ℝ≥0∞)) μ

/-- `ℒp` seminorm, equal to `0` for `p=0`, to `(∫ ∥f a∥^p ∂μ) ^ (1/p)` for `0 < p < ∞` and to
`ess_sup ∥f∥ μ` for `p = ∞`. -/
def snorm (f : α → F) (q : ℝ≥0∞) (μ : measure α) : ℝ≥0∞ :=
if q = 0 then 0 else (if q = ⊤ then snorm_ess_sup f μ else snorm' f (ennreal.to_real q) μ)

lemma snorm_eq_snorm' (hq_ne_zero : q ≠ 0) (hq_ne_top : q ≠ ⊤) {f : α → F} :
  snorm f q μ = snorm' f (ennreal.to_real q) μ :=
by simp [snorm, hq_ne_zero, hq_ne_top]

@[simp] lemma snorm_exponent_top {f : α → F} : snorm f ⊤ μ = snorm_ess_sup f μ := by simp [snorm]

/-- The property that `f:α→E` is ae_measurable and `(∫ ∥f a∥^p ∂μ)^(1/p)` is finite -/
def mem_ℒp (f : α → E) (p : ℝ≥0∞) (μ : measure α) : Prop :=
ae_measurable f μ ∧ snorm f p μ < ⊤

lemma lintegral_rpow_nnnorm_eq_rpow_snorm' {f : α → F} (hp0_lt : 0 < p) :
  ∫⁻ a, (nnnorm (f a)) ^ p ∂μ = (snorm' f p μ) ^ p :=
begin
  rw [snorm', ←ennreal.rpow_mul, one_div, inv_mul_cancel, ennreal.rpow_one],
  exact (ne_of_lt hp0_lt).symm,
end

end ℒp_space_definition

lemma mem_ℒp_one_iff_integrable {f : α → E} : mem_ℒp f 1 μ ↔ integrable f μ :=
by simp_rw [integrable, has_finite_integral, mem_ℒp,
    snorm_eq_snorm' one_ne_zero ennreal.one_ne_top, ennreal.one_to_real, snorm', one_div_one,
    ennreal.rpow_one]

section top

lemma mem_ℒp.snorm_lt_top {f : α → E} (hfp : mem_ℒp f q μ) : snorm f q μ < ⊤ := hfp.2

lemma mem_ℒp.snorm_ne_top {f : α → E} (hfp : mem_ℒp f q μ) : snorm f q μ ≠ ⊤ := ne_of_lt (hfp.2)

lemma lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top {f : α → F} (hp0_lt : 0 < p)
  (hfp : snorm' f p μ < ⊤) :
  ∫⁻ a, (nnnorm (f a)) ^ p ∂μ < ⊤ :=
begin
  rw lintegral_rpow_nnnorm_eq_rpow_snorm' hp0_lt,
  exact ennreal.rpow_lt_top_of_nonneg (le_of_lt hp0_lt) (ne_of_lt hfp),
end

end top

section zero

@[simp] lemma snorm'_exponent_zero {f : α → F} : snorm' f 0 μ = 1 :=
by rw [snorm', div_zero, ennreal.rpow_zero]

@[simp] lemma snorm_exponent_zero {f : α → F} : snorm f 0 μ = 0 :=
by simp [snorm]

lemma mem_ℒp_zero_iff_ae_measurable {f : α → E} : mem_ℒp f 0 μ ↔ ae_measurable f μ :=
by simp [mem_ℒp, snorm_exponent_zero]

@[simp] lemma snorm'_zero (hp0_lt : 0 < p) : snorm' (0 : α → F) p μ = 0 :=
by simp [snorm', hp0_lt]

@[simp] lemma snorm'_zero' (hp0_ne : p ≠ 0) (hμ : μ ≠ 0) : snorm' (0 : α → F) p μ = 0 :=
begin
  cases le_or_lt 0 p with hp0 hp_neg,
  { exact snorm'_zero (lt_of_le_of_ne hp0 hp0_ne.symm), },
  { simp [snorm', ennreal.rpow_eq_zero_iff, hμ, hp_neg], },
end

@[simp] lemma snorm_ess_sup_zero : snorm_ess_sup (0 : α → F) μ = 0 :=
begin
  simp_rw [snorm_ess_sup, pi.zero_apply, nnnorm_zero, ennreal.coe_zero, ←ennreal.bot_eq_zero],
  exact ess_sup_const_bot,
end

@[simp] lemma snorm_zero : snorm (0 : α → F) q μ = 0 :=
begin
  by_cases h0 : q = 0,
  { simp [h0], },
  by_cases h_top : q = ⊤,
  { simp only [h_top, snorm_exponent_top, snorm_ess_sup_zero], },
  rw ←ne.def at h0,
  simp [snorm_eq_snorm' h0 h_top,
    ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) h0.symm, h_top⟩],
end

lemma zero_mem_ℒp : mem_ℒp (0 : α → E) q μ :=
⟨measurable_zero.ae_measurable, by { rw snorm_zero, exact ennreal.coe_lt_top, } ⟩

lemma snorm'_measure_zero_of_pos {f : α → F} (hp_pos : 0 < p) : snorm' f p 0 = 0 :=
by simp [snorm', hp_pos]

lemma snorm'_measure_zero_of_exponent_zero {f : α → F} : snorm' f 0 0 = 1 := by simp [snorm']

lemma snorm'_measure_zero_of_neg {f : α → F} (hp_neg : p < 0) : snorm' f p 0 = ⊤ :=
by simp [snorm', hp_neg]

@[simp] lemma snorm_ess_sup_measure_zero {f : α → F} : snorm_ess_sup f 0 = 0 :=
by simp [snorm_ess_sup]

@[simp] lemma snorm_measure_zero {f : α → F} : snorm f q 0 = 0 :=
begin
  by_cases h0 : q = 0,
  { simp [h0], },
  by_cases h_top : q = ⊤,
  { simp [h_top], },
  rw ←ne.def at h0,
  simp [snorm_eq_snorm' h0 h_top, snorm',
    ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) h0.symm, h_top⟩],
end

end zero

section const

lemma snorm'_const (c : F) (hp_pos : 0 < p) :
  snorm' (λ x : α , c) p μ = (nnnorm c : ℝ≥0∞) * (μ set.univ) ^ (1/p) :=
begin
  rw [snorm', lintegral_const, @ennreal.mul_rpow_of_nonneg _ _ (1/p) (by simp [le_of_lt hp_pos])],
  congr,
  rw ←ennreal.rpow_mul,
  suffices hp_cancel : p * (1/p) = 1, by rw [hp_cancel, ennreal.rpow_one],
  rw [one_div, mul_inv_cancel (ne_of_lt hp_pos).symm],
end

lemma snorm'_const' [finite_measure μ] (c : F) (hc_ne_zero : c ≠ 0) (hp_ne_zero : p ≠ 0) :
  snorm' (λ x : α , c) p μ = (nnnorm c : ℝ≥0∞) * (μ set.univ) ^ (1/p) :=
begin
  rw [snorm', lintegral_const, ennreal.mul_rpow_of_ne_top _ (measure_ne_top μ set.univ)],
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

lemma snorm_ess_sup_const (c : F) (hμ : μ ≠ 0) :
  snorm_ess_sup (λ x : α, c) μ = (nnnorm c : ℝ≥0∞) :=
by rw [snorm_ess_sup, ess_sup_const _ hμ]

lemma snorm'_const_of_probability_measure (c : F) (hp_pos : 0 < p) [probability_measure μ] :
  snorm' (λ x : α , c) p μ = (nnnorm c : ℝ≥0∞) :=
by simp [snorm'_const c hp_pos, measure_univ]

lemma snorm_const (c : F) (h0 : q ≠ 0) (hμ : μ ≠ 0) :
  snorm (λ x : α , c) q μ = (nnnorm c : ℝ≥0∞) * (μ set.univ) ^ (1/(ennreal.to_real q)) :=
begin
  by_cases h_top : q = ⊤,
  { simp [h_top, snorm_ess_sup_const c hμ], },
  simp [snorm_eq_snorm' h0 h_top, snorm'_const,
    ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) h0.symm, h_top⟩],
end

lemma snorm_const' (c : F) (h0 : q ≠ 0) (h_top: q ≠ ⊤) :
  snorm (λ x : α , c) q μ = (nnnorm c : ℝ≥0∞) * (μ set.univ) ^ (1/(ennreal.to_real q)) :=
begin
  simp [snorm_eq_snorm' h0 h_top, snorm'_const,
    ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) h0.symm, h_top⟩],
end

lemma mem_ℒp_const (c : E) [finite_measure μ] : mem_ℒp (λ a:α, c) q μ :=
begin
  refine ⟨measurable_const.ae_measurable, _⟩,
  by_cases h0 : q = 0,
  { simp [h0], },
  by_cases hμ : μ = 0,
  { simp [hμ], },
  rw snorm_const c h0 hμ,
  refine ennreal.mul_lt_top ennreal.coe_lt_top _,
  refine ennreal.rpow_lt_top_of_nonneg _ (measure_ne_top μ set.univ),
  simp,
end

end const

lemma snorm'_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) : snorm' f p μ = snorm' g p μ :=
begin
  suffices h_no_pow : ∫⁻ a, (nnnorm (f a)) ^ p ∂μ = ∫⁻ a, (nnnorm (g a)) ^ p ∂μ,
  { simp_rw [snorm', h_no_pow], },
  exact lintegral_congr_ae (hfg.mono (λ x hx, by simp [*])),
end

lemma snorm_ess_sup_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) :
  snorm_ess_sup f μ = snorm_ess_sup g μ :=
ess_sup_congr_ae (hfg.mono (λ x hx, by rw hx))

lemma snorm_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) : snorm f q μ = snorm g q μ :=
begin
  by_cases h0 : q = 0,
  { simp [h0], },
  by_cases h_top : q = ⊤,
  { rw [h_top, snorm_exponent_top],
    exact snorm_ess_sup_congr_ae hfg, },
  repeat { rw snorm_eq_snorm' h0 h_top, },
  exact snorm'_congr_ae hfg,
end

lemma mem_ℒp.ae_eq {f g : α → E} (hfg : f =ᵐ[μ] g) (hf_Lp : mem_ℒp f q μ) : mem_ℒp g q μ :=
begin
  split,
  { cases hf_Lp.1 with f' hf',
    exact ⟨f', ⟨hf'.1, ae_eq_trans hfg.symm hf'.2⟩⟩, },
  { rw snorm_congr_ae hfg.symm,
    exact hf_Lp.2, },
end

lemma mem_ℒp_congr_ae {f g : α → E} (hfg : f =ᵐ[μ] g) : mem_ℒp f q μ ↔ mem_ℒp g q μ :=
⟨λ h, h.ae_eq hfg, λ h, h.ae_eq hfg.symm⟩

section opens_measurable_space
variable [opens_measurable_space E]

lemma snorm'_eq_zero_of_ae_zero {f : α → F} (hp0_lt : 0 < p) (hf_zero : f =ᵐ[μ] 0) :
  snorm' f p μ = 0 :=
by rw [snorm'_congr_ae hf_zero, snorm'_zero hp0_lt]

lemma snorm'_eq_zero_of_ae_zero' (hp0_ne : p ≠ 0) (hμ : μ ≠ 0) {f : α → F} (hf_zero : f =ᵐ[μ] 0) :
  snorm' f p μ = 0 :=
by rw [snorm'_congr_ae hf_zero, snorm'_zero' hp0_ne hμ]

lemma ae_eq_zero_of_snorm'_eq_zero {f : α → E} (hp0 : 0 ≤ p) (hf : ae_measurable f μ)
  (h : snorm' f p μ = 0) :
  f =ᵐ[μ] 0 :=
begin
  rw [snorm', ennreal.rpow_eq_zero_iff] at h,
  cases h,
  { rw lintegral_eq_zero_iff' hf.nnnorm.ennreal_coe.ennreal_rpow_const at h,
    refine h.left.mono (λ x hx, _),
    rw [pi.zero_apply, ennreal.rpow_eq_zero_iff] at hx,
    cases hx,
    { cases hx with hx _,
      rwa [←ennreal.coe_zero, ennreal.coe_eq_coe, nnnorm_eq_zero] at hx, },
    { exact absurd hx.left ennreal.coe_ne_top, }, },
  { exfalso,
    rw [one_div, inv_lt_zero] at h,
    linarith, },
end

lemma snorm'_eq_zero_iff (hp0_lt : 0 < p) {f : α → E} (hf : ae_measurable f μ) :
  snorm' f p μ = 0 ↔ f =ᵐ[μ] 0 :=
⟨ae_eq_zero_of_snorm'_eq_zero (le_of_lt hp0_lt) hf, snorm'_eq_zero_of_ae_zero hp0_lt⟩

lemma coe_nnnorm_ae_le_snorm_ess_sup (f : α → F) (μ : measure α) :
  ∀ᵐ x ∂μ, (nnnorm (f x) : ℝ≥0∞) ≤ snorm_ess_sup f μ :=
ennreal.ae_le_ess_sup (λ x, (nnnorm (f x) : ℝ≥0∞))

lemma snorm_ess_sup_eq_zero_iff {f : α → F} : snorm_ess_sup f μ = 0 ↔ f =ᵐ[μ] 0 :=
begin
  rw [snorm_ess_sup, ennreal.ess_sup_eq_zero_iff],
  split; intro h;
    { refine h.mono (λ x hx, _),
      simp_rw pi.zero_apply at hx ⊢,
      simpa using hx, },
end

lemma snorm_eq_zero_iff {f : α → E} (hf : ae_measurable f μ) (h0 : q ≠ 0) :
  snorm f q μ = 0 ↔ f =ᵐ[μ] 0 :=
begin
  by_cases h_top : q = ⊤,
  { rw [h_top, snorm_exponent_top, snorm_ess_sup_eq_zero_iff], },
  rw snorm_eq_snorm' h0 h_top,
  exact snorm'_eq_zero_iff
    (ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) h0.symm, h_top⟩) hf,
end

end opens_measurable_space

@[simp] lemma snorm'_neg {f : α → F} : snorm' (-f) p μ = snorm' f p μ := by simp [snorm']

@[simp] lemma snorm_neg {f : α → F} : snorm (-f) q μ = snorm f q μ :=
begin
  by_cases h0 : q = 0,
  { simp [h0], },
  by_cases h_top : q = ⊤,
  { simp [h_top, snorm_ess_sup], },
  simp [snorm_eq_snorm' h0 h_top],
end

section borel_space
variable [borel_space E]

lemma mem_ℒp.neg {f : α → E} (hf : mem_ℒp f q μ) : mem_ℒp (-f) q μ :=
⟨ae_measurable.neg hf.1, by simp [hf.right]⟩

lemma snorm'_le_snorm'_mul_rpow_measure_univ {p q : ℝ} (hp0_lt : 0 < p) (hpq : p ≤ q)
  {f : α → E} (hf : ae_measurable f μ) :
  snorm' f p μ ≤ snorm' f q μ * (μ set.univ) ^ (1/p - 1/q) :=
begin
  have hq0_lt : 0 < q, from lt_of_lt_of_le hp0_lt hpq,
  by_cases hpq_eq : p = q,
  { rw [hpq_eq, sub_self, ennreal.rpow_zero, mul_one],
    exact le_refl _, },
  have hpq : p < q, from lt_of_le_of_ne hpq hpq_eq,
  let g := λ a : α, (1 : ℝ≥0∞),
  have h_rw : ∫⁻ a, ↑(nnnorm (f a))^p ∂ μ = ∫⁻ a, (nnnorm (f a) * (g a))^p ∂ μ,
  from lintegral_congr (λ a, by simp),
  repeat {rw snorm'},
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

lemma snorm'_le_snorm_ess_sup_mul_rpow_measure_univ (hp_pos : 0 < p) {f : α → F} :
  snorm' f p μ ≤ snorm_ess_sup f μ * (μ set.univ) ^ (1/p) :=
begin
  have h_le : ∫⁻ (a : α), ↑(nnnorm (f a)) ^ p ∂μ ≤ ∫⁻ (a : α), (snorm_ess_sup f μ) ^ p ∂μ,
  { refine lintegral_mono_ae _,
    have h_nnnorm_le_snorm_ess_sup := coe_nnnorm_ae_le_snorm_ess_sup f μ,
    refine h_nnnorm_le_snorm_ess_sup.mono (λ x hx, ennreal.rpow_le_rpow hx (le_of_lt hp_pos)), },
  rw [snorm', ←ennreal.rpow_one (snorm_ess_sup f μ)],
  nth_rewrite 1 ←mul_inv_cancel (ne_of_lt hp_pos).symm,
  rw [ennreal.rpow_mul, one_div,
    ←@ennreal.mul_rpow_of_nonneg _ _ p⁻¹ (by simp [le_of_lt hp_pos])],
  refine ennreal.rpow_le_rpow _ (by simp [le_of_lt hp_pos]),
  rwa lintegral_const at h_le,
end

lemma snorm'_le_snorm'_of_exponent_le {p q : ℝ} (hp0_lt : 0 < p) (hpq : p ≤ q) (μ : measure α)
  [probability_measure μ] {f : α → E} (hf : ae_measurable f μ) :
  snorm' f p μ ≤ snorm' f q μ :=
begin
  have h_le_μ := snorm'_le_snorm'_mul_rpow_measure_univ hp0_lt hpq hf,
  rwa [measure_univ, ennreal.one_rpow, mul_one] at h_le_μ,
end

lemma snorm'_le_snorm_ess_sup (hp_pos : 0 < p) {f : α → F} [probability_measure μ] :
  snorm' f p μ ≤ snorm_ess_sup f μ :=
le_trans (snorm'_le_snorm_ess_sup_mul_rpow_measure_univ hp_pos) (le_of_eq (by simp [measure_univ]))

lemma snorm_le_snorm_of_exponent_le {p q : ℝ≥0∞} (hpq : p ≤ q) [probability_measure μ]
  {f : α → E} (hf : ae_measurable f μ) :
  snorm f p μ ≤ snorm f q μ :=
begin
  by_cases hp0 : p = 0,
  { simp [hp0], },
  rw ←ne.def at hp0,
  by_cases hq_top : q = ⊤,
  { by_cases hp_top : p = ⊤,
    { rw [hq_top, hp_top],
      exact le_refl _, },
    { have hp_pos : 0 < p.to_real,
      from ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) hp0.symm, hp_top⟩,
      rw [snorm_eq_snorm' hp0 hp_top, hq_top, snorm_exponent_top],
      refine le_trans (snorm'_le_snorm_ess_sup_mul_rpow_measure_univ hp_pos) (le_of_eq _),
      simp [measure_univ], }, },
  { have hp_top : p ≠ ⊤,
    { by_contra hp_eq_top,
      push_neg at hp_eq_top,
      refine hq_top _,
      rwa [hp_eq_top, top_le_iff] at hpq, },
    have hp_pos : 0 < p.to_real,
    from ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) hp0.symm, hp_top⟩,
    have hq0 : q ≠ 0,
    { by_contra hq_eq_zero,
      push_neg at hq_eq_zero,
      have hp_eq_zero : p = 0, from le_antisymm (by rwa hq_eq_zero at hpq) (zero_le _),
      rw [hp_eq_zero, ennreal.zero_to_real] at hp_pos,
      exact (lt_irrefl _) hp_pos, },
    have hpq_real : p.to_real ≤ q.to_real, by rwa ennreal.to_real_le_to_real hp_top hq_top,
    rw [snorm_eq_snorm' hp0 hp_top, snorm_eq_snorm' hq0 hq_top],
    exact snorm'_le_snorm'_of_exponent_le hp_pos hpq_real _ hf, },
end

lemma snorm'_lt_top_of_snorm'_lt_top_of_exponent_le {p q : ℝ} [finite_measure μ] {f : α → E}
  (hf : ae_measurable f μ) (hfq_lt_top : snorm' f q μ < ⊤) (hp_nonneg : 0 ≤ p) (hpq : p ≤ q) :
  snorm' f p μ < ⊤ :=
begin
  cases le_or_lt p 0 with hp_nonpos hp_pos,
  { rw le_antisymm hp_nonpos hp_nonneg,
    simp, },
  have hq_pos : 0 < q, from lt_of_lt_of_le hp_pos hpq,
  calc snorm' f p μ
      ≤ snorm' f q μ * (μ set.univ) ^ (1/p - 1/q) :
    snorm'_le_snorm'_mul_rpow_measure_univ hp_pos hpq hf
  ... < ⊤ :
  begin
    rw ennreal.mul_lt_top_iff,
    refine or.inl ⟨hfq_lt_top, ennreal.rpow_lt_top_of_nonneg _ (measure_ne_top μ set.univ)⟩,
    rwa [le_sub, sub_zero, one_div, one_div, inv_le_inv hq_pos hp_pos],
  end
end

lemma mem_ℒp.mem_ℒp_of_exponent_le {p q : ℝ≥0∞} [finite_measure μ] {f : α → E}
  (hfq : mem_ℒp f q μ) (hpq : p ≤ q) :
  mem_ℒp f p μ :=
begin
  cases hfq with hfq_m hfq_lt_top,
  by_cases hp0 : p = 0,
  { rwa [hp0, mem_ℒp_zero_iff_ae_measurable], },
  rw ←ne.def at hp0,
  refine ⟨hfq_m, _⟩,
  by_cases hp_top : p = ⊤,
  { have hq_top : q = ⊤,
      by rwa [hp_top, top_le_iff] at hpq,
    rw [hp_top],
    rwa hq_top at hfq_lt_top, },
  have hp_pos : 0 < p.to_real,
    from ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) hp0.symm, hp_top⟩,
  by_cases hq_top : q = ⊤,
  { rw snorm_eq_snorm' hp0 hp_top,
    rw [hq_top, snorm_exponent_top] at hfq_lt_top,
    refine lt_of_le_of_lt (snorm'_le_snorm_ess_sup_mul_rpow_measure_univ hp_pos) _,
    refine ennreal.mul_lt_top hfq_lt_top _,
    exact ennreal.rpow_lt_top_of_nonneg (by simp [le_of_lt hp_pos]) (measure_ne_top μ set.univ), },
  have hq0 : q ≠ 0,
  { by_contra hq_eq_zero,
    push_neg at hq_eq_zero,
    have hp_eq_zero : p = 0, from le_antisymm (by rwa hq_eq_zero at hpq) (zero_le _),
    rw [hp_eq_zero, ennreal.zero_to_real] at hp_pos,
    exact (lt_irrefl _) hp_pos, },
  have hpq_real : p.to_real ≤ q.to_real, by rwa ennreal.to_real_le_to_real hp_top hq_top,
  rw snorm_eq_snorm' hp0 hp_top,
  rw snorm_eq_snorm' hq0 hq_top at hfq_lt_top,
  exact snorm'_lt_top_of_snorm'_lt_top_of_exponent_le hfq_m hfq_lt_top (le_of_lt hp_pos) hpq_real,
end

lemma mem_ℒp.integrable (hq1 : 1 ≤ q) {f : α → E} [finite_measure μ] (hfq : mem_ℒp f q μ) :
  integrable f μ :=
mem_ℒp_one_iff_integrable.mp (hfq.mem_ℒp_of_exponent_le hq1)

lemma snorm'_add_le {f g : α → E} (hf : ae_measurable f μ) (hg : ae_measurable g μ) (hp1 : 1 ≤ p) :
  snorm' (f + g) p μ ≤ snorm' f p μ + snorm' g p μ :=
calc (∫⁻ a, ↑(nnnorm ((f + g) a)) ^ p ∂μ) ^ (1 / p)
    ≤ (∫⁻ a, (((λ a, (nnnorm (f a) : ℝ≥0∞))
        + (λ a, (nnnorm (g a) : ℝ≥0∞))) a) ^ p ∂μ) ^ (1 / p) :
begin
  refine @ennreal.rpow_le_rpow _ _ (1/p) _ (by simp [le_trans zero_le_one hp1]),
  refine lintegral_mono (λ a, ennreal.rpow_le_rpow _ (le_trans zero_le_one hp1)),
  simp [←ennreal.coe_add, nnnorm_add_le],
end
... ≤ snorm' f p μ + snorm' g p μ :
  ennreal.lintegral_Lp_add_le hf.nnnorm.ennreal_coe hg.nnnorm.ennreal_coe hp1

lemma snorm_ess_sup_add_le {f g : α → F} :
  snorm_ess_sup (f + g) μ ≤ snorm_ess_sup f μ + snorm_ess_sup g μ :=
begin
  refine le_trans (ess_sup_mono_ae (filter.eventually_of_forall (λ x, _)))
    (ennreal.ess_sup_add_le _ _),
  simp_rw [pi.add_apply, ←ennreal.coe_add, ennreal.coe_le_coe],
  exact nnnorm_add_le _ _,
end

lemma snorm_add_le {f g : α → E} (hf : ae_measurable f μ) (hg : ae_measurable g μ) (hq1 : 1 ≤ q) :
  snorm (f + g) q μ ≤ snorm f q μ + snorm g q μ :=
begin
  by_cases hq0 : q = 0,
  { simp [hq0], },
  by_cases hq_top : q = ⊤,
  { simp [hq_top, snorm_ess_sup_add_le], },
  have hq1_real : 1 ≤ q.to_real,
  by rwa [←ennreal.one_to_real, ennreal.to_real_le_to_real ennreal.one_ne_top hq_top],
  repeat { rw snorm_eq_snorm' hq0 hq_top, },
  exact snorm'_add_le hf hg hq1_real,
end

lemma snorm_add_lt_top_of_one_le {f g : α → E} (hf : mem_ℒp f q μ) (hg : mem_ℒp g q μ)
  (hq1 : 1 ≤ q) :
  snorm (f + g) q μ < ⊤ :=
lt_of_le_of_lt (snorm_add_le hf.1 hg.1 hq1) (ennreal.add_lt_top.mpr ⟨hf.2, hg.2⟩)

lemma snorm'_add_lt_top_of_le_one {f g : α → E} (hf : ae_measurable f μ) (hg : ae_measurable g μ)
  (hf_snorm : snorm' f p μ < ⊤) (hg_snorm : snorm' g p μ < ⊤) (hp_pos : 0 < p) (hp1 : p ≤ 1) :
  snorm' (f + g) p μ < ⊤ :=
calc (∫⁻ a, ↑(nnnorm ((f + g) a)) ^ p ∂μ) ^ (1 / p)
    ≤ (∫⁻ a, (((λ a, (nnnorm (f a) : ℝ≥0∞))
        + (λ a, (nnnorm (g a) : ℝ≥0∞))) a) ^ p ∂μ) ^ (1 / p) :
begin
  refine @ennreal.rpow_le_rpow _ _ (1/p) _ (by simp [hp_pos.le]),
  refine lintegral_mono (λ a, ennreal.rpow_le_rpow _ hp_pos.le),
  simp [←ennreal.coe_add, nnnorm_add_le],
end
... ≤ (∫⁻ a, (nnnorm (f a) : ℝ≥0∞) ^ p + (nnnorm (g a) : ℝ≥0∞) ^ p ∂μ) ^ (1 / p) :
begin
  refine @ennreal.rpow_le_rpow _ _ (1/p) (lintegral_mono (λ a, _)) (by simp [hp_pos.le]),
  exact ennreal.rpow_add_le_add_rpow _ _ hp_pos hp1,
end
... < ⊤ :
begin
  refine @ennreal.rpow_lt_top_of_nonneg _ (1/p) (by simp [hp_pos.le]) _,
  rw [lintegral_add' hf.nnnorm.ennreal_coe.ennreal_rpow_const
    hg.nnnorm.ennreal_coe.ennreal_rpow_const, ennreal.add_ne_top, ←lt_top_iff_ne_top,
    ←lt_top_iff_ne_top],
  exact ⟨lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top hp_pos hf_snorm,
    lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top hp_pos hg_snorm⟩,
end

lemma snorm_add_lt_top {f g : α → E} (hf : mem_ℒp f q μ) (hg : mem_ℒp g q μ) :
  snorm (f + g) q μ < ⊤ :=
begin
  by_cases h0 : q = 0,
  { simp [h0], },
  rw ←ne.def at h0,
  cases le_total 1 q with hq1 hq1,
  { exact snorm_add_lt_top_of_one_le hf hg hq1, },
  have hq_top : q ≠ ⊤, from (lt_of_le_of_lt hq1 ennreal.coe_lt_top).ne,
  have hq_pos : 0 < q.to_real,
  { rw [←ennreal.zero_to_real, @ennreal.to_real_lt_to_real 0 q ennreal.coe_ne_top hq_top],
    exact ((zero_le q).lt_of_ne h0.symm), },
  have hq1_real : q.to_real ≤ 1,
  { rwa [←ennreal.one_to_real, @ennreal.to_real_le_to_real q 1 hq_top ennreal.coe_ne_top], },
  rw snorm_eq_snorm' h0 hq_top,
  rw [mem_ℒp, snorm_eq_snorm' h0 hq_top] at hf hg,
  exact snorm'_add_lt_top_of_le_one hf.1 hg.1 hf.2 hg.2 hq_pos hq1_real,
end

section second_countable_topology
variable [topological_space.second_countable_topology E]

lemma mem_ℒp.add {f g : α → E} (hf : mem_ℒp f q μ) (hg : mem_ℒp g q μ) : mem_ℒp (f + g) q μ :=
⟨ae_measurable.add hf.1 hg.1, snorm_add_lt_top hf hg⟩

lemma mem_ℒp.sub {f g : α → E} (hf : mem_ℒp f q μ) (hg : mem_ℒp g q μ) : mem_ℒp (f - g) q μ :=
by { rw sub_eq_add_neg, exact hf.add hg.neg }

end second_countable_topology

end borel_space

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]

lemma snorm'_const_smul {f : α → F} (c : 𝕜) (hp0_lt : 0 < p) :
  snorm' (c • f) p μ = (nnnorm c : ℝ≥0∞) * snorm' f p μ :=
begin
  rw snorm',
  simp_rw [pi.smul_apply, nnnorm_smul, ennreal.coe_mul,
    ennreal.mul_rpow_of_nonneg _ _ (le_of_lt hp0_lt)],
  suffices h_integral : ∫⁻ a, ↑(nnnorm c) ^ p * ↑(nnnorm (f a)) ^ p ∂μ
    = (nnnorm c : ℝ≥0∞)^p * ∫⁻ a, (nnnorm (f a)) ^ p ∂μ,
  { apply_fun (λ x, x ^ (1/p)) at h_integral,
    rw [h_integral, @ennreal.mul_rpow_of_nonneg _ _ (1/p) (by simp [le_of_lt hp0_lt])],
    congr,
    simp_rw [←ennreal.rpow_mul, one_div, mul_inv_cancel (ne_of_lt hp0_lt).symm,
      ennreal.rpow_one], },
  rw lintegral_const_mul',
  rw ennreal.coe_rpow_of_nonneg _ (le_of_lt hp0_lt),
  exact ennreal.coe_ne_top,
end

lemma snorm_ess_sup_const_smul {f : α → F} (c : 𝕜) :
  snorm_ess_sup (c • f) μ = (nnnorm c : ℝ≥0∞) * snorm_ess_sup f μ :=
by simp_rw [snorm_ess_sup,  pi.smul_apply, nnnorm_smul, ennreal.coe_mul, ennreal.ess_sup_const_mul]

lemma snorm_const_smul {f : α → F} (c : 𝕜) :
  snorm (c • f) q μ = (nnnorm c : ℝ≥0∞) * snorm f q μ :=
begin
  by_cases h0 : q = 0,
  { simp [h0], },
  by_cases h_top : q = ⊤,
  { simp [h_top, snorm_ess_sup_const_smul], },
  repeat { rw snorm_eq_snorm' h0 h_top, },
  rw ←ne.def at h0,
  exact snorm'_const_smul c
    (ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) h0.symm, h_top⟩),
end

lemma mem_ℒp.const_smul [borel_space E] {f : α → E} (hf : mem_ℒp f q μ) (c : 𝕜) :
  mem_ℒp (c • f) q μ :=
⟨ae_measurable.const_smul hf.1 c,
  lt_of_le_of_lt (le_of_eq (snorm_const_smul c)) (ennreal.mul_lt_top ennreal.coe_lt_top hf.2)⟩

lemma snorm'_smul_le_mul_snorm' [opens_measurable_space E] [measurable_space 𝕜]
  [opens_measurable_space 𝕜] {q r : ℝ}
  {f : α → E} (hf : ae_measurable f μ) {φ : α → 𝕜} (hφ : ae_measurable φ μ)
  (hp0_lt : 0 < p) (hpq : p < q) (hpqr : 1/p = 1/q + 1/r) :
  snorm' (φ • f) p μ ≤ snorm' φ q μ * snorm' f r μ :=
begin
  simp_rw [snorm', pi.smul_apply', nnnorm_smul, ennreal.coe_mul],
  exact ennreal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hφ.nnnorm.ennreal_coe
    hf.nnnorm.ennreal_coe,
end

end normed_space

end ℒp

/-! ### Lp space

The space of equivalence classes of measurable functions for which `snorm f p μ < ⊤`.
-/

@[simp] lemma snorm_ae_eq_fun {α E : Type*} [measurable_space α] {μ : measure α}
  [measurable_space E] [normed_group E] {p : ℝ≥0∞} {f : α → E} (hf : ae_measurable f μ) :
  snorm (ae_eq_fun.mk f hf) p μ = snorm f p μ :=
snorm_congr_ae (ae_eq_fun.coe_fn_mk _ _)

lemma mem_ℒp.snorm_mk_lt_top {α E : Type*} [measurable_space α] {μ : measure α}
  [measurable_space E] [normed_group E] {p : ℝ≥0∞} {f : α → E} (hfp : mem_ℒp f p μ) :
  snorm (ae_eq_fun.mk f hfp.1) p μ < ⊤ :=
by simp [hfp.2]

/-- Lp space -/
def Lp {α} (E : Type*) [measurable_space α] [measurable_space E] [normed_group E]
  [borel_space E] [topological_space.second_countable_topology E]
  (p : ℝ≥0∞) (μ : measure α) : add_subgroup (α →ₘ[μ] E) :=
{ carrier := {f | snorm f p μ < ⊤},
  zero_mem' := by simp [snorm_congr_ae ae_eq_fun.coe_fn_zero, snorm_zero],
  add_mem' := λ f g hf hg, by simp [snorm_congr_ae (ae_eq_fun.coe_fn_add _ _),
    snorm_add_lt_top ⟨f.ae_measurable, hf⟩ ⟨g.ae_measurable, hg⟩],
  neg_mem' := λ f hf,
    by rwa [set.mem_set_of_eq, snorm_congr_ae (ae_eq_fun.coe_fn_neg _), snorm_neg] }

/-- make an element of Lp from a function verifying `mem_ℒp` -/
def mem_ℒp.to_Lp {α E} [measurable_space α] [measurable_space E] [normed_group E]
  [borel_space E] [topological_space.second_countable_topology E]
  (f : α → E) {p : ℝ≥0∞} {μ : measure α} (h_mem_ℒp : mem_ℒp f p μ) : Lp E p μ :=
⟨ae_eq_fun.mk f h_mem_ℒp.1, h_mem_ℒp.snorm_mk_lt_top⟩

lemma mem_ℒp.coe_fn_to_Lp {α E} [measurable_space α] [measurable_space E] [normed_group E]
  [borel_space E] [topological_space.second_countable_topology E] {μ : measure α} {p : ℝ≥0∞}
  {f : α → E} (hf : mem_ℒp f p μ) : hf.to_Lp f =ᵐ[μ] f :=
ae_eq_fun.coe_fn_mk _ _

namespace Lp

variables {α E F : Type*} [measurable_space α] {μ : measure α} [measurable_space E] [normed_group E]
  [borel_space E] [topological_space.second_countable_topology E] {p : ℝ≥0∞}

lemma mem_Lp_iff_snorm_lt_top {f : α →ₘ[μ] E} : f ∈ Lp E p μ ↔ snorm f p μ < ⊤ := iff.refl _

lemma antimono [finite_measure μ] {p q : ℝ≥0∞} (hpq : p ≤ q) : Lp E q μ ≤ Lp E p μ :=
λ f hf, (mem_ℒp.mem_ℒp_of_exponent_le ⟨f.ae_measurable, hf⟩ hpq).2

lemma coe_fn_mk {f : α →ₘ[μ] E} (hf : snorm f p μ < ⊤) : ⇑(⟨f, hf⟩ : Lp E p μ) =ᵐ[μ] f :=
by simp only [coe_fn_coe_base, subtype.coe_mk]

lemma snorm_lt_top (f : Lp E p μ) : snorm f p μ < ⊤ := f.prop

lemma snorm_ne_top (f : Lp E p μ) : snorm f p μ ≠ ⊤ := (snorm_lt_top f).ne

lemma measurable (f : Lp E p μ) : measurable f := f.val.measurable

lemma ae_measurable (f : Lp E p μ) : ae_measurable f μ := f.val.ae_measurable

lemma mem_ℒp (f : Lp E p μ) : mem_ℒp f p μ := ⟨ae_measurable f, f.prop⟩

lemma coe_fn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0 := ae_eq_fun.coe_fn_zero

lemma coe_fn_neg {f : Lp E p μ} : ⇑(-f) =ᵐ[μ] -f := ae_eq_fun.coe_fn_neg _

lemma coe_fn_add {f g : Lp E p μ} : ⇑(f + g) =ᵐ[μ] f + g := ae_eq_fun.coe_fn_add _ _

lemma coe_fn_sub {f g : Lp E p μ} : ⇑(f - g) =ᵐ[μ] f - g := ae_eq_fun.coe_fn_sub _ _

lemma mem_Lp_const (α) [measurable_space α] (μ : measure α) (c : E) [finite_measure μ] :
  @ae_eq_fun.const α _ _ μ _ c ∈ Lp E p μ :=
(mem_ℒp_const c).snorm_mk_lt_top

instance : has_norm (Lp E p μ) := { norm := λ f, ennreal.to_real (snorm f p μ) }

lemma norm_def (f : Lp E p μ) : ∥f∥ = ennreal.to_real (snorm f p μ) := rfl

@[simp] lemma norm_zero : ∥(0 : Lp E p μ)∥ = 0 :=
by simp [norm, snorm_congr_ae ae_eq_fun.coe_fn_zero, snorm_zero]

lemma norm_eq_zero_iff {f : Lp E p μ} (hp : 0 < p) : ∥f∥ = 0 ↔ f = 0 :=
begin
  refine ⟨λ hf, _, λ hf, by simp [hf]⟩,
  rw [norm_def, ennreal.to_real_eq_zero_iff] at hf,
  cases hf,
  { rw snorm_eq_zero_iff (ae_measurable f) hp.ne.symm at hf,
    exact subtype.eq (ae_eq_fun.ext (hf.trans ae_eq_fun.coe_fn_zero.symm)), },
  { exact absurd hf (snorm_ne_top f), },
end

@[simp] lemma norm_neg {f : Lp E p μ} : ∥-f∥ = ∥f∥ :=
by rw [norm_def, norm_def, snorm_congr_ae coe_fn_neg, snorm_neg]

instance [hp : fact (1 ≤ p)] : normed_group (Lp E p μ) :=
normed_group.of_core _
{ norm_eq_zero_iff := λ f, norm_eq_zero_iff (ennreal.zero_lt_one.trans_le hp),
  triangle := begin
    assume f g,
    simp only [norm_def],
    rw ← ennreal.to_real_add (snorm_ne_top f) (snorm_ne_top g),
    suffices h_snorm : snorm ⇑(f + g) p μ ≤ snorm ⇑f p μ + snorm ⇑g p μ,
    { rwa ennreal.to_real_le_to_real (snorm_ne_top (f + g)),
      exact ennreal.add_ne_top.mpr ⟨snorm_ne_top f, snorm_ne_top g⟩, },
    rw [snorm_congr_ae coe_fn_add],
    exact snorm_add_le (ae_measurable f) (ae_measurable g) hp,
  end,
  norm_neg := by simp }

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 E]

lemma mem_Lp_const_smul (c : 𝕜) (f : Lp E p μ) : c • ↑f ∈ Lp E p μ :=
begin
  rw [mem_Lp_iff_snorm_lt_top, snorm_congr_ae (ae_eq_fun.coe_fn_smul _ _), snorm_const_smul,
    ennreal.mul_lt_top_iff],
  exact or.inl ⟨ennreal.coe_lt_top, f.prop⟩,
end

instance : has_scalar 𝕜 (Lp E p μ) := { smul := λ c f, ⟨c • ↑f, mem_Lp_const_smul c f⟩ }

lemma coe_fn_smul {f : Lp E p μ} {c : 𝕜} : ⇑(c • f) =ᵐ[μ] c • f := ae_eq_fun.coe_fn_smul _ _

instance : semimodule 𝕜 (Lp E p μ) :=
{ one_smul := λ _, subtype.eq (one_smul 𝕜 _),
  mul_smul := λ _ _ _, subtype.eq (mul_smul _ _ _),
  smul_add := λ _ _ _, subtype.eq (smul_add _ _ _),
  smul_zero := λ _, subtype.eq (smul_zero _),
  add_smul := λ _ _ _, subtype.eq (add_smul _ _ _),
  zero_smul := λ _, subtype.eq (zero_smul _ _) }

lemma norm_const_smul (c : 𝕜) (f : Lp E p μ) : ∥c • f∥ = ∥c∥ * ∥f∥ :=
by rw [norm_def, snorm_congr_ae coe_fn_smul, snorm_const_smul c,
  ennreal.to_real_mul, ennreal.coe_to_real, coe_nnnorm, norm_def]

instance [fact (1 ≤ p)] : normed_space 𝕜 (Lp E p μ) :=
{ norm_smul_le := λ _ _, by simp [norm_const_smul] }

end normed_space

end Lp

lemma finset.prop_sum_of_subadditive {α γ} [add_comm_monoid α]
  (p : α → Prop) (hp_add : ∀ x y, p x → p y → p (x + y)) (hp_zero : p 0) (g : γ → α) :
  ∀ (s : finset γ) (hs : ∀ x, x ∈ s → p (g x)), p (∑ x in s, g x) :=
begin
  refine finset.induction (by simp [hp_zero]) _,
  intros a s ha h hpsa,
  rw finset.sum_insert ha,
  exact hp_add _ _ (hpsa a (finset.mem_insert_self a s))
    (h (λ x hx, hpsa x (finset.mem_insert_of_mem hx))),
end

lemma finset.le_sum_of_subadditive' {α β γ} [add_comm_monoid α] [ordered_add_comm_monoid β]
  (f : α → β) (h_zero : f 0 = 0) (p : α → Prop) (h_add : ∀ x y, p x → p y → f (x + y) ≤ f x + f y)
  (hp_add : ∀ x y, p x → p y → p (x + y)) (hp_zero : p 0) (g : γ → α) :
  ∀ (s : finset γ) (hs : ∀ x, x ∈ s → p (g x)), f (∑ x in s, g x) ≤ ∑ x in s, f (g x) :=
begin
  refine finset.induction (by simp [h_zero]) _,
  intros a s ha hs hsa,
  rw finset.sum_insert ha,
  have hsa_restrict : (∀ (x : γ), x ∈ s → p (g x)),
    from λ x hx, hsa x (finset.mem_insert_of_mem hx),
  have hp_sup : p ∑ (x : γ) in s, g x,
    from finset.prop_sum_of_subadditive p hp_add hp_zero g s hsa_restrict,
  have hp_ga : p (g a), from hsa a (finset.mem_insert_self a s),
  refine le_trans (h_add (g a) _ hp_ga hp_sup) _,
  rw finset.sum_insert ha,
  exact add_le_add_left (hs hsa_restrict) _,
end

variables {α E F : Type*} [measurable_space α] {μ : measure α} [measurable_space E] [normed_group E]
  [borel_space E] [topological_space.second_countable_topology E]
  [normed_group F]

lemma snorm'_sum_le {ι} {f : ι → α → E} {s : finset ι} {p : ℝ}
  (hfs : ∀ i, i ∈ s → ae_measurable (f i) μ) (hp1 : 1 ≤ p) :
  snorm' (∑ i in s, f i) p μ ≤ ∑ i in s, snorm' (f i) p μ :=
begin
  refine @finset.le_sum_of_subadditive' (α → E) ennreal ι _ _ (λ f, snorm' f p μ)
    (snorm'_zero (zero_lt_one.trans_le hp1)) (λ f, ae_measurable f μ) _
    (λ x y, ae_measurable.add) (@measurable_zero E α _ _ _).ae_measurable _ _ hfs,
  exact λ f g hf hg, snorm'_add_le hf hg hp1,
end

lemma snorm_sum_le {ι} {f : ι → α → E} {s : finset ι} {p : ennreal}
  (hfs : ∀ i, i ∈ s → ae_measurable (f i) μ) (hp1 : 1 ≤ p) :
  snorm (∑ i in s, f i) p μ ≤ ∑ i in s, snorm (f i) p μ :=
begin
  refine @finset.le_sum_of_subadditive' (α → E) ennreal ι _ _ (λ f, snorm f p μ)
    snorm_zero (λ f, ae_measurable f μ) _
    (λ x y, ae_measurable.add) (@measurable_zero E α _ _ _).ae_measurable _ _ hfs,
  exact λ f g hf hg, snorm_add_le hf hg hp1,
end

@[simp] lemma snorm'_norm {f : α → F} {p : ℝ} : snorm' (λ a, ∥f a∥) p μ = snorm' f p μ :=
by simp_rw [snorm', nnnorm_norm]

lemma snorm_norm {f : α → F} {p : ennreal} : snorm (λ a, ∥f a∥) p μ = snorm f p μ :=
begin
  by_cases hp0 : p = 0,
  { simp [hp0], },
  by_cases hp_top : p = ⊤,
  { simp [hp_top, snorm_ess_sup], },
  simp [hp0, hp_top, snorm_eq_snorm'],
end

lemma temp {f : ℕ → α → E} (hf : ∀ n, ae_measurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p)
  {B : ℕ → ennreal} (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm' (f n - f m) p μ < B N)
  (n : ℕ) :
  snorm' (λ x, ∑ i in finset.range (n + 1), norm (f (i + 1) x - f i x)) p μ ≤ tsum B :=
begin
  let f_norm_diff := λ i x, norm (f (i + 1) x - f i x),
  have hgf_norm_diff : ∀ n, (λ x, ∑ i in finset.range (n + 1), norm (f (i + 1) x - f i x))
    = ∑ i in finset.range (n + 1), f_norm_diff i,
  from λ n, funext (λ x, by simp [f_norm_diff]),
  rw hgf_norm_diff,
  refine le_trans (snorm'_sum_le _ hp1) _,
  { exact λ i _, ae_measurable.norm ((hf (i+1)).sub (hf i)), },
  simp only [f_norm_diff],
  simp_rw [←pi.sub_apply, snorm'_norm],
  refine le_trans (finset.sum_le_sum _) (sum_le_tsum _ _ ennreal.summable),
  { exact λ m _, le_of_lt (h_cau m (m + 1) m (nat.le_succ m) (le_refl m)), },
  { exact λ m _, zero_le _, },
end

lemma measurable.finset_sum' {β ι} [measurable_space β] [add_comm_monoid β]
  [topological_space β] [borel_space β] [topological_space.second_countable_topology β]
  [has_continuous_add β] {f : ι → α → β} {s : finset ι} (hf : ∀ i, i ∈ s → measurable (f i)) :
  measurable ∑ i in s, f i :=
begin
  refine @finset.prop_sum_of_subadditive (α → β) ι _ measurable _ _ f s hf,
  { exact λ x y hx hy, hx.add hy, },
  { exact @measurable_zero β α _ _ _, },
end

/-- private since it is superseded by the next lemma -/
private lemma liminf_map_le {α β ι} [complete_linear_order α] [complete_linear_order β] [preorder ι]
  {f : ι → α} {g : α → β} (hg_bij : function.bijective g) (hg_mono : monotone g) :
  filter.at_top.liminf (λ n, g (f n)) ≤ g (filter.at_top.liminf f) :=
begin
  have h_inv : ∃ (g_inv : β → α), function.left_inverse g_inv g ∧ function.right_inverse g_inv g,
  from function.bijective_iff_has_inverse.mp hg_bij,
  cases h_inv with g_inv h_inv,
  repeat { rw filter.liminf_eq, },
  refine Sup_le (λ x hx, _),
  refine le_trans _ (monotone.le_map_Sup _),
  rw set.mem_set_of_eq at hx,
  { refine le_trans _ (le_supr _ (g_inv x)),
    have hx_mem : g_inv x ∈ {a : α | ∀ᶠ n in filter.at_top, a ≤ f n},
    { rw set.mem_set_of_eq,
      refine filter.eventually.mp hx (filter.eventually_of_forall (λ n hn, _)),
      have h_inv_mono : monotone g_inv,
      { intros x y hxy,
        by_cases h_eq : x = y,
        { rw h_eq, },
        { have hxy' : x < y, from lt_of_le_of_ne hxy h_eq,
          rw ←h_inv.2 x at hxy',
          rw ←h_inv.2 y at hxy',
          exact le_of_lt (monotone.reflect_lt hg_mono hxy'), }, },
      rw (h_inv.1 (f n)).symm,
      exact h_inv_mono hn, },
    exact le_trans (le_of_eq (h_inv.2 x).symm) (le_supr _ hx_mem), },
  { exact hg_mono, },
end

lemma liminf_map_eq {α β ι} [complete_linear_order α] [complete_linear_order β] [preorder ι]
  {f : ι → α} {g : α → β} (hg_bij : function.bijective g) (hg_mono : monotone g) :
  filter.at_top.liminf (λ n, g (f n)) = g (filter.at_top.liminf f) :=
begin
  refine le_antisymm (liminf_map_le hg_bij hg_mono) _,
  have h_inv : ∃ (g_inv : β → α), function.left_inverse g_inv g ∧ function.right_inverse g_inv g,
  from function.bijective_iff_has_inverse.mp hg_bij,
  cases h_inv with g_inv h_inv,
  have h_inv_mono : monotone g_inv,
  { intros x y hxy,
    by_cases h_eq : x = y,
    { rw h_eq, },
    { have hxy' : x < y, from lt_of_le_of_ne hxy h_eq,
      rw [←h_inv.2 x, ←h_inv.2 y] at hxy',
      exact le_of_lt (monotone.reflect_lt hg_mono hxy'), }, },
  rw ←h_inv.2 (filter.at_top.liminf (λ n, g (f n))),
  refine hg_mono _,
  have hf : f = λ i, g_inv(g (f i)),
  { ext i,
    exact (h_inv.1 (f i)).symm, },
  nth_rewrite 0 hf,
  refine liminf_map_le _ h_inv_mono,
  rw function.bijective_iff_has_inverse,
  exact ⟨g, ⟨h_inv.2, h_inv.1⟩⟩,
end

lemma sum_fun {α β ι : Type*} [add_comm_monoid β] {f : ι → α → β} {s : finset ι}:
  (∑ i in s, f i) = λ x, ∑ i in s, f i x :=
funext (λ x, finset.sum_apply _ _ _)

lemma temp2 {f : ℕ → α → E} (hf : ∀ n, measurable (f n)) {p : ℝ} (hp1 : 1 ≤ p)
  {B : ℕ → ennreal} (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm' (f n - f m) p μ < B N) :
  (∫⁻ a, (∑' i, nnnorm (f (i + 1) a - f i a) : ennreal)^p ∂μ) ^ (1/p) ≤ tsum B :=
begin
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1,
  have hp_ne_zero : p ≠ 0 := hp_pos.ne.symm,
  suffices h_pow : ∫⁻ a, (∑' i, nnnorm (f (i + 1) a - f i a) : ennreal)^p ∂μ ≤ (tsum B) ^ p,
  by rwa [@ennreal.rpow_le_iff _ _ (1/p) (by simp [hp_pos]), one_div_one_div],
  have hn : ∀ n, ∫⁻ a, (∑ i in finset.range (n + 1), nnnorm (f (i + 1) a - f i a) : ennreal)^p ∂μ
    ≤ (tsum B) ^ p,
  { intro n,
    let hn_snorm := temp (λ n, (hf n).ae_measurable) hp1 h_cau n,
    rw [←one_div_one_div p, ←@ennreal.rpow_le_iff _ _ (1/p) (by simp [hp_pos]), one_div_one_div p],
    simp only [snorm] at hn_snorm,
    have h_nnnorm_nonneg :
      (λ a, (nnnorm (∑ i in finset.range (n + 1), ∥f (i + 1) a - f i a∥) : ennreal) ^ p)
      = λ a, (∑ i in finset.range (n + 1), (nnnorm( f (i + 1) a - f i a) : ennreal)) ^ p,
    { ext1 a,
      congr,
      simp_rw ←of_real_norm_eq_coe_nnnorm,
      rw ←ennreal.of_real_sum,
      { rw real.norm_of_nonneg _,
        exact finset.sum_nonneg (λ x hx, norm_nonneg _), },
      { exact λ x hx, norm_nonneg _, }, },
    change (∫⁻ a, (λ x, ↑(nnnorm (∑ i in finset.range (n + 1), ∥f (i+1) x - f i x∥))^p) a ∂μ)^(1/p)
      ≤ tsum B at hn_snorm,
    rwa h_nnnorm_nonneg at hn_snorm, },
  simp_rw ennreal.tsum_eq_liminf,
  rw ←ennreal.tsum_eq_liminf,
  have h_liminf_pow : ∫⁻ a, filter.at_top.liminf (λ n, ∑ i in finset.range (n + 1),
      (nnnorm (f (i + 1) a - f i a)))^p ∂μ
    = ∫⁻ a, filter.at_top.liminf (λ n, (∑ i in finset.range (n + 1),
      (nnnorm (f (i + 1) a - f i a)))^p) ∂μ,
  { refine lintegral_congr (λ x, _),
    have h_rpow_mono : monotone (λ x : ennreal, x^p),
    { intros x y hxy,
      exact ennreal.rpow_le_rpow hxy (le_trans zero_le_one hp1), },
    have h_rpow_bij :function.bijective (λ x : ennreal, x^p),
    from ennreal.bijective_rpow_const_of_ne_zero hp_ne_zero,
    rw liminf_map_eq h_rpow_bij h_rpow_mono, },
  rw h_liminf_pow,
  refine le_trans (lintegral_liminf_le _) _,
  { refine λ n, measurable.ennreal_rpow_const _,
    rw ←sum_fun,
    let g := λ i x, (nnnorm (f (i + 1) x - f i x) : ennreal),
    refine @measurable.finset_sum' α _ ennreal ℕ _ _ _ _ _ _ g (finset.range (n+1)) _,
    exact λ i hi, ((hf (i+1)).sub (hf i)).nnnorm.ennreal_coe, },
  { rw filter.liminf_eq,
    refine Sup_le (λ x hx, _),
    rw [set.mem_set_of_eq, filter.eventually_at_top] at hx,
    exact le_trans (hx.some_spec hx.some (le_refl hx.some)) (hn hx.some), },
end

lemma tsum_nnnorm_sub_lt_top_of_cauchy_snorm {f : ℕ → α → E} (hf : ∀ n, ae_measurable (f n) μ)
  {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ennreal} (hB : tsum B < ⊤)
  (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm' (f n - f m) p μ < B N) :
  ∀ᵐ x ∂μ, (∑' i, nnnorm (f (i + 1) x - f i x) : ennreal) < ⊤ :=
begin
  let prop : α → (ℕ → E) → Prop := λ x fn, true,
  have hprop : ∀ᵐ x ∂μ, prop x (λ n, f n x), by simp,
  let f' := ae_seq hf prop,
  have hf' := ae_seq.measurable hf prop,
  suffices h_goal_f' : ∀ᵐ x ∂μ, (∑' i, nnnorm (f' (i + 1) x - f' i x) : ennreal) < ⊤,
  { have h_eq : ∀ᵐ x ∂μ, (∑' i, nnnorm (f (i + 1) x - f i x) : ennreal)
      = (∑' i, nnnorm (f' (i + 1) x - f' i x) : ennreal),
    { refine (ae_seq_eq_fun_ae hf hprop).mono (λ x hx, _),
      congr,
      ext i,
      simp_rw [hx i, hx (i + 1)], },
    refine h_goal_f'.mp (h_eq.mono (λ x hx h_lt_top, _)),
    rwa hx, },
  have h_cau' : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm (f' n - f' m) p μ < B N,
  { intros N n m hn hm,
    have h_ae_eq : f' n - f' m =ᵐ[μ] f n - f m,
    { have h_eq := ae_seq_eq_fun_ae hf hprop,
      refine h_eq.mono (λ x hx, _),
      dsimp only at hx,
      rw [pi.sub_apply, pi.sub_apply, hx n, hx m], },
    rw snorm_congr_ae h_ae_eq,
    exact h_cau N n m hn hm, },
  have h_integral : ∫⁻ a, (∑' i, nnnorm (f' (i + 1) a - f' i a) : ennreal)^p ∂μ < ⊤,
  { have h_tsum_lt_top : (tsum B) ^ p < ⊤,
    from ennreal.rpow_lt_top_of_nonneg (le_trans zero_le_one hp1) (lt_top_iff_ne_top.mp hB),
    refine lt_of_le_of_lt _ h_tsum_lt_top,
    have h := temp2 hf' hp1 h_cau',
    rw @ennreal.rpow_le_iff _ _ (1/p) (by simp [(lt_of_lt_of_le zero_lt_one hp1)]) at h,
    rwa one_div_one_div at h, },
  have rpow_ae_lt_top : ∀ᵐ x ∂μ, (∑' i, nnnorm (f' (i + 1) x - f' i x) : ennreal)^p < ⊤,
  { refine ae_lt_top (measurable.ennreal_rpow_const _) h_integral,
    exact measurable.ennreal_tsum (λ n, ((hf' (n+1)).sub (hf' n)).nnnorm.ennreal_coe), },
  refine rpow_ae_lt_top.mono (λ x hx, _),
  rw ←ennreal.rpow_one (∑' (i : ℕ), ↑(nnnorm (f' (i + 1) x - f' i x))),
  rw [←@mul_inv_cancel _ _ p (ne_of_lt (lt_of_lt_of_le zero_lt_one hp1)).symm, ennreal.rpow_mul],
  exact @ennreal.rpow_lt_top_of_nonneg _ p⁻¹ (by simp [le_trans zero_le_one hp1])
    (lt_top_iff_ne_top.mp hx),
end

lemma summable_sub_of_cauchy_snorm [complete_space E] {f : ℕ → α → E}
  (hf : ∀ n, ae_measurable (f n) μ) (hp1 : 1 ≤ p) {B : ℕ → ennreal} (hB : tsum B < ⊤)
  (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N) :
  ∀ᵐ x ∂μ, summable (λ (i : ℕ), f (i + 1) x - f i x) :=
(tsum_nnnorm_sub_lt_top_of_cauchy_snorm hf hp1 hB h_cau).mono(λ x hx, summable_of_summable_nnnorm
  (ennreal.tsum_coe_ne_top_iff_summable.mp (lt_top_iff_ne_top.mp hx)))

lemma ae_tendsto_of_cauchy_snorm [complete_space E] {f : ℕ → α → E}
  (hf : ∀ n, ae_measurable (f n) μ) (hp1 : 1 ≤ p) {B : ℕ → ennreal} (hB : tsum B < ⊤)
  (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N) :
  ∀ᵐ x ∂μ, ∃ l : E, filter.at_top.tendsto (λ n, f n x) (nhds l) :=
begin
  have h_summable := summable_sub_of_cauchy_snorm hf hp1 hB h_cau,
  have h : ∀ᵐ x ∂μ, ∃ l : E,
    filter.at_top.tendsto (λ n, ∑ i in finset.range n, (f (i + 1) x - f i x)) (nhds l),
  { refine filter.eventually.mp h_summable (filter.eventually_of_forall (λ x hx, _)),
    let hx_sum := (summable.has_sum_iff_tendsto_nat hx).mp hx.has_sum,
    exact Exists.intro (∑' i, f (i + 1) x - f i x) hx_sum, },
  refine filter.eventually.mp h (filter.eventually_of_forall (λ x hx, _)),
  cases hx with l hx,
  have h_rw_sum : (λ n, ∑ i in finset.range n, (f (i + 1) x - f i x)) = λ n, f n x - f 0 x,
  { ext1 n,
    change ∑ (i : ℕ) in finset.range n, ((λ m, f m x) (i + 1) - (λ m, f m x) i) = f n x - f 0 x,
    rw finset.sum_range_sub, },
  rw h_rw_sum at hx,
  have hf_rw : (λ n, f n x) = λ n, f n x - f 0 x + f 0 x, by { ext1 n, abel, },
  rw hf_rw,
  exact Exists.intro (l + f 0 x) (tendsto.add_const _ hx),
end

lemma complete_ℒp_minus_ℒp [complete_space E] {f : ℕ → α → E}
  (hf : ∀ n, mem_ℒp (f n) p μ) (hp1 : 1 ≤ p) {B : ℕ → ennreal} (hB : tsum B < ⊤)
  (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N) :
  ∃ (f_lim : α → E) (hf_lim_meas : ae_measurable f_lim μ),
    ∀ (ε : ennreal), 0 < ε → ε < ⊤ → (∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → snorm (f n - f_lim) p μ < ε) :=
begin
  have hp_pos := lt_of_lt_of_le zero_lt_one hp1,
  have hp_ne_zero := (ne_of_lt hp_pos).symm,
  have h_lim_meas : ∃ (f_lim : α → E) (hf_lim_meas : ae_measurable f_lim μ),
    ∀ᵐ x ∂μ, filter.tendsto (λ n, f n x) filter.at_top (nhds (f_lim x)),
  from ae_measurable_limit_of_tendsto_ae (λ n, (hf n).1)
    (ae_tendsto_of_cauchy_snorm (λ n, (hf n).1) hp1 hB h_cau),
  rcases h_lim_meas with ⟨f_lim, h_f_lim_meas, h_lim⟩,
  use [f_lim, h_f_lim_meas],
  have h_snorm_lim_rw : ∀ n, snorm (f n - f_lim) p μ
    = (∫⁻ a, filter.at_top.liminf (λ m, (nnnorm (f n a - f m a) : ennreal)^p) ∂μ) ^ (1/p),
  from snorm_lim hp1 h_lim,
  simp_rw h_snorm_lim_rw,
  intros ε hε hε_top,
  have h_integral : ∃ (N : ℕ), ∀ (n m : ℕ), n ≥ N → m ≥ N
    → ∫⁻ a, (nnnorm (f n a - f m a) : ennreal) ^ p ∂μ < ε^p/2,
  { suffices h_snorm : ∃ (N : ℕ), ∀ (n m : ℕ), n ≥ N → m ≥ N → snorm (f n - f m) p μ < ε/2^(1/p),
    { cases h_snorm with N h_snorm,
      use N,
      intros n m hn hm,
      specialize h_snorm n m hn hm,
      rw [snorm, ennreal.div_def, ←ennreal.rpow_one ε,
        ←@ennreal.inv_rpow_of_pos _ (1/p) (by simp [hp_pos]), one_div, ←mul_inv_cancel hp_ne_zero,
        ennreal.rpow_mul, ←@ennreal.mul_rpow_of_nonneg _ _ p⁻¹ (by simp [le_of_lt hp_pos]),
        ←@ennreal.rpow_lt_rpow_iff _ _ p⁻¹ (by simp [hp_pos])] at h_snorm,
      simp_rw pi.sub_apply at h_snorm,
      rwa ennreal.div_def, },
    suffices h_B : ∃ (N : ℕ), B N ≤ ε/2^(1/p),
    { cases h_B with N h_B,
      exact Exists.intro N (λ n m hn hm, lt_of_lt_of_le (h_cau N n m hn hm) h_B), },
    have hε2_pos : 0 < ε/2^(1/p),
    { rw ennreal.div_pos_iff,
      refine ⟨(ne_of_lt hε).symm, _⟩,
      rw [ne.def, @ennreal.rpow_eq_top_iff_of_pos _ (1/p) (by simp [hp_pos])],
      exact ennreal.two_ne_top, },
    have h_tendsto_zero :=
      ennreal.exists_le_of_tendsto_zero (ennreal.tendsto_zero_of_tsum_lt_top hB) hε2_pos,
    cases h_tendsto_zero with N h_tendsto_zero,
    exact Exists.intro N (h_tendsto_zero N (le_refl N)), },
  rcases h_integral with ⟨N, h_⟩,
  use N,
  intros n hnN,
  suffices h_lt_pow : (∫⁻ a, filter.at_top.liminf (λ (m : ℕ), (nnnorm (f n a - f m a)) ^ p) ∂μ)
    < ε^p,
  { rw ←ennreal.rpow_one ε,
    nth_rewrite 1 ←@mul_inv_cancel _ _ p hp_ne_zero,
    rw [←one_div, ennreal.rpow_mul],
    exact @ennreal.rpow_lt_rpow _ _ (1/p) h_lt_pow (by simp [hp_pos]), },
  refine lt_of_le_of_lt (ae_lintegral_liminf_le (λ m,
    ((hf n).1.sub (hf m).1).nnnorm.ennreal_coe.ennreal_rpow_const)) _,
  rw filter.liminf_eq,
  have hε2 : ε^p/2 < ε^p,
  { rw [ennreal.div_def, mul_comm],
    nth_rewrite 1 ←one_mul (ε^p),
    refine ennreal.mul_lt_mul' (by simp [one_lt_two]) (le_refl (ε^p)) _ _,
    { exact ennreal.rpow_lt_top_of_nonneg (le_of_lt hp_pos) (lt_top_iff_ne_top.mp hε_top), },
    { exact ennreal.rpow_pos_of_pos hε hp_pos, }, },
  refine lt_of_le_of_lt (Sup_le (λ b hb, _)) hε2,
  rw [set.mem_set_of_eq, filter.eventually_at_top] at hb,
  cases hb with N1 hb,
  exact le_trans (hb (max N N1) (le_max_right _ _))
    (le_of_lt (h_ n (max N N1) hnN (le_max_left _ _))),
end

lemma cauchy_complete_ℒp [complete_space E] {f : ℕ → α → E} (hf : ∀ n, mem_ℒp (f n) p μ)
  (hp1 : 1 ≤ p) {B : ℕ → ennreal} (hB : tsum B < ⊤)
  (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N) :
  ∃ (f_lim : α → E) (hf_lim_ℒp : mem_ℒp f_lim p μ),
    ∀ (ε : ennreal), 0 < ε → ε < ⊤ → (∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → snorm (f n - f_lim) p μ < ε) :=
begin
  have h_almost := complete_ℒp_minus_ℒp hf hp1 hB h_cau,
  rcases h_almost with ⟨f_lim, f_lim_meas, h_tendsto⟩,
  have hf_lim_ℒp : mem_ℒp f_lim p μ,
  { refine ⟨f_lim_meas, _⟩,
    refine lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top (lt_of_lt_of_le zero_lt_one hp1) _,
    cases (h_tendsto 1 ennreal.zero_lt_one ennreal.one_lt_top) with N h_tendsto,
    specialize h_tendsto N (le_refl N),
    have h_add : f_lim = f_lim - f N + f N, by abel,
    rw h_add,
    refine lt_of_le_of_lt (snorm_add_le (f_lim_meas.sub (hf N).1) (hf N).1 hp1) _,
    rw ennreal.add_lt_top,
    split,
    { refine lt_of_lt_of_le _ (@le_top ennreal _ 1),
      have h_neg : f_lim - f N = -(f N - f_lim), by simp,
      rwa [h_neg, snorm_neg], },
    { exact mem_ℒp.snorm_lt_top (le_trans zero_le_one hp1) (hf N), }, },
  use [f_lim, hf_lim_ℒp],
  exact h_tendsto,
end

lemma tendsto_Lp_of_tendsto_ℒp {f : ℕ → Lp α E hp μ}
  (h_tendsto : ∃ (f_lim : α → E) (hf_lim_meas : mem_ℒp f_lim p μ),
    ∀ (ε : ennreal), 0 < ε → ε < ⊤ → (∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → snorm (f n - f_lim) p μ < ε)) :
  ∃ (g : Lp α E hp μ), filter.at_top.tendsto f (nhds g) :=
begin
  simp_rw metric.tendsto_at_top,
  rcases h_tendsto with ⟨f_lim, f_lim_ℒp, h_tendsto⟩,
  use Lp.mk_of_fun f_lim hp f_lim_ℒp,
  intros ε hε,
  have hε_pos : 0 < ennreal.of_real ε, from ennreal.of_real_pos.mpr hε,
  specialize h_tendsto (ennreal.of_real ε) hε_pos ennreal.of_real_lt_top,
  cases h_tendsto with N h_tendsto,
  use N,
  intros n hn,
  specialize h_tendsto n hn,
  simp only [dist, Lp_norm],
  rw ←@ennreal.to_real_of_real ε (le_of_lt hε),
  rw ennreal.to_real_lt_to_real _ ennreal.of_real_ne_top,
  { have h_coe : ⇑(f n) - f_lim =ᵐ[μ] ⇑(f n) - ⇑(Lp.mk_of_fun f_lim hp f_lim_ℒp).val,
    { suffices h_coe' : f_lim =ᵐ[μ] ⇑(Lp.mk_of_fun f_lim hp f_lim_ℒp),
      { refine filter.eventually.mp h_coe' (filter.eventually_of_forall (λ x hx, _)),
        simp_rw pi.sub_apply,
        rw hx,
        refl, },
      exact (Lp.coe_fn_mk_of_fun _).symm, },
    rw snorm_congr_ae h_coe at h_tendsto,
    change snorm ⇑((f n).val - (Lp.mk_of_fun f_lim hp f_lim_ℒp).val) p μ < ennreal.of_real ε,
    rw snorm_congr_ae (ae_eq_fun.coe_fn_sub _ _),
    exact h_tendsto, },
  { exact mem_ℒp.snorm_ne_top (le_trans zero_le_one (f n).one_le_p)
      ((f n).mem_Lp.sub (Lp.mk_of_fun f_lim hp f_lim_ℒp).mem_Lp (f n).one_le_p), },
end

lemma tendsto_ℒp_of_tendsto_Lp {f : ℕ → Lp α E hp μ}
  (h_tendsto : ∃ (g : Lp α E hp μ), filter.at_top.tendsto f (nhds g)) :
  ∃ (f_lim : α → E) (hf_lim_meas : mem_ℒp f_lim p μ),
    ∀ (ε : ennreal), 0 < ε → ε < ⊤ → (∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → snorm (f n - f_lim) p μ < ε) :=
begin
  simp_rw metric.tendsto_at_top at h_tendsto,
  cases h_tendsto with g h_tendsto,
  use [g, g.mem_Lp],
  intros ε hε hε_top,
  have hε_pos : 0 < ε.to_real, from ennreal.to_real_pos_iff.mpr ⟨hε, lt_top_iff_ne_top.mp hε_top⟩,
  specialize h_tendsto ε.to_real hε_pos,
  cases h_tendsto with N h_tendsto,
  use N,
  intros n hn,
  specialize h_tendsto n hn,
  simp only [dist, Lp_norm] at h_tendsto,
  rw ennreal.to_real_lt_to_real _ (lt_top_iff_ne_top.mp hε_top) at h_tendsto,
  { rw snorm_congr_ae (@Lp.coe_fn_sub α E _ _ _ _ _ _ _ _ _ _).symm,
    exact h_tendsto, },
  rw ←lt_top_iff_ne_top,
  exact mem_ℒp.snorm_lt_top (le_trans zero_le_one hp) (f n - g).mem_Lp,
end

lemma tendsto_Lp_iff_tendsto_ℒp {f : ℕ → Lp α E hp μ} :
 (∃ (g : Lp α E hp μ), filter.at_top.tendsto f (nhds g))
  ↔ ∃ (f_lim : α → E) (hf_lim_meas : mem_ℒp f_lim p μ),
    ∀ (ε : ennreal), 0 < ε → ε < ⊤ → (∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → snorm (f n - f_lim) p μ < ε) :=
⟨λ h, tendsto_ℒp_of_tendsto_Lp h, λ h, tendsto_Lp_of_tendsto_ℒp h⟩

instance [complete_space E] : complete_space (Lp α E hp μ) :=
begin
  let B := λ n : ℕ, ((1:ℝ) / 2) ^ n,
  have hB_pos : ∀ n, 0 < B n, from λ n, pow_pos (div_pos zero_lt_one zero_lt_two) n,
  refine metric.complete_of_convergent_controlled_sequences B hB_pos (λ f hf, _),
  refine tendsto_Lp_of_tendsto_ℒp _,
  have hB : summable B, from summable_geometric_two,
  cases hB with M hB,
  let M1 := ennreal.of_real M,
  let B1 := λ n, ennreal.of_real (B n),
  have hM1 : M1 < ⊤, from ennreal.of_real_lt_top,
  have hB1_has : has_sum B1 M1,
  { have h_tsum_B1 : tsum B1 = M1,
    { change (∑' (n : ℕ), ennreal.of_real (B n)) = ennreal.of_real M,
      rw ←hB.tsum_eq,
      exact ennreal.tsum_of_real (λ n, le_of_lt (hB_pos n)) hB.summable, },
    have h_sum := (@ennreal.summable _ B1).has_sum,
    rwa h_tsum_B1 at h_sum, },
  have hB1 : tsum B1 < ⊤, by rwa hB1_has.tsum_eq,
  let f1 : ℕ → α → E := λ n, f n,
  have h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm (f1 n - f1 m) p μ < B1 N,
  { intros N n m hn hm,
    specialize hf N n m hn hm,
    rw ←@ennreal.of_real_to_real (snorm (f1 n - f1 m) p μ)
      (mem_ℒp.snorm_ne_top (le_trans zero_le_one hp) (mem_ℒp.sub (f n).mem_Lp (f m).mem_Lp hp)),
    rw ennreal.of_real_lt_of_real_iff (hB_pos N),
    rwa snorm_congr_ae Lp.coe_fn_sub.symm, },
  exact cauchy_complete_ℒp (λ n, (f n).mem_Lp) hp hB1 h_cau,
end


end measure_theory
