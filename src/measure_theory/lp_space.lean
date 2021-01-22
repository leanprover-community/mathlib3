/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rémy Degenne.
-/
import measure_theory.ess_sup
import measure_theory.l1_space
import analysis.mean_inequalities

/-!
# ℒp space and Lp space

This file describes properties of almost everywhere measurable functions with finite seminorm,
denoted by `snorm f p μ` and defined for `p:ennreal` as `0` if `p=0`, `(∫ ∥f a∥^p ∂μ) ^ (1/p)` for
`0 < p < ∞` and `ess_sup ∥f∥ μ` for `p=∞`.

The Prop-valued `mem_ℒp f p μ` states that a function `f : α → E` has finite seminorm.
The space `Lp α E p μ` is the subtype of elements of `α →ₘ[μ] E` (see ae_eq_fun) such that
`snorm f p μ` is finite. For `1 ≤ p`, `snorm` defines a norm and Lp is a metric space.

TODO: prove that Lp is complete.

## Main definitions

* `snorm' f p μ` : `(∫ ∥f a∥^p ∂μ) ^ (1/p)` for `f : α → F` and `p : ℝ`, where `α` is a  measurable
  space and `F` is a normed group.
* `snorm_ess_sup f μ` : seminorm in `ℒ∞`, equal to the essential supremum `ess_sup ∥f∥ μ`.
* `snorm f p μ` : for `p : ennreal`, seminorm in `ℒp`, equal to `0` for `p=0`, to `snorm' f p μ`
  for `0 < p < ∞` and to `snorm_ess_sup f μ` for `p = ∞`.

* `mem_ℒp f p μ` : property that the function `f` is almost everywhere measurable and has finite
  p-seminorm for measure `μ` (`snorm f p μ < ∞`)
* `Lp α E p μ := {f : α →ₘ[μ} E // snorm f p μ < ∞}` : elements of `α →ₘ[μ] E` (see ae_eq_fun) such
  that `snorm f p μ` is finite.

-/

open measure_theory

noncomputable theory

namespace Lp_space

section ℒp

variables {α E F : Type*} [measurable_space α] {μ : measure α}
  [measurable_space E] [normed_group E]
  [normed_group F]
  {p : ℝ} {q : ennreal}

section ℒp_space_definition

/-- `(∫ ∥f a∥^p ∂μ) ^ (1/p)`, which is a seminorm on the space of measurable functions for which
this quantity is finite -/
def snorm' (f : α → F) (p : ℝ) (μ : measure α) : ennreal := (∫⁻ a, (nnnorm (f a))^p ∂μ) ^ (1/p)

/-- seminorm for `ℒ∞`, equal to the essential supremum of `∥f∥`. -/
def snorm_ess_sup (f : α → F) (μ : measure α) := ess_sup (λ x, (nnnorm (f x) : ennreal)) μ

/-- `ℒp` seminorm, equal to `0` for `p=0`, to `(∫ ∥f a∥^p ∂μ) ^ (1/p)` for `0 < p < ∞` and to
`ess_sup ∥f∥ μ` for `p = ∞`. -/
def snorm (f : α → F) (q : ennreal) (μ : measure α) : ennreal :=
if q = 0 then 0 else (if q = ⊤ then snorm_ess_sup f μ else snorm' f (ennreal.to_real q) μ)

lemma snorm_eq_snorm' (hq_ne_zero : q ≠ 0) (hq_ne_top : q ≠ ⊤) {f : α → F} :
  snorm f q μ = snorm' f (ennreal.to_real q) μ :=
by simp [snorm, hq_ne_zero, hq_ne_top]

@[simp] lemma snorm_exponent_top {f : α → F} : snorm f ⊤ μ = snorm_ess_sup f μ := by simp [snorm]

/-- The property that `f:α→E` is ae_measurable and `(∫ ∥f a∥^p ∂μ)^(1/p)` is finite -/
def mem_ℒp (f : α → E) (p : ennreal) (μ : measure α) : Prop :=
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
  snorm' (λ x : α , c) p μ = (nnnorm c : ennreal) * (μ set.univ) ^ (1/p) :=
begin
  rw [snorm', lintegral_const, @ennreal.mul_rpow_of_nonneg _ _ (1/p) (by simp [le_of_lt hp_pos])],
  congr,
  rw ←ennreal.rpow_mul,
  suffices hp_cancel : p * (1/p) = 1, by rw [hp_cancel, ennreal.rpow_one],
  rw [one_div, mul_inv_cancel (ne_of_lt hp_pos).symm],
end

lemma snorm'_const' [finite_measure μ] (c : F) (hc_ne_zero : c ≠ 0) (hp_ne_zero : p ≠ 0) :
  snorm' (λ x : α , c) p μ = (nnnorm c : ennreal) * (μ set.univ) ^ (1/p) :=
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
  snorm_ess_sup (λ x : α, c) μ = (nnnorm c : ennreal) :=
by rw [snorm_ess_sup, ess_sup_const _ hμ]

lemma snorm'_const_of_probability_measure (c : F) (hp_pos : 0 < p) [probability_measure μ] :
  snorm' (λ x : α , c) p μ = (nnnorm c : ennreal) :=
by simp [snorm'_const c hp_pos, measure_univ]

lemma snorm_const (c : F) (h0 : q ≠ 0) (hμ : μ ≠ 0) :
  snorm (λ x : α , c) q μ = (nnnorm c : ennreal) * (μ set.univ) ^ (1/(ennreal.to_real q)) :=
begin
  by_cases h_top : q = ⊤,
  { simp [h_top, snorm_ess_sup_const c hμ], },
  simp [snorm_eq_snorm' h0 h_top, snorm'_const,
    ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) h0.symm, h_top⟩],
end

lemma snorm_const' (c : F) (h0 : q ≠ 0) (h_top: q ≠ ⊤) :
  snorm (λ x : α , c) q μ = (nnnorm c : ennreal) * (μ set.univ) ^ (1/(ennreal.to_real q)) :=
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
  ∀ᵐ x ∂μ, (nnnorm (f x) : ennreal) ≤ snorm_ess_sup f μ :=
ennreal.ae_le_ess_sup (λ x, (nnnorm (f x) : ennreal))

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
  let g := λ a : α, (1 : ennreal),
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

lemma snorm_le_snorm_of_exponent_le {p q : ennreal} (hpq : p ≤ q) [probability_measure μ]
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

lemma mem_ℒp.mem_ℒp_of_exponent_le {p q : ennreal} [finite_measure μ] {f : α → E}
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
    ≤ (∫⁻ a, (((λ a, (nnnorm (f a) : ennreal))
        + (λ a, (nnnorm (g a) : ennreal))) a) ^ p ∂μ) ^ (1 / p) :
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
    ≤ (∫⁻ a, (((λ a, (nnnorm (f a) : ennreal))
        + (λ a, (nnnorm (g a) : ennreal))) a) ^ p ∂μ) ^ (1 / p) :
begin
  refine @ennreal.rpow_le_rpow _ _ (1/p) _ (by simp [hp_pos.le]),
  refine lintegral_mono (λ a, ennreal.rpow_le_rpow _ hp_pos.le),
  simp [←ennreal.coe_add, nnnorm_add_le],
end
... ≤ (∫⁻ a, (nnnorm (f a) : ennreal) ^ p + (nnnorm (g a) : ennreal) ^ p ∂μ) ^ (1 / p) :
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
  snorm' (c • f) p μ = (nnnorm c : ennreal) * snorm' f p μ :=
begin
  rw snorm',
  simp_rw [pi.smul_apply, nnnorm_smul, ennreal.coe_mul,
    ennreal.mul_rpow_of_nonneg _ _ (le_of_lt hp0_lt)],
  suffices h_integral : ∫⁻ a, ↑(nnnorm c) ^ p * ↑(nnnorm (f a)) ^ p ∂μ
    = (nnnorm c : ennreal)^p * ∫⁻ a, (nnnorm (f a)) ^ p ∂μ,
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
  snorm_ess_sup (c • f) μ = (nnnorm c : ennreal) * snorm_ess_sup f μ :=
by simp_rw [snorm_ess_sup,  pi.smul_apply, nnnorm_smul, ennreal.coe_mul, ennreal.ess_sup_const_mul]

lemma snorm_const_smul {f : α → F} (c : 𝕜) :
  snorm (c • f) q μ = (nnnorm c : ennreal) * snorm f q μ :=
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

variables {α E F : Type*} [measurable_space α] {μ : measure α} [measurable_space E] [normed_group E]
  [normed_group F] {p : ennreal}

lemma mem_ℒp.snorm_mk_lt_top {f : α → E} (hfp : mem_ℒp f p μ) :
  snorm (@ae_eq_fun.mk α E _ μ _ f hfp.1) p μ < ⊤ :=
by { rw snorm_congr_ae (ae_eq_fun.coe_fn_mk _ _), exact hfp.2 }

/-- Lp space -/
def Lp (α E : Type*) [measurable_space α] [measurable_space E] [normed_group E]
  (p : ennreal) (μ : measure α) :=
{f : α →ₘ[μ] E // snorm f p μ < ⊤}

namespace Lp

lemma mk_coe_fn {f : Lp α E p μ} : (⟨f.val, f.prop⟩ : Lp α E p μ) = f := subtype.eq rfl

/-- make an element of Lp from a function verifying `mem_ℒp` -/
def mk_of_fun {f : α → E} (h_mem_ℒp : mem_ℒp f p μ) : Lp α E p μ :=
⟨@ae_eq_fun.mk α E _ μ _ f h_mem_ℒp.1, h_mem_ℒp.snorm_mk_lt_top⟩

instance : has_coe_to_fun (Lp α E p μ) := ⟨_, λ f, (f.val : α → E)⟩

lemma coe_fn_mk {f : α →ₘ[μ] E} (hf : snorm f p μ < ⊤) : (⟨f, hf⟩ : Lp α E p μ) =ᵐ[μ] f :=
by refl

lemma coe_fn_mk_of_fun {f : α → E} (hf : mem_ℒp f p μ) : mk_of_fun hf =ᵐ[μ] f :=
ae_eq_fun.coe_fn_mk _ _

lemma snorm_lt_top (f : Lp α E p μ) : snorm f p μ < ⊤ := f.prop

lemma snorm_ne_top (f : Lp α E p μ) : snorm f p μ ≠ ⊤ := f.prop.ne

lemma measurable (f : Lp α E p μ) : measurable f := f.val.measurable

lemma ae_measurable (f : Lp α E p μ) : ae_measurable f μ := f.val.ae_measurable

lemma mem_ℒp (f : Lp α E p μ) : mem_ℒp f p μ := ⟨f.ae_measurable, f.prop⟩

/-- The norm in Lp space (which verifies the triangle inequality only for `1 ≤ p`) -/
def Lp_norm (f : Lp α E p μ) : ℝ := ennreal.to_real (snorm f p μ)

instance : has_norm (Lp α E p μ) := { norm := λ f, Lp_norm f }

@[simp] lemma norm_eq_Lp_norm {f : Lp α E p μ} : ∥f∥ = Lp_norm f := rfl

lemma zero_mem_Lp : snorm (0 : α →ₘ[μ] E) p μ < ⊤ :=
by { rw snorm_congr_ae ae_eq_fun.coe_fn_zero, simp, }

instance : has_zero (Lp α E p μ) := { zero := ⟨0, zero_mem_Lp⟩ }

@[simp] lemma coe_zero : (0 : Lp α E p μ).val = (0 : α →ₘ[μ] E) := rfl

lemma coe_fn_zero : ⇑(0 : Lp α E p μ) =ᵐ[μ] 0 :=
ae_eq_fun.coe_fn_zero

instance : inhabited (Lp α E p μ) := ⟨0⟩

@[simp] lemma Lp_norm_zero : Lp_norm (0 : Lp α E p μ) = 0 :=
by simp [Lp_norm, snorm_congr_ae coe_fn_zero, snorm_zero]

lemma mem_Lp_const (α) [measurable_space α] (μ : measure α) (c : E) [finite_measure μ] :
  snorm (@ae_eq_fun.const α _ _ μ _ c) p μ < ⊤ :=
(mem_ℒp_const c).snorm_mk_lt_top

/-- Constant function, as an element of Lp -/
def const (c : E) [finite_measure μ] : Lp α E p μ := ⟨ae_eq_fun.const α c, mem_Lp_const α μ c⟩

section opens_measurable_space
variables [opens_measurable_space E]

lemma Lp_norm_eq_zero_iff {f : Lp α E p μ} (hp : 0 < p) : Lp_norm f = 0 ↔ f = 0 :=
begin
  refine ⟨λ hf, _, λ hf, by simp [hf]⟩,
  rw [Lp_norm, ennreal.to_real_eq_zero_iff] at hf,
  cases hf,
  { rw snorm_eq_zero_iff f.ae_measurable hp.ne.symm at hf,
    exact subtype.eq (ae_eq_fun.ext (hf.trans ae_eq_fun.coe_fn_zero.symm)), },
  { exact absurd hf f.prop.ne, },
end

end opens_measurable_space

section borel_space
variables [borel_space E]

instance : has_neg (Lp α E p μ) :=
{ neg := λ f,
    ⟨-f.val, by { rw [snorm_congr_ae (ae_eq_fun.coe_fn_neg _), snorm_neg], exact f.prop }⟩ }

@[simp] lemma coe_neg {f : Lp α E p μ} : (-f).val = -f.val := rfl

lemma coe_fn_neg {f : Lp α E p μ} : ⇑(-f) =ᵐ[μ] -f := ae_eq_fun.coe_fn_neg _

@[simp] lemma Lp_norm_neg {f : Lp α E p μ} : Lp_norm (-f) = Lp_norm f :=
by rw [Lp_norm, Lp_norm, snorm_congr_ae coe_fn_neg, snorm_neg]

section second_countable_topology
variable [topological_space.second_countable_topology E]

instance : has_add (Lp α E p μ) :=
{ add := λ f g, ⟨f.val + g.val,
  by { rw snorm_congr_ae (ae_eq_fun.coe_fn_add _ _), exact snorm_add_lt_top f.mem_ℒp g.mem_ℒp }⟩ }

@[simp] lemma coe_add {f g : Lp α E p μ} : (f + g).val = f.val + g.val := rfl

lemma coe_fn_add {f g : Lp α E p μ} : ⇑(f + g) =ᵐ[μ] f + g := ae_eq_fun.coe_fn_add _ _

instance : add_comm_group (Lp α E p μ) :=
{ add := (+),
  neg := has_neg.neg,
  zero := 0,
  add_assoc := λ _ _ _ , subtype.eq (add_assoc _ _ _),
  zero_add := λ _, subtype.eq (zero_add _),
  add_zero := λ _, subtype.eq (add_zero _),
  add_comm := λ _ _, subtype.eq (add_comm _ _),
  add_left_neg := λ _, subtype.eq (add_left_neg _), }

@[simp] lemma coe_sub {f g : Lp α E p μ} : (f - g).val = f.val - g.val := rfl

lemma coe_fn_sub {f g : Lp α E p μ} : ⇑(f - g) =ᵐ[μ] f - g := ae_eq_fun.coe_fn_sub _ _

instance : has_dist (Lp α E p μ) := { dist := λ f g, Lp_norm (f - g) }

private lemma dist_triangle' [hp : fact (1 ≤ p)] (f g h : Lp α E p μ) :
  dist f h ≤ dist f g + dist g h :=
begin
  simp only [dist, Lp_norm],
  rw ←ennreal.to_real_add (f - g).snorm_ne_top (g - h).snorm_ne_top,
  suffices h_snorm : snorm ⇑(f - h) p μ ≤ snorm ⇑(f - g) p μ + snorm ⇑(g - h) p μ,
  { rwa ennreal.to_real_le_to_real (f - h).snorm_ne_top,
    exact ennreal.add_ne_top.mpr ⟨(f - g).snorm_ne_top, (g - h).snorm_ne_top⟩, },
  have h_add : (f - h) = f - g + (g - h), by abel,
  rw [h_add, snorm_congr_ae coe_fn_add],
  exact snorm_add_le (f - g).ae_measurable (g - h).ae_measurable hp,
end

instance [hp : fact (1 ≤ p)] : metric_space (Lp α E p μ) :=
{ dist_self := λ _, by simp [dist, Lp_norm_zero],
  dist_comm := λ _ _, by { simp only [dist], rw [←Lp_norm_neg, neg_sub] },
  dist_triangle := dist_triangle',
  eq_of_dist_eq_zero := λ _ _ h, by simpa [dist,
    Lp_norm_eq_zero_iff (ennreal.zero_lt_one.trans_le hp), sub_eq_zero] using h, }

instance [fact (1 ≤ p)] : normed_group (Lp α E p μ) := { dist_eq := λ _ _, by simp [dist, norm] }

end second_countable_topology

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 E]

lemma mem_Lp_const_smul (c : 𝕜) (f : Lp α E p μ) : snorm (⇑(c • f.val)) p μ < ⊤ :=
begin
  rw [snorm_congr_ae (ae_eq_fun.coe_fn_smul _ _), snorm_const_smul, ennreal.mul_lt_top_iff],
  exact or.inl ⟨ennreal.coe_lt_top, f.prop⟩,
end

instance : has_scalar 𝕜 (Lp α E p μ) := { smul := λ c f, ⟨c • f.val, mem_Lp_const_smul c f⟩ }

@[simp] lemma coe_smul {f : Lp α E p μ} {c : 𝕜} : (c • f).val = c • f.val := rfl

lemma coe_fn_smul {f : Lp α E p μ} {c : 𝕜} : ⇑(c • f) =ᵐ[μ] c • f := ae_eq_fun.coe_fn_smul _ _

lemma Lp_norm_const_smul (c : 𝕜) (f : Lp α E p μ) : Lp_norm (c • f) = ∥c∥ * Lp_norm f :=
by simp [Lp_norm, snorm_congr_ae coe_fn_smul, snorm_const_smul c, ennreal.to_real_mul]

section normed_space_second_countable_topology
variable [topological_space.second_countable_topology E]

instance : mul_action 𝕜 (Lp α E p μ) :=
{ one_smul := λ _, subtype.eq (one_smul 𝕜 _),
  mul_smul := λ _ _ _, subtype.eq (mul_smul _ _ _) }

instance : distrib_mul_action 𝕜 (Lp α E p μ) :=
{ smul_add := λ _ _ _, subtype.eq (smul_add _ _ _),
  smul_zero := λ _, subtype.eq (smul_zero _) }

instance : semimodule 𝕜 (Lp α E p μ) :=
{ add_smul := λ _ _ _, subtype.eq (add_smul _ _ _),
  zero_smul := λ _, subtype.eq (zero_smul _ _) }

instance : vector_space 𝕜 (Lp α E p μ) := infer_instance

instance [fact (1 ≤ p)] : normed_space 𝕜 (Lp α E p μ) :=
{ norm_smul_le := λ _ _, by simp only [norm, Lp_norm_const_smul] }

end normed_space_second_countable_topology

end normed_space

end borel_space

end Lp

end Lp_space
