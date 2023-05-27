/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import analysis.normed_space.indicator_function
import analysis.special_functions.pow.continuity
import measure_theory.function.ess_sup
import measure_theory.function.ae_eq_fun
import measure_theory.integral.mean_inequalities

/-!
# ℒp space

This file describes properties of almost everywhere strongly measurable functions with finite
seminorm, denoted by `snorm f p μ` and defined for `p:ℝ≥0∞` as `0` if `p=0`,
`(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `0 < p < ∞` and `ess_sup ‖f‖ μ` for `p=∞`.

The Prop-valued `mem_ℒp f p μ` states that a function `f : α → E` has finite seminorm.

## Main definitions

* `snorm' f p μ` : `(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `f : α → F` and `p : ℝ`, where `α` is a  measurable
  space and `F` is a normed group.
* `snorm_ess_sup f μ` : seminorm in `ℒ∞`, equal to the essential supremum `ess_sup ‖f‖ μ`.
* `snorm f p μ` : for `p : ℝ≥0∞`, seminorm in `ℒp`, equal to `0` for `p=0`, to `snorm' f p μ`
  for `0 < p < ∞` and to `snorm_ess_sup f μ` for `p = ∞`.

* `mem_ℒp f p μ` : property that the function `f` is almost everywhere strongly measurable and has
  finite `p`-seminorm for the measure `μ` (`snorm f p μ < ∞`)

-/

noncomputable theory
open topological_space measure_theory filter
open_locale nnreal ennreal big_operators topology measure_theory

variables {α E F G : Type*} {m m0 : measurable_space α} {p : ℝ≥0∞} {q : ℝ} {μ ν : measure α}
  [normed_add_comm_group E] [normed_add_comm_group F] [normed_add_comm_group G]

namespace measure_theory

section ℒp

/-!
### ℒp seminorm

We define the ℒp seminorm, denoted by `snorm f p μ`. For real `p`, it is given by an integral
formula (for which we use the notation `snorm' f p μ`), and for `p = ∞` it is the essential
supremum (for which we use the notation `snorm_ess_sup f μ`).

We also define a predicate `mem_ℒp f p μ`, requesting that a function is almost everywhere
measurable and has finite `snorm f p μ`.

This paragraph is devoted to the basic properties of these definitions. It is constructed as
follows: for a given property, we prove it for `snorm'` and `snorm_ess_sup` when it makes sense,
deduce it for `snorm`, and translate it in terms of `mem_ℒp`.
-/

section ℒp_space_definition

/-- `(∫ ‖f a‖^q ∂μ) ^ (1/q)`, which is a seminorm on the space of measurable functions for which
this quantity is finite -/
def snorm' {m : measurable_space α} (f : α → F) (q : ℝ) (μ : measure α) : ℝ≥0∞ :=
(∫⁻ a, ‖f a‖₊^q ∂μ) ^ (1/q)

/-- seminorm for `ℒ∞`, equal to the essential supremum of `‖f‖`. -/
def snorm_ess_sup {m : measurable_space α} (f : α → F) (μ : measure α) :=
ess_sup (λ x, (‖f x‖₊ : ℝ≥0∞)) μ

/-- `ℒp` seminorm, equal to `0` for `p=0`, to `(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `0 < p < ∞` and to
`ess_sup ‖f‖ μ` for `p = ∞`. -/
def snorm {m : measurable_space α} (f : α → F) (p : ℝ≥0∞) (μ : measure α) : ℝ≥0∞ :=
if p = 0 then 0 else (if p = ∞ then snorm_ess_sup f μ else snorm' f (ennreal.to_real p) μ)

lemma snorm_eq_snorm' (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {f : α → F} :
  snorm f p μ = snorm' f (ennreal.to_real p) μ :=
by simp [snorm, hp_ne_zero, hp_ne_top]

lemma snorm_eq_lintegral_rpow_nnnorm (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {f : α → F} :
  snorm f p μ = (∫⁻ x, ‖f x‖₊ ^ p.to_real ∂μ) ^ (1 / p.to_real) :=
by rw [snorm_eq_snorm' hp_ne_zero hp_ne_top, snorm']

lemma snorm_one_eq_lintegral_nnnorm {f : α → F} : snorm f 1 μ = ∫⁻ x, ‖f x‖₊ ∂μ :=
by simp_rw [snorm_eq_lintegral_rpow_nnnorm one_ne_zero ennreal.coe_ne_top, ennreal.one_to_real,
  one_div_one, ennreal.rpow_one]

@[simp] lemma snorm_exponent_top {f : α → F} : snorm f ∞ μ = snorm_ess_sup f μ := by simp [snorm]

/-- The property that `f:α→E` is ae strongly measurable and `(∫ ‖f a‖^p ∂μ)^(1/p)` is finite
if `p < ∞`, or `ess_sup f < ∞` if `p = ∞`. -/
def mem_ℒp {α} {m : measurable_space α}
  (f : α → E) (p : ℝ≥0∞) (μ : measure α . volume_tac) : Prop :=
ae_strongly_measurable f μ ∧ snorm f p μ < ∞

lemma mem_ℒp.ae_strongly_measurable {f : α → E} {p : ℝ≥0∞} (h : mem_ℒp f p μ) :
  ae_strongly_measurable f μ := h.1

lemma lintegral_rpow_nnnorm_eq_rpow_snorm' {f : α → F} (hq0_lt : 0 < q) :
  ∫⁻ a, ‖f a‖₊ ^ q ∂μ = (snorm' f q μ) ^ q :=
begin
  rw [snorm', ←ennreal.rpow_mul, one_div, inv_mul_cancel, ennreal.rpow_one],
  exact (ne_of_lt hq0_lt).symm,
end

end ℒp_space_definition

section top

lemma mem_ℒp.snorm_lt_top {f : α → E} (hfp : mem_ℒp f p μ) : snorm f p μ < ∞ := hfp.2

lemma mem_ℒp.snorm_ne_top {f : α → E} (hfp : mem_ℒp f p μ) : snorm f p μ ≠ ∞ := ne_of_lt (hfp.2)

lemma lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top {f : α → F} (hq0_lt : 0 < q)
  (hfq : snorm' f q μ < ∞) :
  ∫⁻ a, ‖f a‖₊ ^ q ∂μ < ∞ :=
begin
  rw lintegral_rpow_nnnorm_eq_rpow_snorm' hq0_lt,
  exact ennreal.rpow_lt_top_of_nonneg (le_of_lt hq0_lt) (ne_of_lt hfq),
end

lemma lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top {f : α → F} (hp_ne_zero : p ≠ 0)
  (hp_ne_top : p ≠ ∞) (hfp : snorm f p μ < ∞) :
  ∫⁻ a, ‖f a‖₊ ^ p.to_real ∂μ < ∞ :=
begin
  apply lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top,
  { exact ennreal.to_real_pos hp_ne_zero hp_ne_top },
  { simpa [snorm_eq_snorm' hp_ne_zero hp_ne_top] using hfp }
end

lemma snorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top {f : α → F} (hp_ne_zero : p ≠ 0)
  (hp_ne_top : p ≠ ∞) :
  snorm f p μ < ∞ ↔ ∫⁻ a, ‖f a‖₊ ^ p.to_real ∂μ < ∞ :=
⟨lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top hp_ne_zero hp_ne_top,
  begin
    intros h,
    have hp' := ennreal.to_real_pos hp_ne_zero hp_ne_top,
    have : 0 < 1 / p.to_real := div_pos zero_lt_one hp',
    simpa [snorm_eq_lintegral_rpow_nnnorm hp_ne_zero hp_ne_top] using
      ennreal.rpow_lt_top_of_nonneg (le_of_lt this) (ne_of_lt h)
  end⟩

end top

section zero

@[simp] lemma snorm'_exponent_zero {f : α → F} : snorm' f 0 μ = 1 :=
by rw [snorm', div_zero, ennreal.rpow_zero]

@[simp] lemma snorm_exponent_zero {f : α → F} : snorm f 0 μ = 0 :=
by simp [snorm]

lemma mem_ℒp_zero_iff_ae_strongly_measurable {f : α → E} :
  mem_ℒp f 0 μ ↔ ae_strongly_measurable f μ :=
by simp [mem_ℒp, snorm_exponent_zero]

@[simp] lemma snorm'_zero (hp0_lt : 0 < q) : snorm' (0 : α → F) q μ = 0 :=
by simp [snorm', hp0_lt]

@[simp] lemma snorm'_zero' (hq0_ne : q ≠ 0) (hμ : μ ≠ 0) : snorm' (0 : α → F) q μ = 0 :=
begin
  cases le_or_lt 0 q with hq0 hq_neg,
  { exact snorm'_zero (lt_of_le_of_ne hq0 hq0_ne.symm), },
  { simp [snorm', ennreal.rpow_eq_zero_iff, hμ, hq_neg], },
end

@[simp] lemma snorm_ess_sup_zero : snorm_ess_sup (0 : α → F) μ = 0 :=
begin
  simp_rw [snorm_ess_sup, pi.zero_apply, nnnorm_zero, ennreal.coe_zero, ←ennreal.bot_eq_zero],
  exact ess_sup_const_bot,
end

@[simp] lemma snorm_zero : snorm (0 : α → F) p μ = 0 :=
begin
  by_cases h0 : p = 0,
  { simp [h0], },
  by_cases h_top : p = ∞,
  { simp only [h_top, snorm_exponent_top, snorm_ess_sup_zero], },
  rw ←ne.def at h0,
  simp [snorm_eq_snorm' h0 h_top, ennreal.to_real_pos h0 h_top],
end

@[simp] lemma snorm_zero' : snorm (λ x : α, (0 : F)) p μ = 0 :=
by convert snorm_zero

lemma zero_mem_ℒp : mem_ℒp (0 : α → E) p μ :=
⟨ae_strongly_measurable_zero, by { rw snorm_zero, exact ennreal.coe_lt_top, } ⟩

lemma zero_mem_ℒp' : mem_ℒp (λ x : α, (0 : E)) p μ :=
by convert zero_mem_ℒp

variables [measurable_space α]

lemma snorm'_measure_zero_of_pos {f : α → F} (hq_pos : 0 < q) :
  snorm' f q (0 : measure α) = 0 :=
by simp [snorm', hq_pos]

lemma snorm'_measure_zero_of_exponent_zero {f : α → F} : snorm' f 0 (0 : measure α) = 1 :=
by simp [snorm']

lemma snorm'_measure_zero_of_neg {f : α → F} (hq_neg : q < 0) : snorm' f q (0 : measure α) = ∞ :=
by simp [snorm', hq_neg]

@[simp] lemma snorm_ess_sup_measure_zero {f : α → F} : snorm_ess_sup f (0 : measure α) = 0 :=
by simp [snorm_ess_sup]

@[simp] lemma snorm_measure_zero {f : α → F} : snorm f p (0 : measure α) = 0 :=
begin
  by_cases h0 : p = 0,
  { simp [h0], },
  by_cases h_top : p = ∞,
  { simp [h_top], },
  rw ←ne.def at h0,
  simp [snorm_eq_snorm' h0 h_top, snorm', ennreal.to_real_pos h0 h_top],
end

end zero

section const

lemma snorm'_const (c : F) (hq_pos : 0 < q) :
  snorm' (λ x : α , c) q μ = (‖c‖₊ : ℝ≥0∞) * (μ set.univ) ^ (1/q) :=
begin
  rw [snorm', lintegral_const, ennreal.mul_rpow_of_nonneg _ _ (by simp [hq_pos.le] : 0 ≤ 1 / q)],
  congr,
  rw ←ennreal.rpow_mul,
  suffices hq_cancel : q * (1/q) = 1, by rw [hq_cancel, ennreal.rpow_one],
  rw [one_div, mul_inv_cancel (ne_of_lt hq_pos).symm],
end

lemma snorm'_const' [is_finite_measure μ] (c : F) (hc_ne_zero : c ≠ 0) (hq_ne_zero : q ≠ 0) :
  snorm' (λ x : α , c) q μ = (‖c‖₊ : ℝ≥0∞) * (μ set.univ) ^ (1/q) :=
begin
  rw [snorm', lintegral_const, ennreal.mul_rpow_of_ne_top _ (measure_ne_top μ set.univ)],
  { congr,
    rw ←ennreal.rpow_mul,
    suffices hp_cancel : q * (1/q) = 1, by rw [hp_cancel, ennreal.rpow_one],
    rw [one_div, mul_inv_cancel hq_ne_zero], },
  { rw [ne.def, ennreal.rpow_eq_top_iff, not_or_distrib, not_and_distrib, not_and_distrib],
    split,
    { left,
      rwa [ennreal.coe_eq_zero, nnnorm_eq_zero], },
    { exact or.inl ennreal.coe_ne_top, }, },
end

lemma snorm_ess_sup_const (c : F) (hμ : μ ≠ 0) :
  snorm_ess_sup (λ x : α, c) μ = (‖c‖₊ : ℝ≥0∞) :=
by rw [snorm_ess_sup, ess_sup_const _ hμ]

lemma snorm'_const_of_is_probability_measure (c : F) (hq_pos : 0 < q) [is_probability_measure μ] :
  snorm' (λ x : α , c) q μ = (‖c‖₊ : ℝ≥0∞) :=
by simp [snorm'_const c hq_pos, measure_univ]

lemma snorm_const (c : F) (h0 : p ≠ 0) (hμ : μ ≠ 0) :
  snorm (λ x : α , c) p μ = (‖c‖₊ : ℝ≥0∞) * (μ set.univ) ^ (1/(ennreal.to_real p)) :=
begin
  by_cases h_top : p = ∞,
  { simp [h_top, snorm_ess_sup_const c hμ], },
  simp [snorm_eq_snorm' h0 h_top, snorm'_const, ennreal.to_real_pos h0 h_top],
end

lemma snorm_const' (c : F) (h0 : p ≠ 0) (h_top: p ≠ ∞) :
  snorm (λ x : α , c) p μ = (‖c‖₊ : ℝ≥0∞) * (μ set.univ) ^ (1/(ennreal.to_real p)) :=
begin
  simp [snorm_eq_snorm' h0 h_top, snorm'_const, ennreal.to_real_pos h0 h_top],
end

lemma snorm_const_lt_top_iff {p : ℝ≥0∞} {c : F} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  snorm (λ x : α, c) p μ < ∞ ↔ c = 0 ∨ μ set.univ < ∞ :=
begin
  have hp : 0 < p.to_real, from ennreal.to_real_pos hp_ne_zero hp_ne_top,
  by_cases hμ : μ = 0,
  { simp only [hμ, measure.coe_zero, pi.zero_apply, or_true, with_top.zero_lt_top,
      snorm_measure_zero], },
  by_cases hc : c = 0,
  { simp only [hc, true_or, eq_self_iff_true, with_top.zero_lt_top, snorm_zero'], },
  rw snorm_const' c hp_ne_zero hp_ne_top,
  by_cases hμ_top : μ set.univ = ∞,
  { simp [hc, hμ_top, hp], },
  rw ennreal.mul_lt_top_iff,
  simp only [true_and, one_div, ennreal.rpow_eq_zero_iff, hμ, false_or, or_false,
    ennreal.coe_lt_top, nnnorm_eq_zero, ennreal.coe_eq_zero,
    measure_theory.measure.measure_univ_eq_zero, hp, inv_lt_zero, hc, and_false, false_and,
    _root_.inv_pos, or_self, hμ_top, ne.lt_top hμ_top, iff_true],
  exact ennreal.rpow_lt_top_of_nonneg (inv_nonneg.mpr hp.le) hμ_top,
end

lemma mem_ℒp_const (c : E) [is_finite_measure μ] : mem_ℒp (λ a:α, c) p μ :=
begin
  refine ⟨ae_strongly_measurable_const, _⟩,
  by_cases h0 : p = 0,
  { simp [h0], },
  by_cases hμ : μ = 0,
  { simp [hμ], },
  rw snorm_const c h0 hμ,
  refine ennreal.mul_lt_top ennreal.coe_ne_top _,
  refine (ennreal.rpow_lt_top_of_nonneg _ (measure_ne_top μ set.univ)).ne,
  simp,
end

lemma mem_ℒp_top_const (c : E) : mem_ℒp (λ a:α, c) ∞ μ :=
begin
  refine ⟨ae_strongly_measurable_const, _⟩,
  by_cases h : μ = 0,
  { simp only [h, snorm_measure_zero, with_top.zero_lt_top] },
  { rw snorm_const _ ennreal.top_ne_zero h,
    simp only [ennreal.top_to_real, div_zero, ennreal.rpow_zero, mul_one, ennreal.coe_lt_top] }
end

lemma mem_ℒp_const_iff {p : ℝ≥0∞} {c : E} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  mem_ℒp (λ x : α, c) p μ ↔ c = 0 ∨ μ set.univ < ∞ :=
begin
  rw ← snorm_const_lt_top_iff hp_ne_zero hp_ne_top,
  exact ⟨λ h, h.2, λ h, ⟨ae_strongly_measurable_const, h⟩⟩,
end

end const

lemma snorm'_mono_nnnorm_ae {f : α → F} {g : α → G} (hq : 0 ≤ q) (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
  snorm' f q μ ≤ snorm' g q μ :=
begin
  rw [snorm'],
  refine ennreal.rpow_le_rpow _ (one_div_nonneg.2 hq),
  refine lintegral_mono_ae (h.mono $ λ x hx, _),
  exact ennreal.rpow_le_rpow (ennreal.coe_le_coe.2 hx) hq
end

lemma snorm'_mono_ae {f : α → F} {g : α → G} (hq : 0 ≤ q) (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
  snorm' f q μ ≤ snorm' g q μ :=
snorm'_mono_nnnorm_ae hq h

lemma snorm'_congr_nnnorm_ae {f g : α → F} (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ = ‖g x‖₊) :
  snorm' f q μ = snorm' g q μ :=
begin
  have : (λ x, (‖f x‖₊ ^ q : ℝ≥0∞)) =ᵐ[μ] (λ x, ‖g x‖₊ ^ q),
    from hfg.mono (λ x hx, by simp_rw hx),
  simp only [snorm', lintegral_congr_ae this]
end

lemma snorm'_congr_norm_ae {f g : α → F} (hfg : ∀ᵐ x ∂μ, ‖f x‖ = ‖g x‖) :
  snorm' f q μ = snorm' g q μ :=
snorm'_congr_nnnorm_ae $ hfg.mono $ λ x hx, nnreal.eq hx

lemma snorm'_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) : snorm' f q μ = snorm' g q μ :=
snorm'_congr_nnnorm_ae (hfg.fun_comp _)

lemma snorm_ess_sup_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) :
  snorm_ess_sup f μ = snorm_ess_sup g μ :=
ess_sup_congr_ae (hfg.fun_comp (coe ∘ nnnorm))

lemma snorm_ess_sup_mono_nnnorm_ae {f g : α → F} (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
  snorm_ess_sup f μ ≤ snorm_ess_sup g μ :=
ess_sup_mono_ae $ hfg.mono $ λ x hx, ennreal.coe_le_coe.mpr hx

lemma snorm_mono_nnnorm_ae {f : α → F} {g : α → G} (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
  snorm f p μ ≤ snorm g p μ :=
begin
  simp only [snorm],
  split_ifs,
  { exact le_rfl },
  { exact ess_sup_mono_ae (h.mono $ λ x hx, ennreal.coe_le_coe.mpr hx) },
  { exact snorm'_mono_nnnorm_ae ennreal.to_real_nonneg h }
end

lemma snorm_mono_ae {f : α → F} {g : α → G} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
  snorm f p μ ≤ snorm g p μ :=
snorm_mono_nnnorm_ae h

lemma snorm_mono_ae_real {f : α → F} {g : α → ℝ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x) :
  snorm f p μ ≤ snorm g p μ :=
snorm_mono_ae $ h.mono (λ x hx, hx.trans ((le_abs_self _).trans (real.norm_eq_abs _).symm.le))

lemma snorm_mono_nnnorm {f : α → F} {g : α → G} (h : ∀ x, ‖f x‖₊ ≤ ‖g x‖₊) :
  snorm f p μ ≤ snorm g p μ :=
snorm_mono_nnnorm_ae (eventually_of_forall (λ x, h x))

lemma snorm_mono {f : α → F} {g : α → G} (h : ∀ x, ‖f x‖ ≤ ‖g x‖) :
  snorm f p μ ≤ snorm g p μ :=
snorm_mono_nnnorm h

lemma snorm_mono_real {f : α → F} {g : α → ℝ} (h : ∀ x, ‖f x‖ ≤ g x) :
  snorm f p μ ≤ snorm g p μ :=
snorm_mono_ae_real (eventually_of_forall (λ x, h x))

lemma snorm_ess_sup_le_of_ae_nnnorm_bound {f : α → F} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
  snorm_ess_sup f μ ≤ C :=
ess_sup_le_of_ae_le C $ hfC.mono $ λ x hx, ennreal.coe_le_coe.mpr hx

lemma snorm_ess_sup_le_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
  snorm_ess_sup f μ ≤ ennreal.of_real C :=
snorm_ess_sup_le_of_ae_nnnorm_bound $ hfC.mono $ λ x hx, hx.trans C.le_coe_to_nnreal

lemma snorm_ess_sup_lt_top_of_ae_nnnorm_bound {f : α → F} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
  snorm_ess_sup f μ < ∞ :=
(snorm_ess_sup_le_of_ae_nnnorm_bound hfC).trans_lt ennreal.coe_lt_top

lemma snorm_ess_sup_lt_top_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
  snorm_ess_sup f μ < ∞ :=
(snorm_ess_sup_le_of_ae_bound hfC).trans_lt ennreal.of_real_lt_top

lemma snorm_le_of_ae_nnnorm_bound {f : α → F} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
  snorm f p μ ≤ C • (μ set.univ ^ p.to_real⁻¹) :=
begin
  by_cases hμ : μ = 0,
  { simp [hμ] },
  haveI : μ.ae.ne_bot := ae_ne_bot.mpr hμ,
  by_cases hp : p = 0,
  { simp [hp] },
  have : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖(C : ℝ)‖₊ := hfC.mono (λ x hx, hx.trans_eq C.nnnorm_eq.symm),
  refine (snorm_mono_ae this).trans_eq _,
  rw [snorm_const _ hp hμ, C.nnnorm_eq, one_div, ennreal.smul_def, smul_eq_mul],
end

lemma snorm_le_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
  snorm f p μ ≤ ((μ set.univ) ^ p.to_real⁻¹) * (ennreal.of_real C) :=
begin
  rw [←mul_comm],
  exact snorm_le_of_ae_nnnorm_bound (hfC.mono $ λ x hx, hx.trans C.le_coe_to_nnreal),
end

lemma snorm_congr_nnnorm_ae {f : α → F} {g : α → G} (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ = ‖g x‖₊) :
  snorm f p μ = snorm g p μ :=
le_antisymm (snorm_mono_nnnorm_ae $ eventually_eq.le hfg)
  (snorm_mono_nnnorm_ae $ (eventually_eq.symm hfg).le)

lemma snorm_congr_norm_ae {f : α → F} {g : α → G} (hfg : ∀ᵐ x ∂μ, ‖f x‖ = ‖g x‖) :
  snorm f p μ = snorm g p μ :=
snorm_congr_nnnorm_ae $ hfg.mono $ λ x hx, nnreal.eq hx

@[simp] lemma snorm'_norm {f : α → F} : snorm' (λ a, ‖f a‖) q μ = snorm' f q μ :=
by simp [snorm']

@[simp] lemma snorm_norm (f : α → F) : snorm (λ x, ‖f x‖) p μ = snorm f p μ :=
snorm_congr_norm_ae $ eventually_of_forall $ λ x, norm_norm _

lemma snorm'_norm_rpow (f : α → F) (p q : ℝ) (hq_pos : 0 < q) :
  snorm' (λ x, ‖f x‖ ^ q) p μ = (snorm' f (p * q) μ) ^ q :=
begin
  simp_rw snorm',
  rw [← ennreal.rpow_mul, ←one_div_mul_one_div],
  simp_rw one_div,
  rw [mul_assoc, inv_mul_cancel hq_pos.ne.symm, mul_one],
  congr,
  ext1 x,
  simp_rw ← of_real_norm_eq_coe_nnnorm,
  rw [real.norm_eq_abs, abs_eq_self.mpr (real.rpow_nonneg_of_nonneg (norm_nonneg _) _),
    mul_comm, ← ennreal.of_real_rpow_of_nonneg (norm_nonneg _) hq_pos.le, ennreal.rpow_mul],
end

lemma snorm_norm_rpow (f : α → F) (hq_pos : 0 < q) :
  snorm (λ x, ‖f x‖ ^ q) p μ = (snorm f (p * ennreal.of_real q) μ) ^ q :=
begin
  by_cases h0 : p = 0,
  { simp [h0, ennreal.zero_rpow_of_pos hq_pos], },
  by_cases hp_top : p = ∞,
  { simp only [hp_top, snorm_exponent_top, ennreal.top_mul, hq_pos.not_le, ennreal.of_real_eq_zero,
      if_false, snorm_exponent_top, snorm_ess_sup],
    have h_rpow : ess_sup (λ (x : α), (‖(‖f x‖ ^ q)‖₊ : ℝ≥0∞)) μ
      = ess_sup (λ (x : α), (↑‖f x‖₊) ^ q) μ,
    { congr,
      ext1 x,
      nth_rewrite 1 ← nnnorm_norm,
      rw [ennreal.coe_rpow_of_nonneg _ hq_pos.le, ennreal.coe_eq_coe],
      ext,
      push_cast,
      rw real.norm_rpow_of_nonneg (norm_nonneg _), },
    rw h_rpow,
    have h_rpow_mono := ennreal.strict_mono_rpow_of_pos hq_pos,
    have h_rpow_surj := (ennreal.rpow_left_bijective hq_pos.ne.symm).2,
    let iso := h_rpow_mono.order_iso_of_surjective _ h_rpow_surj,
    exact (iso.ess_sup_apply (λ x, (‖f x‖₊ : ℝ≥0∞)) μ).symm, },
  rw [snorm_eq_snorm' h0 hp_top, snorm_eq_snorm' _ _],
  swap, { refine mul_ne_zero h0 _, rwa [ne.def, ennreal.of_real_eq_zero, not_le], },
  swap, { exact ennreal.mul_ne_top hp_top ennreal.of_real_ne_top, },
  rw [ennreal.to_real_mul, ennreal.to_real_of_real hq_pos.le],
  exact snorm'_norm_rpow f p.to_real q hq_pos,
end

lemma snorm_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) : snorm f p μ = snorm g p μ :=
snorm_congr_norm_ae $ hfg.mono (λ x hx, hx ▸ rfl)

lemma mem_ℒp_congr_ae {f g : α → E} (hfg : f =ᵐ[μ] g) : mem_ℒp f p μ ↔ mem_ℒp g p μ :=
by simp only [mem_ℒp, snorm_congr_ae hfg, ae_strongly_measurable_congr hfg]

lemma mem_ℒp.ae_eq {f g : α → E} (hfg : f =ᵐ[μ] g) (hf_Lp : mem_ℒp f p μ) : mem_ℒp g p μ :=
(mem_ℒp_congr_ae hfg).1 hf_Lp

lemma mem_ℒp.of_le {f : α → E} {g : α → F}
  (hg : mem_ℒp g p μ) (hf : ae_strongly_measurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
  mem_ℒp f p μ :=
⟨hf, (snorm_mono_ae hfg).trans_lt hg.snorm_lt_top⟩

alias mem_ℒp.of_le ← mem_ℒp.mono

lemma mem_ℒp.mono' {f : α → E} {g : α → ℝ} (hg : mem_ℒp g p μ)
  (hf : ae_strongly_measurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a) : mem_ℒp f p μ :=
hg.mono hf $ h.mono $ λ x hx, le_trans hx (le_abs_self _)

lemma mem_ℒp.congr_norm {f : α → E} {g : α → F} (hf : mem_ℒp f p μ)
  (hg : ae_strongly_measurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) :
  mem_ℒp g p μ :=
hf.mono hg $ eventually_eq.le $ eventually_eq.symm h

lemma mem_ℒp_congr_norm {f : α → E} {g : α → F}
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) :
  mem_ℒp f p μ ↔ mem_ℒp g p μ :=
⟨λ h2f, h2f.congr_norm hg h, λ h2g, h2g.congr_norm hf $ eventually_eq.symm h⟩

lemma mem_ℒp_top_of_bound {f : α → E} (hf : ae_strongly_measurable f μ) (C : ℝ)
  (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
  mem_ℒp f ∞ μ :=
⟨hf, by { rw snorm_exponent_top, exact snorm_ess_sup_lt_top_of_ae_bound hfC, }⟩

lemma mem_ℒp.of_bound [is_finite_measure μ] {f : α → E} (hf : ae_strongly_measurable f μ)
  (C : ℝ) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
  mem_ℒp f p μ :=
(mem_ℒp_const C).of_le hf (hfC.mono (λ x hx, le_trans hx (le_abs_self _)))

@[mono] lemma snorm'_mono_measure (f : α → F) (hμν : ν ≤ μ) (hq : 0 ≤ q) :
  snorm' f q ν ≤ snorm' f q μ :=
begin
  simp_rw snorm',
  suffices h_integral_mono : (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ q ∂ν) ≤ ∫⁻ a, ‖f a‖₊ ^ q ∂μ,
    from ennreal.rpow_le_rpow h_integral_mono (by simp [hq]),
  exact lintegral_mono' hμν le_rfl,
end

@[mono] lemma snorm_ess_sup_mono_measure (f : α → F) (hμν : ν ≪ μ) :
  snorm_ess_sup f ν ≤ snorm_ess_sup f μ :=
by { simp_rw snorm_ess_sup, exact ess_sup_mono_measure hμν, }

@[mono] lemma snorm_mono_measure (f : α → F) (hμν : ν ≤ μ) :
  snorm f p ν ≤ snorm f p μ :=
begin
  by_cases hp0 : p = 0,
  { simp [hp0], },
  by_cases hp_top : p = ∞,
  { simp [hp_top, snorm_ess_sup_mono_measure f (measure.absolutely_continuous_of_le hμν)], },
  simp_rw snorm_eq_snorm' hp0 hp_top,
  exact snorm'_mono_measure f hμν ennreal.to_real_nonneg,
end

lemma mem_ℒp.mono_measure {f : α → E} (hμν : ν ≤ μ) (hf : mem_ℒp f p μ) :
  mem_ℒp f p ν :=
⟨hf.1.mono_measure hμν, (snorm_mono_measure f hμν).trans_lt hf.2⟩

lemma mem_ℒp.restrict (s : set α) {f : α → E} (hf : mem_ℒp f p μ) :
  mem_ℒp f p (μ.restrict s) :=
hf.mono_measure measure.restrict_le_self

lemma snorm'_smul_measure {p : ℝ} (hp : 0 ≤ p) {f : α → F} (c : ℝ≥0∞) :
  snorm' f p (c • μ) = c ^ (1 / p) * snorm' f p μ :=
by { rw [snorm', lintegral_smul_measure, ennreal.mul_rpow_of_nonneg, snorm'], simp [hp], }

lemma snorm_ess_sup_smul_measure {f : α → F} {c : ℝ≥0∞} (hc : c ≠ 0) :
  snorm_ess_sup f (c • μ) = snorm_ess_sup f μ :=
by { simp_rw [snorm_ess_sup], exact ess_sup_smul_measure hc, }

/-- Use `snorm_smul_measure_of_ne_top` instead. -/
private lemma snorm_smul_measure_of_ne_zero_of_ne_top {p : ℝ≥0∞} (hp_ne_zero : p ≠ 0)
  (hp_ne_top : p ≠ ∞) {f : α → F} (c : ℝ≥0∞) :
  snorm f p (c • μ) = c ^ (1 / p).to_real • snorm f p μ :=
begin
  simp_rw snorm_eq_snorm' hp_ne_zero hp_ne_top,
  rw snorm'_smul_measure ennreal.to_real_nonneg,
  congr,
  simp_rw one_div,
  rw ennreal.to_real_inv,
end

lemma snorm_smul_measure_of_ne_zero {p : ℝ≥0∞} {f : α → F} {c : ℝ≥0∞} (hc : c ≠ 0) :
  snorm f p (c • μ) = c ^ (1 / p).to_real • snorm f p μ :=
begin
  by_cases hp0 : p = 0,
  { simp [hp0], },
  by_cases hp_top : p = ∞,
  { simp [hp_top, snorm_ess_sup_smul_measure hc], },
  exact snorm_smul_measure_of_ne_zero_of_ne_top hp0 hp_top c,
end

lemma snorm_smul_measure_of_ne_top {p : ℝ≥0∞} (hp_ne_top : p ≠ ∞) {f : α → F} (c : ℝ≥0∞) :
  snorm f p (c • μ) = c ^ (1 / p).to_real • snorm f p μ :=
begin
  by_cases hp0 : p = 0,
  { simp [hp0], },
  { exact snorm_smul_measure_of_ne_zero_of_ne_top hp0 hp_ne_top c, },
end

lemma snorm_one_smul_measure {f : α → F} (c : ℝ≥0∞) :
  snorm f 1 (c • μ) = c * snorm f 1 μ :=
by { rw @snorm_smul_measure_of_ne_top _ _ _ μ _ 1 (@ennreal.coe_ne_top 1) f c, simp, }

lemma mem_ℒp.of_measure_le_smul {μ' : measure α} (c : ℝ≥0∞) (hc : c ≠ ∞)
  (hμ'_le : μ' ≤ c • μ) {f : α → E} (hf : mem_ℒp f p μ) :
  mem_ℒp f p μ' :=
begin
  refine ⟨hf.1.mono' (measure.absolutely_continuous_of_le_smul hμ'_le), _⟩,
  refine (snorm_mono_measure f hμ'_le).trans_lt _,
  by_cases hc0 : c = 0,
  { simp [hc0], },
  rw [snorm_smul_measure_of_ne_zero hc0, smul_eq_mul],
  refine ennreal.mul_lt_top _ hf.2.ne,
  simp [hc, hc0],
end

lemma mem_ℒp.smul_measure {f : α → E} {c : ℝ≥0∞} (hf : mem_ℒp f p μ) (hc : c ≠ ∞) :
  mem_ℒp f p (c • μ) :=
hf.of_measure_le_smul c hc le_rfl

include m

lemma snorm_one_add_measure (f : α → F) (μ ν : measure α) :
  snorm f 1 (μ + ν) = snorm f 1 μ + snorm f 1 ν :=
by { simp_rw snorm_one_eq_lintegral_nnnorm, rw lintegral_add_measure _ μ ν, }

lemma snorm_le_add_measure_right (f : α → F) (μ ν : measure α) {p : ℝ≥0∞} :
  snorm f p μ ≤ snorm f p (μ + ν) :=
snorm_mono_measure f $ measure.le_add_right $ le_refl _

lemma snorm_le_add_measure_left (f : α → F) (μ ν : measure α) {p : ℝ≥0∞} :
  snorm f p ν ≤ snorm f p (μ + ν) :=
snorm_mono_measure f $ measure.le_add_left $ le_refl _

omit m

lemma mem_ℒp.left_of_add_measure {f : α → E} (h : mem_ℒp f p (μ + ν)) : mem_ℒp f p μ :=
h.mono_measure $ measure.le_add_right $ le_refl _

lemma mem_ℒp.right_of_add_measure {f : α → E} (h : mem_ℒp f p (μ + ν)) : mem_ℒp f p ν :=
h.mono_measure $ measure.le_add_left $ le_refl _

lemma mem_ℒp.norm {f : α → E} (h : mem_ℒp f p μ) : mem_ℒp (λ x, ‖f x‖) p μ :=
h.of_le h.ae_strongly_measurable.norm (eventually_of_forall (λ x, by simp))

lemma mem_ℒp_norm_iff {f : α → E} (hf : ae_strongly_measurable f μ) :
  mem_ℒp (λ x, ‖f x‖) p μ ↔ mem_ℒp f p μ :=
⟨λ h, ⟨hf, by { rw ← snorm_norm, exact h.2, }⟩, λ h, h.norm⟩

lemma snorm'_eq_zero_of_ae_zero {f : α → F} (hq0_lt : 0 < q) (hf_zero : f =ᵐ[μ] 0) :
  snorm' f q μ = 0 :=
by rw [snorm'_congr_ae hf_zero, snorm'_zero hq0_lt]

lemma snorm'_eq_zero_of_ae_zero' (hq0_ne : q ≠ 0) (hμ : μ ≠ 0) {f : α → F} (hf_zero : f =ᵐ[μ] 0) :
  snorm' f q μ = 0 :=
by rw [snorm'_congr_ae hf_zero, snorm'_zero' hq0_ne hμ]

lemma ae_eq_zero_of_snorm'_eq_zero {f : α → E} (hq0 : 0 ≤ q) (hf : ae_strongly_measurable f μ)
  (h : snorm' f q μ = 0) : f =ᵐ[μ] 0 :=
begin
  rw [snorm', ennreal.rpow_eq_zero_iff] at h,
  cases h,
  { rw lintegral_eq_zero_iff' (hf.ennnorm.pow_const q) at h,
    refine h.left.mono (λ x hx, _),
    rw [pi.zero_apply, ennreal.rpow_eq_zero_iff] at hx,
    cases hx,
    { cases hx with hx _,
      rwa [←ennreal.coe_zero, ennreal.coe_eq_coe, nnnorm_eq_zero] at hx, },
    { exact absurd hx.left ennreal.coe_ne_top, }, },
  { exfalso,
    rw [one_div, inv_lt_zero] at h,
    exact hq0.not_lt h.right },
end

lemma snorm'_eq_zero_iff (hq0_lt : 0 < q) {f : α → E} (hf : ae_strongly_measurable f μ) :
  snorm' f q μ = 0 ↔ f =ᵐ[μ] 0 :=
⟨ae_eq_zero_of_snorm'_eq_zero (le_of_lt hq0_lt) hf, snorm'_eq_zero_of_ae_zero hq0_lt⟩

lemma coe_nnnorm_ae_le_snorm_ess_sup {m : measurable_space α} (f : α → F) (μ : measure α) :
  ∀ᵐ x ∂μ, (‖f x‖₊ : ℝ≥0∞) ≤ snorm_ess_sup f μ :=
ennreal.ae_le_ess_sup (λ x, (‖f x‖₊ : ℝ≥0∞))

@[simp] lemma snorm_ess_sup_eq_zero_iff {f : α → F} : snorm_ess_sup f μ = 0 ↔ f =ᵐ[μ] 0 :=
by simp [eventually_eq, snorm_ess_sup]

lemma snorm_eq_zero_iff {f : α → E} (hf : ae_strongly_measurable f μ) (h0 : p ≠ 0) :
  snorm f p μ = 0 ↔ f =ᵐ[μ] 0 :=
begin
  by_cases h_top : p = ∞,
  { rw [h_top, snorm_exponent_top, snorm_ess_sup_eq_zero_iff], },
  rw snorm_eq_snorm' h0 h_top,
  exact snorm'_eq_zero_iff (ennreal.to_real_pos h0 h_top) hf,
end

lemma snorm'_add_le {f g : α → E}
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) (hq1 : 1 ≤ q) :
  snorm' (f + g) q μ ≤ snorm' f q μ + snorm' g q μ :=
calc (∫⁻ a, ↑‖(f + g) a‖₊ ^ q ∂μ) ^ (1 / q)
    ≤ (∫⁻ a, (((λ a, (‖f a‖₊ : ℝ≥0∞))
        + (λ a, (‖g a‖₊ : ℝ≥0∞))) a) ^ q ∂μ) ^ (1 / q) :
begin
  refine ennreal.rpow_le_rpow _ (by simp [le_trans zero_le_one hq1] : 0 ≤ 1 / q),
  refine lintegral_mono (λ a, ennreal.rpow_le_rpow _ (le_trans zero_le_one hq1)),
  simp [←ennreal.coe_add, nnnorm_add_le],
end
... ≤ snorm' f q μ + snorm' g q μ :
  ennreal.lintegral_Lp_add_le hf.ennnorm hg.ennnorm hq1

lemma snorm'_add_le_of_le_one {f g : α → E}
  (hf : ae_strongly_measurable f μ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
  snorm' (f + g) q μ ≤ 2^(1/q-1) * (snorm' f q μ + snorm' g q μ) :=
calc (∫⁻ a, ↑‖(f + g) a‖₊ ^ q ∂μ) ^ (1 / q)
    ≤ (∫⁻ a, (((λ a, (‖f a‖₊ : ℝ≥0∞))
        + (λ a, (‖g a‖₊ : ℝ≥0∞))) a) ^ q ∂μ) ^ (1 / q) :
begin
  refine ennreal.rpow_le_rpow _ (by simp [hq0] : 0 ≤ 1 / q),
  refine lintegral_mono (λ a, ennreal.rpow_le_rpow _ hq0),
  simp [←ennreal.coe_add, nnnorm_add_le],
end
... ≤ 2^(1/q-1) * (snorm' f q μ + snorm' g q μ) :
  ennreal.lintegral_Lp_add_le_of_le_one hf.ennnorm hq0 hq1

lemma snorm_ess_sup_add_le {f g : α → F} :
  snorm_ess_sup (f + g) μ ≤ snorm_ess_sup f μ + snorm_ess_sup g μ :=
begin
  refine le_trans (ess_sup_mono_ae (eventually_of_forall (λ x, _)))
    (ennreal.ess_sup_add_le _ _),
  simp_rw [pi.add_apply, ←ennreal.coe_add, ennreal.coe_le_coe],
  exact nnnorm_add_le _ _,
end

lemma snorm_add_le
  {f g : α → E} (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) (hp1 : 1 ≤ p) :
  snorm (f + g) p μ ≤ snorm f p μ + snorm g p μ :=
begin
  by_cases hp0 : p = 0,
  { simp [hp0], },
  by_cases hp_top : p = ∞,
  { simp [hp_top, snorm_ess_sup_add_le], },
  have hp1_real : 1 ≤ p.to_real,
  by rwa [← ennreal.one_to_real, ennreal.to_real_le_to_real ennreal.one_ne_top hp_top],
  repeat { rw snorm_eq_snorm' hp0 hp_top, },
  exact snorm'_add_le hf hg hp1_real,
end

/-- A constant for the inequality `‖f + g‖_{L^p} ≤ C * (‖f‖_{L^p} + ‖g‖_{L^p})`. It is equal to `1`
for `p ≥ 1` or `p = 0`, and `2^(1/p-1)` in the more tricky interval `(0, 1)`. -/
def Lp_add_const (p : ℝ≥0∞) : ℝ≥0∞ :=
if p ∈ set.Ioo (0 : ℝ≥0∞) 1 then 2^(1/p.to_real-1) else 1

lemma Lp_add_const_of_one_le {p : ℝ≥0∞} (hp : 1 ≤ p) : Lp_add_const p = 1 :=
begin
  rw [Lp_add_const, if_neg],
  assume h,
  exact lt_irrefl _ (h.2.trans_le hp),
end

lemma Lp_add_const_zero : Lp_add_const 0 = 1 :=
begin
  rw [Lp_add_const, if_neg],
  assume h,
  exact lt_irrefl _ (h.1),
end

lemma Lp_add_const_lt_top (p : ℝ≥0∞) : Lp_add_const p < ∞ :=
begin
  rw [Lp_add_const],
  split_ifs,
  { apply ennreal.rpow_lt_top_of_nonneg _ ennreal.two_ne_top,
    simp only [one_div, sub_nonneg],
    apply one_le_inv (ennreal.to_real_pos h.1.ne' (h.2.trans ennreal.one_lt_top).ne),
    simpa using ennreal.to_real_mono ennreal.one_ne_top h.2.le },
  { exact ennreal.one_lt_top }
end

lemma snorm_add_le'
  {f g : α → E} (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) (p : ℝ≥0∞) :
  snorm (f + g) p μ ≤ Lp_add_const p * (snorm f p μ + snorm g p μ) :=
begin
  rcases eq_or_ne p 0 with rfl|hp,
  { simp only [snorm_exponent_zero, add_zero, mul_zero, le_zero_iff] },
  rcases lt_or_le p 1 with h'p|h'p,
  { simp only [snorm_eq_snorm' hp (h'p.trans ennreal.one_lt_top).ne],
    convert snorm'_add_le_of_le_one hf ennreal.to_real_nonneg _,
    { have : p ∈ set.Ioo (0 : ℝ≥0∞) 1 := ⟨hp.bot_lt, h'p⟩,
      simp only [Lp_add_const, if_pos this] },
    { simpa using ennreal.to_real_mono ennreal.one_ne_top h'p.le } },
  { simp [Lp_add_const_of_one_le h'p],
    exact snorm_add_le hf hg h'p }
end

variables (μ E)
/-- Technical lemma to control the addition of functions in `L^p` even for `p < 1`: Given `δ > 0`,
there exists `η` such that two functions bounded by `η` in `L^p` have a sum bounded by `δ`. One
could take `η = δ / 2` for `p ≥ 1`, but the point of the lemma is that it works also for `p < 1`.
-/
lemma exists_Lp_half (p : ℝ≥0∞) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
  ∃ (η : ℝ≥0∞), 0 < η ∧ ∀ (f g : α → E) (hf : ae_strongly_measurable f μ)
    (hg : ae_strongly_measurable g μ) (Hf : snorm f p μ ≤ η) (Hg : snorm g p μ ≤ η),
      snorm (f + g) p μ < δ :=
begin
  have : tendsto (λ (η : ℝ≥0∞), Lp_add_const p * (η + η)) (𝓝[>] 0) (𝓝 (Lp_add_const p * (0 + 0))),
    from (ennreal.tendsto.const_mul (tendsto_id.add tendsto_id)
      (or.inr (Lp_add_const_lt_top p).ne)).mono_left nhds_within_le_nhds,
  simp only [add_zero, mul_zero] at this,
  rcases (((tendsto_order.1 this).2 δ hδ.bot_lt).and self_mem_nhds_within).exists
    with ⟨η, hη, ηpos⟩,
  refine ⟨η, ηpos, λ f g hf hg Hf Hg, _⟩,
  calc snorm (f + g) p μ ≤ Lp_add_const p * (snorm f p μ + snorm g p μ) : snorm_add_le' hf hg p
  ... ≤ Lp_add_const p * (η + η) : mul_le_mul_of_nonneg_left (add_le_add Hf Hg) bot_le
  ... < δ : hη
end
variables {μ E}

lemma snorm_sub_le'
  {f g : α → E} (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) (p : ℝ≥0∞) :
  snorm (f - g) p μ ≤ Lp_add_const p * (snorm f p μ + snorm g p μ) :=
calc snorm (f - g) p μ = snorm (f + - g) p μ : by rw sub_eq_add_neg
  -- We cannot use snorm_add_le on f and (-g) because we don't have `ae_measurable (-g) μ`, since
  -- we don't suppose `[borel_space E]`.
... = snorm (λ x, ‖f x + - g x‖) p μ : (snorm_norm (f + - g)).symm
... ≤ snorm (λ x, ‖f x‖ + ‖- g x‖) p μ : by
{ refine snorm_mono_real (λ x, _), rw norm_norm, exact norm_add_le _ _, }
... = snorm (λ x, ‖f x‖ + ‖g x‖) p μ : by simp_rw norm_neg
... ≤ Lp_add_const p * (snorm (λ x, ‖f x‖) p μ + snorm (λ x, ‖g x‖) p μ) :
  snorm_add_le' hf.norm hg.norm p
... = Lp_add_const p * (snorm f p μ + snorm g p μ) : by rw [← snorm_norm f, ← snorm_norm g]

lemma snorm_sub_le
  {f g : α → E} (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) (hp : 1 ≤ p) :
  snorm (f - g) p μ ≤ snorm f p μ + snorm g p μ :=
by simpa [Lp_add_const_of_one_le hp] using snorm_sub_le' hf hg p

lemma snorm_add_lt_top {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  snorm (f + g) p μ < ∞ := calc
snorm (f + g) p μ ≤ Lp_add_const p * (snorm f p μ + snorm g p μ) :
  snorm_add_le' hf.ae_strongly_measurable hg.ae_strongly_measurable p
... < ∞ :
begin
  apply ennreal.mul_lt_top (Lp_add_const_lt_top p).ne,
  exact ((ennreal.add_lt_top).2 ⟨hf.2, hg.2⟩).ne,
end

lemma ae_le_snorm_ess_sup {f : α → F} : ∀ᵐ y ∂μ, ↑‖f y‖₊ ≤ snorm_ess_sup f μ := ae_le_ess_sup

lemma meas_snorm_ess_sup_lt {f : α → F} : μ {y | snorm_ess_sup f μ < ‖f y‖₊} = 0 :=
meas_ess_sup_lt

section map_measure

variables {β : Type*} {mβ : measurable_space β} {f : α → β} {g : β → E}

include mβ

lemma snorm_ess_sup_map_measure
  (hg : ae_strongly_measurable g (measure.map f μ)) (hf : ae_measurable f μ) :
  snorm_ess_sup g (measure.map f μ) = snorm_ess_sup (g ∘ f) μ :=
ess_sup_map_measure hg.ennnorm hf

lemma snorm_map_measure (hg : ae_strongly_measurable g (measure.map f μ)) (hf : ae_measurable f μ) :
  snorm g p (measure.map f μ) = snorm (g ∘ f) p μ :=
begin
  by_cases hp_zero : p = 0,
  { simp only [hp_zero, snorm_exponent_zero], },
  by_cases hp_top : p = ∞,
  { simp_rw [hp_top, snorm_exponent_top],
    exact snorm_ess_sup_map_measure hg hf, },
  simp_rw snorm_eq_lintegral_rpow_nnnorm hp_zero hp_top,
  rw lintegral_map' (hg.ennnorm.pow_const p.to_real) hf,
end

lemma mem_ℒp_map_measure_iff
  (hg : ae_strongly_measurable g (measure.map f μ)) (hf : ae_measurable f μ) :
  mem_ℒp g p (measure.map f μ) ↔ mem_ℒp (g ∘ f) p μ :=
by simp [mem_ℒp, snorm_map_measure hg hf, hg.comp_ae_measurable hf, hg]

lemma _root_.measurable_embedding.snorm_ess_sup_map_measure {g : β → F}
  (hf : measurable_embedding f) :
  snorm_ess_sup g (measure.map f μ) = snorm_ess_sup (g ∘ f) μ :=
hf.ess_sup_map_measure

lemma _root_.measurable_embedding.snorm_map_measure {g : β → F} (hf : measurable_embedding f) :
  snorm g p (measure.map f μ) = snorm (g ∘ f) p μ :=
begin
  by_cases hp_zero : p = 0,
  { simp only [hp_zero, snorm_exponent_zero], },
  by_cases hp : p = ∞,
  { simp_rw [hp, snorm_exponent_top],
    exact hf.ess_sup_map_measure, },
  { simp_rw snorm_eq_lintegral_rpow_nnnorm hp_zero hp,
    rw hf.lintegral_map, },
end

lemma _root_.measurable_embedding.mem_ℒp_map_measure_iff {g : β → F}
  (hf : measurable_embedding f) :
  mem_ℒp g p (measure.map f μ) ↔ mem_ℒp (g ∘ f) p μ :=
by simp_rw [mem_ℒp, hf.ae_strongly_measurable_map_iff, hf.snorm_map_measure]

lemma _root_.measurable_equiv.mem_ℒp_map_measure_iff (f : α ≃ᵐ β) {g : β → F} :
  mem_ℒp g p (measure.map f μ) ↔ mem_ℒp (g ∘ f) p μ :=
f.measurable_embedding.mem_ℒp_map_measure_iff

omit mβ

end map_measure

section trim

lemma snorm'_trim (hm : m ≤ m0) {f : α → E} (hf : strongly_measurable[m] f) :
  snorm' f q (ν.trim hm) = snorm' f q ν :=
begin
  simp_rw snorm',
  congr' 1,
  refine lintegral_trim hm _,
  refine @measurable.pow_const _ _ _ _ _ _ _ m _ (@measurable.coe_nnreal_ennreal _ m _ _) _,
  apply @strongly_measurable.measurable,
  exact (@strongly_measurable.nnnorm α m _ _ _ hf),
end

lemma limsup_trim (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : measurable[m] f) :
  (ν.trim hm).ae.limsup f = ν.ae.limsup f :=
begin
  simp_rw limsup_eq,
  suffices h_set_eq : {a : ℝ≥0∞ | ∀ᵐ n ∂(ν.trim hm), f n ≤ a} = {a : ℝ≥0∞ | ∀ᵐ n ∂ν, f n ≤ a},
    by rw h_set_eq,
  ext1 a,
  suffices h_meas_eq : ν {x | ¬ f x ≤ a} = ν.trim hm {x | ¬ f x ≤ a},
    by simp_rw [set.mem_set_of_eq, ae_iff, h_meas_eq],
  refine (trim_measurable_set_eq hm _).symm,
  refine @measurable_set.compl _ _ m (@measurable_set_le ℝ≥0∞ _ _ _ _ m _ _ _ _ _ hf _),
  exact @measurable_const _ _ _ m _,
end

lemma ess_sup_trim (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : measurable[m] f) :
  ess_sup f (ν.trim hm) = ess_sup f ν :=
by { simp_rw ess_sup, exact limsup_trim hm hf, }

lemma snorm_ess_sup_trim (hm : m ≤ m0) {f : α → E} (hf : strongly_measurable[m] f) :
  snorm_ess_sup f (ν.trim hm) = snorm_ess_sup f ν :=
ess_sup_trim _ (@strongly_measurable.ennnorm _ m _ _ _ hf)

lemma snorm_trim (hm : m ≤ m0) {f : α → E} (hf : strongly_measurable[m] f) :
  snorm f p (ν.trim hm) = snorm f p ν :=
begin
  by_cases h0 : p = 0,
  { simp [h0], },
  by_cases h_top : p = ∞,
  { simpa only [h_top, snorm_exponent_top] using snorm_ess_sup_trim hm hf, },
  simpa only [snorm_eq_snorm' h0 h_top] using snorm'_trim hm hf,
end

lemma snorm_trim_ae (hm : m ≤ m0) {f : α → E} (hf : ae_strongly_measurable f (ν.trim hm)) :
  snorm f p (ν.trim hm) = snorm f p ν :=
begin
  rw [snorm_congr_ae hf.ae_eq_mk, snorm_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk)],
  exact snorm_trim hm hf.strongly_measurable_mk,
end

lemma mem_ℒp_of_mem_ℒp_trim (hm : m ≤ m0) {f : α → E} (hf : mem_ℒp f p (ν.trim hm)) :
  mem_ℒp f p ν :=
⟨ae_strongly_measurable_of_ae_strongly_measurable_trim hm hf.1,
(le_of_eq (snorm_trim_ae hm hf.1).symm).trans_lt hf.2⟩

end trim

@[simp] lemma snorm'_neg {f : α → F} : snorm' (-f) q μ = snorm' f q μ := by simp [snorm']

@[simp] lemma snorm_neg {f : α → F} : snorm (-f) p μ = snorm f p μ :=
begin
  by_cases h0 : p = 0,
  { simp [h0], },
  by_cases h_top : p = ∞,
  { simp [h_top, snorm_ess_sup], },
  simp [snorm_eq_snorm' h0 h_top],
end

lemma mem_ℒp.neg {f : α → E} (hf : mem_ℒp f p μ) : mem_ℒp (-f) p μ :=
⟨ae_strongly_measurable.neg hf.1, by simp [hf.right]⟩

lemma mem_ℒp_neg_iff {f : α → E} : mem_ℒp (-f) p μ ↔ mem_ℒp f p μ :=
⟨λ h, neg_neg f ▸ h.neg, mem_ℒp.neg⟩

lemma snorm'_le_snorm'_mul_rpow_measure_univ {p q : ℝ} (hp0_lt : 0 < p) (hpq : p ≤ q)
  {f : α → E} (hf : ae_strongly_measurable f μ) :
  snorm' f p μ ≤ snorm' f q μ * (μ set.univ) ^ (1/p - 1/q) :=
begin
  have hq0_lt : 0 < q, from lt_of_lt_of_le hp0_lt hpq,
  by_cases hpq_eq : p = q,
  { rw [hpq_eq, sub_self, ennreal.rpow_zero, mul_one],
    exact le_rfl, },
  have hpq : p < q, from lt_of_le_of_ne hpq hpq_eq,
  let g := λ a : α, (1 : ℝ≥0∞),
  have h_rw : ∫⁻ a, ↑‖f a‖₊^p ∂ μ = ∫⁻ a, (‖f a‖₊ * (g a))^p ∂ μ,
  from lintegral_congr (λ a, by simp),
  repeat {rw snorm'},
  rw h_rw,
  let r := p * q / (q - p),
  have hpqr : 1/p = 1/q + 1/r,
  { field_simp [(ne_of_lt hp0_lt).symm,
      (ne_of_lt hq0_lt).symm],
    ring, },
  calc (∫⁻ (a : α), (↑‖f a‖₊ * g a) ^ p ∂μ) ^ (1/p)
      ≤ (∫⁻ (a : α), ↑‖f a‖₊ ^ q ∂μ) ^ (1/q) * (∫⁻ (a : α), (g a) ^ r ∂μ) ^ (1/r) :
    ennreal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hf.ennnorm ae_measurable_const
  ... = (∫⁻ (a : α), ↑‖f a‖₊ ^ q ∂μ) ^ (1/q) * μ set.univ ^ (1/p - 1/q) :
    by simp [hpqr],
end

lemma snorm'_le_snorm_ess_sup_mul_rpow_measure_univ (hq_pos : 0 < q) {f : α → F} :
  snorm' f q μ ≤ snorm_ess_sup f μ * (μ set.univ) ^ (1/q) :=
begin
  have h_le : ∫⁻ (a : α), ↑‖f a‖₊ ^ q ∂μ ≤ ∫⁻ (a : α), (snorm_ess_sup f μ) ^ q ∂μ,
  { refine lintegral_mono_ae _,
    have h_nnnorm_le_snorm_ess_sup := coe_nnnorm_ae_le_snorm_ess_sup f μ,
    refine h_nnnorm_le_snorm_ess_sup.mono (λ x hx, ennreal.rpow_le_rpow hx (le_of_lt hq_pos)), },
  rw [snorm', ←ennreal.rpow_one (snorm_ess_sup f μ)],
  nth_rewrite 1 ←mul_inv_cancel (ne_of_lt hq_pos).symm,
  rw [ennreal.rpow_mul, one_div,
    ←ennreal.mul_rpow_of_nonneg _ _ (by simp [hq_pos.le] : 0 ≤ q⁻¹)],
  refine ennreal.rpow_le_rpow _ (by simp [hq_pos.le]),
  rwa lintegral_const at h_le,
end

lemma snorm_le_snorm_mul_rpow_measure_univ {p q : ℝ≥0∞} (hpq : p ≤ q) {f : α → E}
  (hf : ae_strongly_measurable f μ) :
  snorm f p μ ≤ snorm f q μ * (μ set.univ) ^ (1/p.to_real - 1/q.to_real) :=
begin
  by_cases hp0 : p = 0,
  { simp [hp0, zero_le], },
  rw ← ne.def at hp0,
  have hp0_lt : 0 < p, from lt_of_le_of_ne (zero_le _) hp0.symm,
  have hq0_lt : 0 < q, from lt_of_lt_of_le hp0_lt hpq,
  by_cases hq_top : q = ∞,
  { simp only [hq_top, div_zero, one_div, ennreal.top_to_real, sub_zero, snorm_exponent_top,
      inv_zero],
    by_cases hp_top : p = ∞,
    { simp only [hp_top, ennreal.rpow_zero, mul_one, ennreal.top_to_real, sub_zero, inv_zero,
        snorm_exponent_top],
      exact le_rfl, },
    rw snorm_eq_snorm' hp0 hp_top,
    have hp_pos : 0 < p.to_real, from ennreal.to_real_pos hp0_lt.ne' hp_top,
    refine (snorm'_le_snorm_ess_sup_mul_rpow_measure_univ hp_pos).trans (le_of_eq _),
    congr,
    exact one_div _, },
  have hp_lt_top : p < ∞, from hpq.trans_lt (lt_top_iff_ne_top.mpr hq_top),
  have hp_pos : 0 < p.to_real, from ennreal.to_real_pos hp0_lt.ne' hp_lt_top.ne,
  rw [snorm_eq_snorm' hp0_lt.ne.symm hp_lt_top.ne, snorm_eq_snorm' hq0_lt.ne.symm hq_top],
  have hpq_real : p.to_real ≤ q.to_real, by rwa ennreal.to_real_le_to_real hp_lt_top.ne hq_top,
  exact snorm'_le_snorm'_mul_rpow_measure_univ hp_pos hpq_real hf,
end

lemma snorm'_le_snorm'_of_exponent_le {m : measurable_space α} {p q : ℝ} (hp0_lt : 0 < p)
  (hpq : p ≤ q) (μ : measure α) [is_probability_measure μ] {f : α → E}
  (hf : ae_strongly_measurable f μ) :
  snorm' f p μ ≤ snorm' f q μ :=
begin
  have h_le_μ := snorm'_le_snorm'_mul_rpow_measure_univ hp0_lt hpq hf,
  rwa [measure_univ, ennreal.one_rpow, mul_one] at h_le_μ,
end

lemma snorm'_le_snorm_ess_sup (hq_pos : 0 < q) {f : α → F} [is_probability_measure μ] :
  snorm' f q μ ≤ snorm_ess_sup f μ :=
le_trans (snorm'_le_snorm_ess_sup_mul_rpow_measure_univ hq_pos) (le_of_eq (by simp [measure_univ]))

lemma snorm_le_snorm_of_exponent_le {p q : ℝ≥0∞} (hpq : p ≤ q) [is_probability_measure μ]
  {f : α → E} (hf : ae_strongly_measurable f μ) :
  snorm f p μ ≤ snorm f q μ :=
(snorm_le_snorm_mul_rpow_measure_univ hpq hf).trans (le_of_eq (by simp [measure_univ]))

lemma snorm'_lt_top_of_snorm'_lt_top_of_exponent_le {p q : ℝ} [is_finite_measure μ] {f : α → E}
  (hf : ae_strongly_measurable f μ) (hfq_lt_top : snorm' f q μ < ∞)
  (hp_nonneg : 0 ≤ p) (hpq : p ≤ q) :
  snorm' f p μ < ∞ :=
begin
  cases le_or_lt p 0 with hp_nonpos hp_pos,
  { rw le_antisymm hp_nonpos hp_nonneg,
    simp, },
  have hq_pos : 0 < q, from lt_of_lt_of_le hp_pos hpq,
  calc snorm' f p μ
      ≤ snorm' f q μ * (μ set.univ) ^ (1/p - 1/q) :
    snorm'_le_snorm'_mul_rpow_measure_univ hp_pos hpq hf
  ... < ∞ :
  begin
    rw ennreal.mul_lt_top_iff,
    refine or.inl ⟨hfq_lt_top, ennreal.rpow_lt_top_of_nonneg _ (measure_ne_top μ set.univ)⟩,
    rwa [le_sub_comm, sub_zero, one_div, one_div, inv_le_inv hq_pos hp_pos],
  end
end

variables (μ)

lemma pow_mul_meas_ge_le_snorm {f : α → E}
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (hf : ae_strongly_measurable f μ) (ε : ℝ≥0∞) :
  (ε * μ {x | ε ≤ ‖f x‖₊ ^ p.to_real}) ^ (1 / p.to_real) ≤ snorm f p μ :=
begin
  rw snorm_eq_lintegral_rpow_nnnorm hp_ne_zero hp_ne_top,
  exact ennreal.rpow_le_rpow (mul_meas_ge_le_lintegral₀ (hf.ennnorm.pow_const _) ε)
    (one_div_nonneg.2 ennreal.to_real_nonneg),
end

lemma mul_meas_ge_le_pow_snorm {f : α → E}
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (hf : ae_strongly_measurable f μ) (ε : ℝ≥0∞) :
  ε * μ {x | ε ≤ ‖f x‖₊ ^ p.to_real} ≤ snorm f p μ ^ p.to_real :=
begin
  have : 1 / p.to_real * p.to_real = 1,
  { refine one_div_mul_cancel _,
    rw [ne, ennreal.to_real_eq_zero_iff],
    exact not_or hp_ne_zero hp_ne_top },
  rw [← ennreal.rpow_one (ε * μ {x | ε ≤ ‖f x‖₊ ^ p.to_real}), ← this, ennreal.rpow_mul],
  exact ennreal.rpow_le_rpow (pow_mul_meas_ge_le_snorm μ hp_ne_zero hp_ne_top hf ε)
    ennreal.to_real_nonneg,
end

/-- A version of Markov's inequality using Lp-norms. -/
lemma mul_meas_ge_le_pow_snorm' {f : α → E}
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (hf : ae_strongly_measurable f μ) (ε : ℝ≥0∞) :
  ε ^ p.to_real * μ {x | ε ≤ ‖f x‖₊} ≤ snorm f p μ ^ p.to_real :=
begin
  convert mul_meas_ge_le_pow_snorm μ hp_ne_zero hp_ne_top hf (ε ^ p.to_real),
  ext x,
  rw ennreal.rpow_le_rpow_iff (ennreal.to_real_pos hp_ne_zero hp_ne_top),
end

lemma meas_ge_le_mul_pow_snorm {f : α → E} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf : ae_strongly_measurable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  μ {x | ε ≤ ‖f x‖₊} ≤ ε⁻¹ ^ p.to_real * snorm f p μ ^ p.to_real :=
begin
  by_cases ε = ∞,
  { simp [h] },
  have hεpow : ε ^ p.to_real ≠ 0 := (ennreal.rpow_pos (pos_iff_ne_zero.2 hε) h).ne.symm,
  have hεpow' : ε ^ p.to_real ≠ ∞ := (ennreal.rpow_ne_top_of_nonneg ennreal.to_real_nonneg h),
  rw [ennreal.inv_rpow, ← ennreal.mul_le_mul_left hεpow hεpow', ← mul_assoc,
      ennreal.mul_inv_cancel hεpow hεpow', one_mul],
  exact mul_meas_ge_le_pow_snorm' μ hp_ne_zero hp_ne_top hf ε,
end

variables {μ}

lemma mem_ℒp.mem_ℒp_of_exponent_le {p q : ℝ≥0∞} [is_finite_measure μ] {f : α → E}
  (hfq : mem_ℒp f q μ) (hpq : p ≤ q) :
  mem_ℒp f p μ :=
begin
  cases hfq with hfq_m hfq_lt_top,
  by_cases hp0 : p = 0,
  { rwa [hp0, mem_ℒp_zero_iff_ae_strongly_measurable], },
  rw ←ne.def at hp0,
  refine ⟨hfq_m, _⟩,
  by_cases hp_top : p = ∞,
  { have hq_top : q = ∞,
      by rwa [hp_top, top_le_iff] at hpq,
    rw [hp_top],
    rwa hq_top at hfq_lt_top, },
  have hp_pos : 0 < p.to_real, from ennreal.to_real_pos hp0 hp_top,
  by_cases hq_top : q = ∞,
  { rw snorm_eq_snorm' hp0 hp_top,
    rw [hq_top, snorm_exponent_top] at hfq_lt_top,
    refine lt_of_le_of_lt (snorm'_le_snorm_ess_sup_mul_rpow_measure_univ hp_pos) _,
    refine ennreal.mul_lt_top hfq_lt_top.ne _,
    exact (ennreal.rpow_lt_top_of_nonneg (by simp [hp_pos.le]) (measure_ne_top μ set.univ)).ne },
  have hq0 : q ≠ 0,
  { by_contra hq_eq_zero,
    have hp_eq_zero : p = 0, from le_antisymm (by rwa hq_eq_zero at hpq) (zero_le _),
    rw [hp_eq_zero, ennreal.zero_to_real] at hp_pos,
    exact (lt_irrefl _) hp_pos, },
  have hpq_real : p.to_real ≤ q.to_real, by rwa ennreal.to_real_le_to_real hp_top hq_top,
  rw snorm_eq_snorm' hp0 hp_top,
  rw snorm_eq_snorm' hq0 hq_top at hfq_lt_top,
  exact snorm'_lt_top_of_snorm'_lt_top_of_exponent_le hfq_m hfq_lt_top (le_of_lt hp_pos) hpq_real,
end

section has_measurable_add
-- variable [has_measurable_add₂ E]

lemma snorm'_sum_le {ι} {f : ι → α → E} {s : finset ι}
  (hfs : ∀ i, i ∈ s → ae_strongly_measurable (f i) μ) (hq1 : 1 ≤ q) :
  snorm' (∑ i in s, f i) q μ ≤ ∑ i in s, snorm' (f i) q μ :=
finset.le_sum_of_subadditive_on_pred (λ (f : α → E), snorm' f q μ)
  (λ f, ae_strongly_measurable f μ) (snorm'_zero (zero_lt_one.trans_le hq1))
  (λ f g hf hg, snorm'_add_le hf hg hq1) (λ f g hf hg, hf.add hg) _ hfs

lemma snorm_sum_le {ι} {f : ι → α → E} {s : finset ι}
  (hfs : ∀ i, i ∈ s → ae_strongly_measurable (f i) μ) (hp1 : 1 ≤ p) :
  snorm (∑ i in s, f i) p μ ≤ ∑ i in s, snorm (f i) p μ :=
finset.le_sum_of_subadditive_on_pred (λ (f : α → E), snorm f p μ)
  (λ f, ae_strongly_measurable f μ) snorm_zero (λ f g hf hg, snorm_add_le hf hg hp1)
  (λ f g hf hg, hf.add hg) _ hfs

lemma mem_ℒp.add {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) : mem_ℒp (f + g) p μ :=
⟨ae_strongly_measurable.add hf.1 hg.1, snorm_add_lt_top hf hg⟩

lemma mem_ℒp.sub {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) : mem_ℒp (f - g) p μ :=
by { rw sub_eq_add_neg, exact hf.add hg.neg }

lemma mem_ℒp_finset_sum {ι} (s : finset ι) {f : ι → α → E} (hf : ∀ i ∈ s, mem_ℒp (f i) p μ) :
  mem_ℒp (λ a, ∑ i in s, f i a) p μ :=
begin
  haveI : decidable_eq ι := classical.dec_eq _,
  revert hf,
  refine finset.induction_on s _ _,
  { simp only [zero_mem_ℒp', finset.sum_empty, implies_true_iff], },
  { intros i s his ih hf,
    simp only [his, finset.sum_insert, not_false_iff],
    exact (hf i (s.mem_insert_self i)).add (ih (λ j hj, hf j (finset.mem_insert_of_mem hj))), },
end

lemma mem_ℒp_finset_sum' {ι} (s : finset ι) {f : ι → α → E} (hf : ∀ i ∈ s, mem_ℒp (f i) p μ) :
  mem_ℒp (∑ i in s, f i) p μ :=
begin
  convert mem_ℒp_finset_sum s hf,
  ext x,
  simp,
end

end has_measurable_add

section monotonicity

lemma snorm'_le_nnreal_smul_snorm'_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ≥0}
  (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) {p : ℝ} (hp : 0 < p) :
  snorm' f p μ ≤ c • snorm' g p μ :=
begin
  simp_rw [snorm'],
  rw [←ennreal.rpow_le_rpow_iff hp, ennreal.smul_def, smul_eq_mul,
    ennreal.mul_rpow_of_nonneg _ _ hp.le],
  simp_rw [←ennreal.rpow_mul, one_div, inv_mul_cancel hp.ne.symm, ennreal.rpow_one,
    ennreal.coe_rpow_of_nonneg _ hp.le, ←lintegral_const_mul' _ _ ennreal.coe_ne_top,
    ←ennreal.coe_mul],
  apply lintegral_mono_ae,
  simp_rw [ennreal.coe_le_coe, ←nnreal.mul_rpow, nnreal.rpow_le_rpow_iff hp],
  exact h,
end

lemma snorm_ess_sup_le_nnreal_smul_snorm_ess_sup_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ≥0}
  (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) :
  snorm_ess_sup f μ ≤ c • snorm_ess_sup g μ :=
calc  ess_sup (λ x, (‖f x‖₊: ℝ≥0∞)) μ
    ≤ ess_sup (λ x, (↑(c * ‖g x‖₊) : ℝ≥0∞)) μ
          : ess_sup_mono_ae $ h.mono $ λ x hx, ennreal.coe_le_coe.mpr hx
... = ess_sup (λ x, (c * ‖g x‖₊ : ℝ≥0∞)) μ : by simp_rw ennreal.coe_mul
... = c • ess_sup (λ x, (‖g x‖₊ : ℝ≥0∞)) μ : ennreal.ess_sup_const_mul

lemma snorm_le_nnreal_smul_snorm_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ≥0}
  (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) (p : ℝ≥0∞) :
  snorm f p μ ≤ c • snorm g p μ :=
begin
  by_cases h0 : p = 0,
  { simp [h0], },
  by_cases h_top : p = ∞,
  { rw h_top,
    exact snorm_ess_sup_le_nnreal_smul_snorm_ess_sup_of_ae_le_mul h, },
  simp_rw snorm_eq_snorm' h0 h_top,
  exact snorm'_le_nnreal_smul_snorm'_of_ae_le_mul h (ennreal.to_real_pos h0 h_top),
end

-- TODO: add the whole family of lemmas?
private lemma le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg {α} [linear_ordered_semiring α]
  {a b c : α} (ha : 0 ≤ a) (hb : b < 0) (hc : 0 ≤ c) : a ≤ b * c ↔ a = 0 ∧ c = 0 :=
begin
  split,
  { intro h,
    exact ⟨(h.trans (mul_nonpos_of_nonpos_of_nonneg hb.le hc)).antisymm ha,
      (nonpos_of_mul_nonneg_right (ha.trans h) hb).antisymm hc⟩ },
  { rintro ⟨rfl, rfl⟩,
    rw mul_zero, }
end

/-- When `c` is negative, `‖f x‖ ≤ c * ‖g x‖` is nonsense and forces both `f` and `g` to have an
`snorm` of `0`. -/
lemma snorm_eq_zero_and_zero_of_ae_le_mul_neg {f : α → F} {g : α → G} {c : ℝ}
  (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) (hc : c < 0) (p : ℝ≥0∞) :
  snorm f p μ = 0 ∧ snorm g p μ = 0 :=
begin
  simp_rw [le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg (norm_nonneg _) hc (norm_nonneg _),
    norm_eq_zero, eventually_and] at h,
  change f =ᵐ[μ] 0 ∧ g =ᵐ[μ] 0 at h,
  simp [snorm_congr_ae h.1, snorm_congr_ae h.2],
end

lemma snorm_le_mul_snorm_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ}
  (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) (p : ℝ≥0∞) :
  snorm f p μ ≤ (ennreal.of_real c) * snorm g p μ :=
snorm_le_nnreal_smul_snorm_of_ae_le_mul
  (h.mono $ λ x hx, hx.trans $ mul_le_mul_of_nonneg_right c.le_coe_to_nnreal (norm_nonneg _)) _

lemma mem_ℒp.of_nnnorm_le_mul {f : α → E} {g : α → F} {c : ℝ≥0}
  (hg : mem_ℒp g p μ) (hf : ae_strongly_measurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) :
  mem_ℒp f p μ :=
⟨hf, (snorm_le_nnreal_smul_snorm_of_ae_le_mul hfg p).trans_lt $
  ennreal.mul_lt_top ennreal.coe_ne_top hg.snorm_ne_top⟩

lemma mem_ℒp.of_le_mul {f : α → E} {g : α → F} {c : ℝ}
  (hg : mem_ℒp g p μ) (hf : ae_strongly_measurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) :
  mem_ℒp f p μ :=
⟨hf, (snorm_le_mul_snorm_of_ae_le_mul hfg p).trans_lt $
  ennreal.mul_lt_top ennreal.of_real_ne_top hg.snorm_ne_top⟩

lemma snorm'_le_snorm'_mul_snorm' {p q r : ℝ}
  {f : α → E} (hf : ae_strongly_measurable f μ) {g : α → F} (hg : ae_strongly_measurable g μ)
  (b : E → F → G) (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ ‖f x‖₊ * ‖g x‖₊)
  (hp0_lt : 0 < p) (hpq : p < q) (hpqr : 1/p = 1/q + 1/r) :
  snorm' (λ x, b (f x) (g x)) p μ ≤ snorm' f q μ * snorm' g r μ :=
begin
  rw snorm',
  calc (∫⁻ (a : α), ↑‖b (f a) (g a)‖₊ ^ p ∂μ) ^ (1 / p)
        ≤ (∫⁻ (a : α), ↑(‖f a‖₊ * ‖g a‖₊) ^ p ∂μ) ^ (1 / p) :
          (ennreal.rpow_le_rpow_iff $ one_div_pos.mpr (hp0_lt)).mpr $
            lintegral_mono_ae $ h.mono $ λ a ha, (ennreal.rpow_le_rpow_iff (hp0_lt)).mpr $
              ennreal.coe_le_coe.mpr $ ha
    ... ≤ _ : _,
  simp_rw [snorm', ennreal.coe_mul],
  exact ennreal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hf.ennnorm
    hg.ennnorm,
end

lemma snorm_le_snorm_top_mul_snorm (p : ℝ≥0∞)
  (f : α → E) {g : α → F} (hg : ae_strongly_measurable g μ) (b : E → F → G)
  (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ ‖f x‖₊ * ‖g x‖₊) :
  snorm (λ x, b (f x) (g x)) p μ ≤ snorm f ∞ μ * snorm g p μ :=
begin
  by_cases hp_top : p = ∞,
  { simp_rw [hp_top, snorm_exponent_top],
    refine le_trans (ess_sup_mono_ae $ h.mono $ λ a ha, _) (ennreal.ess_sup_mul_le _ _),
    simp_rw [pi.mul_apply, ←ennreal.coe_mul, ennreal.coe_le_coe],
    exact ha },
  by_cases hp_zero : p = 0,
  { simp only [hp_zero, snorm_exponent_zero, mul_zero, le_zero_iff], },
  simp_rw [snorm_eq_lintegral_rpow_nnnorm hp_zero hp_top, snorm_exponent_top, snorm_ess_sup],
  calc (∫⁻ x, ↑‖b (f x) (g x)‖₊ ^ p.to_real ∂μ) ^ (1 / p.to_real)
      ≤ (∫⁻ x, ↑‖f x‖₊ ^ p.to_real * ↑‖g x‖₊ ^ p.to_real ∂μ) ^ (1 / p.to_real) :
    begin
      refine ennreal.rpow_le_rpow _ (one_div_nonneg.mpr ennreal.to_real_nonneg),
      refine lintegral_mono_ae (h.mono $ λ a ha, _),
      rw ←ennreal.mul_rpow_of_nonneg _ _ ennreal.to_real_nonneg,
      refine ennreal.rpow_le_rpow _ ennreal.to_real_nonneg,
      rw [←ennreal.coe_mul, ennreal.coe_le_coe],
      exact ha,
    end
  ... ≤ (∫⁻ x, (ess_sup (λ x, ↑‖f x‖₊) μ) ^ p.to_real * ↑‖g x‖₊ ^ p.to_real ∂μ) ^ (1 / p.to_real) :
    begin
      refine ennreal.rpow_le_rpow _ _,
      swap, { rw one_div_nonneg, exact ennreal.to_real_nonneg, },
      refine lintegral_mono_ae _,
      filter_upwards [@ennreal.ae_le_ess_sup _ _ μ (λ x, ↑‖f x‖₊)] with x hx,
      exact mul_le_mul_right' (ennreal.rpow_le_rpow hx ennreal.to_real_nonneg) _
    end
  ... = ess_sup (λ x, ↑‖f x‖₊) μ * (∫⁻ x, ↑‖g x‖₊ ^ p.to_real ∂μ) ^ (1 / p.to_real) :
    begin
      rw lintegral_const_mul'',
      swap, { exact hg.nnnorm.ae_measurable.coe_nnreal_ennreal.pow ae_measurable_const, },
      rw ennreal.mul_rpow_of_nonneg,
      swap, { rw one_div_nonneg, exact ennreal.to_real_nonneg, },
      rw [← ennreal.rpow_mul, one_div, mul_inv_cancel, ennreal.rpow_one],
      rw [ne.def, ennreal.to_real_eq_zero_iff, auto.not_or_eq],
      exact ⟨hp_zero, hp_top⟩,
    end
end

lemma snorm_le_snorm_mul_snorm_top (p : ℝ≥0∞)
  {f : α → E} (hf : ae_strongly_measurable f μ) (g : α → F) (b : E → F → G)
  (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ ‖f x‖₊ * ‖g x‖₊) :
  snorm (λ x, b (f x) (g x)) p μ ≤ snorm f p μ * snorm g ∞ μ :=
begin
  rw [← snorm_norm f, ← snorm_norm g],
  refine (snorm_mono_ae_real h).trans _,
  simp_rw [mul_comm ‖f _‖₊, nnreal.coe_mul, coe_nnnorm],
  rw mul_comm,
  refine snorm_le_snorm_top_mul_snorm p (λ x, ‖g x‖) hf.norm _ (h.mono $ λ x hx, _),
  simp_rw [nnnorm_mul],
end

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise operation
`λ x, b (f x) (g x)`. -/
lemma snorm_le_snorm_mul_snorm_of_nnnorm {p q r : ℝ≥0∞}
  {f : α → E} (hf : ae_strongly_measurable f μ) {g : α → F} (hg : ae_strongly_measurable g μ)
  (b : E → F → G) (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ ‖f x‖₊ * ‖g x‖₊)
  (hpqr : 1/p = 1/q + 1/r) :
  snorm (λ x, b (f x) (g x)) p μ ≤ snorm f q μ * snorm g r μ :=
begin
  by_cases hp_zero : p = 0,
  { simp [hp_zero], },
  have hq_ne_zero : q ≠ 0,
  { intro hq_zero,
    simp only [hq_zero, hp_zero, one_div, ennreal.inv_zero, top_add,
      ennreal.inv_eq_top] at hpqr,
    exact hpqr, },
  have hr_ne_zero : r ≠ 0,
  { intro hr_zero,
    simp only [hr_zero, hp_zero, one_div, ennreal.inv_zero, add_top,
      ennreal.inv_eq_top] at hpqr,
    exact hpqr, },
  by_cases hq_top : q = ∞,
  { have hpr : p = r,
    { simpa only [hq_top, one_div, ennreal.div_top, zero_add, inv_inj] using hpqr, },
    rw [← hpr, hq_top],
    exact snorm_le_snorm_top_mul_snorm p f hg b h, },
  by_cases hr_top : r = ∞,
  { have hpq : p = q,
    { simpa only [hr_top, one_div, ennreal.div_top, add_zero, inv_inj] using hpqr, },
    rw [← hpq, hr_top],
    exact snorm_le_snorm_mul_snorm_top p hf g b h, },
  have hpq : p < q,
  { suffices : 1 / q < 1 / p,
    { rwa [one_div, one_div, ennreal.inv_lt_inv] at this, },
    rw hpqr,
    refine ennreal.lt_add_right _ _,
    { simp only [hq_ne_zero, one_div, ne.def, ennreal.inv_eq_top, not_false_iff], },
    { simp only [hr_top, one_div, ne.def, ennreal.inv_eq_zero, not_false_iff], }, },
  rw [snorm_eq_snorm' hp_zero (hpq.trans_le le_top).ne, snorm_eq_snorm' hq_ne_zero hq_top,
    snorm_eq_snorm' hr_ne_zero hr_top],
  refine snorm'_le_snorm'_mul_snorm' hf hg _ h _ _ _,
  { exact ennreal.to_real_pos hp_zero (hpq.trans_le le_top).ne, },
  { exact ennreal.to_real_strict_mono hq_top hpq, },
  rw [← ennreal.one_to_real, ← ennreal.to_real_div, ← ennreal.to_real_div, ← ennreal.to_real_div,
    hpqr, ennreal.to_real_add],
  { simp only [hq_ne_zero, one_div, ne.def, ennreal.inv_eq_top, not_false_iff], },
  { simp only [hr_ne_zero, one_div, ne.def, ennreal.inv_eq_top, not_false_iff], },
end

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise operation
`λ x, b (f x) (g x)`. -/
lemma snorm_le_snorm_mul_snorm'_of_norm {p q r : ℝ≥0∞}
  {f : α → E} (hf : ae_strongly_measurable f μ) {g : α → F} (hg : ae_strongly_measurable g μ)
  (b : E → F → G) (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖ ≤ ‖f x‖ * ‖g x‖)
  (hpqr : 1/p = 1/q + 1/r) :
  snorm (λ x, b (f x) (g x)) p μ ≤ snorm f q μ * snorm g r μ :=
snorm_le_snorm_mul_snorm_of_nnnorm hf hg b h hpqr

end monotonicity

/-!
### Bounded actions by normed rings

In this section we show inequalities on the norm.
-/
section has_bounded_smul

variables {𝕜 : Type*} [normed_ring 𝕜] [mul_action_with_zero 𝕜 E] [mul_action_with_zero 𝕜 F]
variables [has_bounded_smul 𝕜 E] [has_bounded_smul 𝕜 F]

lemma snorm'_const_smul_le (c : 𝕜) (f : α → F) (hq_pos : 0 < q) :
  snorm' (c • f) q μ ≤ ‖c‖₊ • snorm' f q μ :=
snorm'_le_nnreal_smul_snorm'_of_ae_le_mul (eventually_of_forall $ λ a, nnnorm_smul_le _ _) hq_pos

lemma snorm_ess_sup_const_smul_le (c : 𝕜) (f : α → F) :
  snorm_ess_sup (c • f) μ ≤ ‖c‖₊ • snorm_ess_sup f μ :=
snorm_ess_sup_le_nnreal_smul_snorm_ess_sup_of_ae_le_mul
  (eventually_of_forall $ λ a, nnnorm_smul_le _ _)

lemma snorm_const_smul_le (c : 𝕜) (f : α → F) :
  snorm (c • f) p μ ≤ ‖c‖₊ • snorm f p μ :=
snorm_le_nnreal_smul_snorm_of_ae_le_mul (eventually_of_forall $ λ a, nnnorm_smul_le _ _) _

lemma mem_ℒp.const_smul {f : α → E} (hf : mem_ℒp f p μ) (c : 𝕜) :
  mem_ℒp (c • f) p μ :=
⟨ae_strongly_measurable.const_smul hf.1 c,
  (snorm_const_smul_le c f).trans_lt (ennreal.mul_lt_top ennreal.coe_ne_top hf.2.ne)⟩

lemma mem_ℒp.const_mul {R} [normed_ring R] {f : α → R} (hf : mem_ℒp f p μ) (c : R) :
  mem_ℒp (λ x, c * f x) p μ :=
hf.const_smul c

lemma snorm'_smul_le_mul_snorm' {p q r : ℝ}
  {f : α → E} (hf : ae_strongly_measurable f μ) {φ : α → 𝕜} (hφ : ae_strongly_measurable φ μ)
  (hp0_lt : 0 < p) (hpq : p < q) (hpqr : 1/p = 1/q + 1/r) :
  snorm' (φ • f) p μ ≤ snorm' φ q μ * snorm' f r μ :=
snorm'_le_snorm'_mul_snorm' hφ hf (•)
  (eventually_of_forall $ λ a, nnnorm_smul_le _ _) hp0_lt hpq hpqr

lemma snorm_smul_le_snorm_top_mul_snorm (p : ℝ≥0∞)
  {f : α → E} (hf : ae_strongly_measurable f μ) (φ : α → 𝕜) :
  snorm (φ • f) p μ ≤ snorm φ ∞ μ * snorm f p μ :=
(snorm_le_snorm_top_mul_snorm p φ hf (•) (eventually_of_forall $ λ a, nnnorm_smul_le _ _) : _)

lemma snorm_smul_le_snorm_mul_snorm_top (p : ℝ≥0∞)
  (f : α → E) {φ : α → 𝕜} (hφ : ae_strongly_measurable φ μ) :
  snorm (φ • f) p μ ≤ snorm φ p μ * snorm f ∞ μ :=
(snorm_le_snorm_mul_snorm_top p hφ f (•) (eventually_of_forall $ λ a, nnnorm_smul_le _ _) : _)

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of a scalar product `φ • f`. -/
lemma snorm_smul_le_mul_snorm {p q r : ℝ≥0∞}
  {f : α → E} (hf : ae_strongly_measurable f μ) {φ : α → 𝕜} (hφ : ae_strongly_measurable φ μ)
  (hpqr : 1/p = 1/q + 1/r) :
  snorm (φ • f) p μ ≤ snorm φ q μ * snorm f r μ :=
(snorm_le_snorm_mul_snorm_of_nnnorm hφ hf (•)
  (eventually_of_forall $ λ a, nnnorm_smul_le _ _) hpqr : _)

lemma mem_ℒp.smul {p q r : ℝ≥0∞} {f : α → E} {φ : α → 𝕜}
  (hf : mem_ℒp f r μ) (hφ : mem_ℒp φ q μ) (hpqr : 1/p = 1/q + 1/r) :
  mem_ℒp (φ • f) p μ :=
⟨hφ.1.smul hf.1, (snorm_smul_le_mul_snorm hf.1 hφ.1 hpqr).trans_lt
  (ennreal.mul_lt_top hφ.snorm_ne_top hf.snorm_ne_top)⟩

lemma mem_ℒp.smul_of_top_right {p : ℝ≥0∞} {f : α → E} {φ : α → 𝕜}
  (hf : mem_ℒp f p μ) (hφ : mem_ℒp φ ∞ μ) :
  mem_ℒp (φ • f) p μ :=
by { apply hf.smul hφ, simp only [ennreal.div_top, zero_add] }

lemma mem_ℒp.smul_of_top_left {p : ℝ≥0∞} {f : α → E} {φ : α → 𝕜}
  (hf : mem_ℒp f ∞ μ) (hφ : mem_ℒp φ p μ) :
  mem_ℒp (φ • f) p μ :=
by { apply hf.smul hφ, simp only [ennreal.div_top, add_zero] }

end has_bounded_smul

/-!
### Bounded actions by normed division rings

The inequalities in the previous section are now tight.
-/
section normed_space

variables {𝕜 : Type*} [normed_division_ring 𝕜] [mul_action_with_zero 𝕜 E] [module 𝕜 F]
variables [has_bounded_smul 𝕜 E] [has_bounded_smul 𝕜 F]

lemma snorm'_const_smul {f : α → F} (c : 𝕜) (hq_pos : 0 < q) :
  snorm' (c • f) q μ = ‖c‖₊ • snorm' f q μ :=
begin
  obtain rfl | hc := eq_or_ne c 0,
  { simp [snorm', hq_pos], },
  refine le_antisymm (snorm'_const_smul_le _ _ hq_pos) _,
  have : snorm' _ q μ ≤ _:= snorm'_const_smul_le (c⁻¹) (c • f) hq_pos,
  rwa [inv_smul_smul₀ hc, nnnorm_inv, ennreal.le_inv_smul_iff (nnnorm_ne_zero_iff.mpr hc)] at this,
end

lemma snorm_ess_sup_const_smul (c : 𝕜) (f : α → F) :
  snorm_ess_sup (c • f) μ = (‖c‖₊ : ℝ≥0∞) * snorm_ess_sup f μ :=
by simp_rw [snorm_ess_sup,  pi.smul_apply, nnnorm_smul, ennreal.coe_mul, ennreal.ess_sup_const_mul]

lemma snorm_const_smul (c : 𝕜) (f : α → F) :
  snorm (c • f) p μ = (‖c‖₊ : ℝ≥0∞) * snorm f p μ :=
begin
  obtain rfl | hc := eq_or_ne c 0,
  { simp, },
  refine le_antisymm (snorm_const_smul_le _ _) _,
  have : snorm _ p μ ≤ _:= snorm_const_smul_le (c⁻¹) (c • f),
  rwa [inv_smul_smul₀ hc, nnnorm_inv, ennreal.le_inv_smul_iff (nnnorm_ne_zero_iff.mpr hc)] at this,
end

end normed_space

lemma snorm_indicator_ge_of_bdd_below (hp : p ≠ 0) (hp' : p ≠ ∞)
  {f : α → F} (C : ℝ≥0) {s : set α} (hs : measurable_set s)
  (hf : ∀ᵐ x ∂μ, x ∈ s → C ≤ ‖s.indicator f x‖₊) :
  C • μ s ^ (1 / p.to_real) ≤ snorm (s.indicator f) p μ :=
begin
  rw [ennreal.smul_def, smul_eq_mul, snorm_eq_lintegral_rpow_nnnorm hp hp',
    ennreal.le_rpow_one_div_iff (ennreal.to_real_pos hp hp'),
    ennreal.mul_rpow_of_nonneg _ _ ennreal.to_real_nonneg,
    ← ennreal.rpow_mul, one_div_mul_cancel (ennreal.to_real_pos hp hp').ne.symm, ennreal.rpow_one,
    ← set_lintegral_const, ← lintegral_indicator _ hs],
  refine lintegral_mono_ae _,
  filter_upwards [hf] with x hx,
  rw nnnorm_indicator_eq_indicator_nnnorm,
  by_cases hxs : x ∈ s,
  { simp only [set.indicator_of_mem hxs] at ⊢ hx,
    exact ennreal.rpow_le_rpow (ennreal.coe_le_coe.2 (hx hxs)) ennreal.to_real_nonneg },
  { simp [set.indicator_of_not_mem hxs] },
end

section is_R_or_C
variables {𝕜 : Type*} [is_R_or_C 𝕜] {f : α → 𝕜}

lemma mem_ℒp.re (hf : mem_ℒp f p μ) : mem_ℒp (λ x, is_R_or_C.re (f x)) p μ :=
begin
  have : ∀ x, ‖is_R_or_C.re (f x)‖ ≤ 1 * ‖f x‖,
    by { intro x, rw one_mul, exact is_R_or_C.norm_re_le_norm (f x), },
  refine hf.of_le_mul _ (eventually_of_forall this),
  exact is_R_or_C.continuous_re.comp_ae_strongly_measurable hf.1,
end

lemma mem_ℒp.im (hf : mem_ℒp f p μ) : mem_ℒp (λ x, is_R_or_C.im (f x)) p μ :=
begin
  have : ∀ x, ‖is_R_or_C.im (f x)‖ ≤ 1 * ‖f x‖,
    by { intro x, rw one_mul, exact is_R_or_C.norm_im_le_norm (f x), },
  refine hf.of_le_mul _ (eventually_of_forall this),
  exact is_R_or_C.continuous_im.comp_ae_strongly_measurable hf.1,
end

end is_R_or_C

section liminf

variables [measurable_space E] [opens_measurable_space E] {R : ℝ≥0}

lemma ae_bdd_liminf_at_top_rpow_of_snorm_bdd {p : ℝ≥0∞}
  {f : ℕ → α → E} (hfmeas : ∀ n, measurable (f n)) (hbdd : ∀ n, snorm (f n) p μ ≤ R) :
  ∀ᵐ x ∂μ, liminf (λ n, (‖f n x‖₊ ^ p.to_real : ℝ≥0∞)) at_top < ∞ :=
begin
  by_cases hp0 : p.to_real = 0,
  { simp only [hp0, ennreal.rpow_zero],
    refine eventually_of_forall (λ x, _),
    rw liminf_const (1 : ℝ≥0∞),
    exacts [ennreal.one_lt_top, at_top_ne_bot] },
  have hp : p ≠ 0 := λ h, by simpa [h] using hp0,
  have hp' : p ≠ ∞ := λ h, by simpa [h] using hp0,
  refine ae_lt_top
    (measurable_liminf (λ n, (hfmeas n).nnnorm.coe_nnreal_ennreal.pow_const p.to_real))
    (lt_of_le_of_lt (lintegral_liminf_le
      (λ n, (hfmeas n).nnnorm.coe_nnreal_ennreal.pow_const p.to_real))
      (lt_of_le_of_lt _ (ennreal.rpow_lt_top_of_nonneg
        ennreal.to_real_nonneg ennreal.coe_ne_top : ↑R ^ p.to_real < ∞))).ne,
  simp_rw snorm_eq_lintegral_rpow_nnnorm hp hp' at hbdd,
  simp_rw [liminf_eq, eventually_at_top],
  exact Sup_le (λ b ⟨a, ha⟩, (ha a le_rfl).trans
    ((ennreal.rpow_one_div_le_iff (ennreal.to_real_pos hp hp')).1 (hbdd _))),
end

lemma ae_bdd_liminf_at_top_of_snorm_bdd {p : ℝ≥0∞} (hp : p ≠ 0)
  {f : ℕ → α → E} (hfmeas : ∀ n, measurable (f n)) (hbdd : ∀ n, snorm (f n) p μ ≤ R) :
  ∀ᵐ x ∂μ, liminf (λ n, (‖f n x‖₊ : ℝ≥0∞)) at_top < ∞ :=
begin
  by_cases hp' : p = ∞,
  { subst hp',
    simp_rw snorm_exponent_top at hbdd,
    have : ∀ n, ∀ᵐ x ∂μ, (‖f n x‖₊ : ℝ≥0∞) < R + 1 :=
      λ n, ae_lt_of_ess_sup_lt (lt_of_le_of_lt (hbdd n) $
        ennreal.lt_add_right ennreal.coe_ne_top one_ne_zero),
    rw ← ae_all_iff at this,
    filter_upwards [this] with x hx using lt_of_le_of_lt
      (liminf_le_of_frequently_le' $ frequently_of_forall $ λ n, (hx n).le)
      (ennreal.add_lt_top.2 ⟨ennreal.coe_lt_top, ennreal.one_lt_top⟩) },
  filter_upwards [ae_bdd_liminf_at_top_rpow_of_snorm_bdd hfmeas hbdd] with x hx,
  have hppos : 0 < p.to_real := ennreal.to_real_pos hp hp',
  have : liminf (λ n, (‖f n x‖₊ ^ p.to_real : ℝ≥0∞)) at_top =
    (liminf (λ n, (‖f n x‖₊ : ℝ≥0∞)) at_top)^ p.to_real,
  { change liminf (λ n, ennreal.order_iso_rpow p.to_real hppos (‖f n x‖₊ : ℝ≥0∞)) at_top =
      ennreal.order_iso_rpow p.to_real hppos (liminf (λ n, (‖f n x‖₊ : ℝ≥0∞)) at_top),
    refine (order_iso.liminf_apply (ennreal.order_iso_rpow p.to_real _) _ _ _ _).symm;
    is_bounded_default },
  rw this at hx,
  rw [← ennreal.rpow_one (liminf (λ n, ‖f n x‖₊) at_top), ← mul_inv_cancel hppos.ne.symm,
    ennreal.rpow_mul],
  exact ennreal.rpow_lt_top_of_nonneg (inv_nonneg.2 hppos.le) hx.ne,
end

end liminf

end ℒp

end measure_theory
