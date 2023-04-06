/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import analysis.normed_space.indicator_function
import analysis.normed.group.hom
import measure_theory.function.ess_sup
import measure_theory.function.ae_eq_fun
import measure_theory.integral.mean_inequalities
import measure_theory.function.strongly_measurable.inner
import topology.continuous_function.compact

/-!
# ℒp space and Lp space

This file describes properties of almost everywhere strongly measurable functions with finite
seminorm, denoted by `snorm f p μ` and defined for `p:ℝ≥0∞` asmm_group (Lp E p μ) := `0` if `p=0`,
`(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `0 < p < ∞` and `ess_sup ‖f‖ μ` for `p=∞`.

The Prop-valued `mem_ℒp f p μ` states that a function `f : α → E` has finite seminorm.
The space `Lp E p μ` is the subtype of elements of `α →ₘ[μ] E` (see ae_eq_fun) such that
`snorm f p μ` is finite. For `1 ≤ p`, `snorm` defines a norm and `Lp` is a complete metric space.

## Main definitions

* `snorm' f p μ` : `(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `f : α → F` and `p : ℝ`, where `α` is a  measurable
  space and `F` is a normed group.
* `snorm_ess_sup f μ` : seminorm in `ℒ∞`, equal to the essential supremum `ess_sup ‖f‖ μ`.
* `snorm f p μ` : for `p : ℝ≥0∞`, seminorm in `ℒp`, equal to `0` for `p=0`, to `snorm' f p μ`
  for `0 < p < ∞` and to `snorm_ess_sup f μ` for `p = ∞`.

* `mem_ℒp f p μ` : property that the function `f` is almost everywhere strongly measurable and has
  finite `p`-seminorm for the measure `μ` (`snorm f p μ < ∞`)
* `Lp E p μ` : elements of `α →ₘ[μ] E` (see ae_eq_fun) such that `snorm f p μ` is finite. Defined
  as an `add_subgroup` of `α →ₘ[μ] E`.

Lipschitz functions vanishing at zero act by composition on `Lp`. We define this action, and prove
that it is continuous. In particular,
* `continuous_linear_map.comp_Lp` defines the action on `Lp` of a continuous linear map.
* `Lp.pos_part` is the positive part of an `Lp` function.
* `Lp.neg_part` is the negative part of an `Lp` function.

When `α` is a topological space equipped with a finite Borel measure, there is a bounded linear map
from the normed space of bounded continuous functions (`α →ᵇ E`) to `Lp E p μ`.  We construct this
as `bounded_continuous_function.to_Lp`.

## Notations

* `α →₁[μ] E` : the type `Lp E 1 μ`.
* `α →₂[μ] E` : the type `Lp E 2 μ`.

## Implementation

Since `Lp` is defined as an `add_subgroup`, dot notation does not work. Use `Lp.measurable f` to
say that the coercion of `f` to a genuine function is measurable, instead of the non-working
`f.measurable`.

To prove that two `Lp` elements are equal, it suffices to show that their coercions to functions
coincide almost everywhere (this is registered as an `ext` rule). This can often be done using
`filter_upwards`. For instance, a proof from first principles that `f + (g + h) = (f + g) + h`
could read (in the `Lp` namespace)
```
example (f g h : Lp E p μ) : (f + g) + h = f + (g + h) :=
begin
  ext1,
  filter_upwards [coe_fn_add (f + g) h, coe_fn_add f g, coe_fn_add f (g + h), coe_fn_add g h]
    with _ ha1 ha2 ha3 ha4,
  simp only [ha1, ha2, ha3, ha4, add_assoc],
end
```
The lemma `coe_fn_add` states that the coercion of `f + g` coincides almost everywhere with the sum
of the coercions of `f` and `g`. All such lemmas use `coe_fn` in their name, to distinguish the
function coercion from the coercion to almost everywhere defined functions.
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

lemma snorm'_mono_ae {f : α → F} {g : α → G} (hq : 0 ≤ q) (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
  snorm' f q μ ≤ snorm' g q μ :=
begin
  rw [snorm'],
  refine ennreal.rpow_le_rpow _ (one_div_nonneg.2 hq),
  refine lintegral_mono_ae (h.mono $ λ x hx, _),
  exact ennreal.rpow_le_rpow (ennreal.coe_le_coe.2 hx) hq
end

lemma snorm'_congr_norm_ae {f g : α → F} (hfg : ∀ᵐ x ∂μ, ‖f x‖ = ‖g x‖) :
  snorm' f q μ = snorm' g q μ :=
begin
  have : (λ x, (‖f x‖₊ ^ q : ℝ≥0∞)) =ᵐ[μ] (λ x, ‖g x‖₊ ^ q),
    from hfg.mono (λ x hx, by { simp only [← coe_nnnorm, nnreal.coe_eq] at hx, simp [hx] }),
  simp only [snorm', lintegral_congr_ae this]
end

lemma snorm'_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) : snorm' f q μ = snorm' g q μ :=
snorm'_congr_norm_ae (hfg.fun_comp _)

lemma snorm_ess_sup_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) :
  snorm_ess_sup f μ = snorm_ess_sup g μ :=
ess_sup_congr_ae (hfg.fun_comp (coe ∘ nnnorm))

lemma snorm_mono_ae {f : α → F} {g : α → G} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
  snorm f p μ ≤ snorm g p μ :=
begin
  simp only [snorm],
  split_ifs,
  { exact le_rfl },
  { refine ess_sup_mono_ae (h.mono $ λ x hx, _),
    exact_mod_cast hx },
  { exact snorm'_mono_ae ennreal.to_real_nonneg h }
end

lemma snorm_mono_ae_real {f : α → F} {g : α → ℝ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x) :
  snorm f p μ ≤ snorm g p μ :=
snorm_mono_ae $ h.mono (λ x hx, hx.trans ((le_abs_self _).trans (real.norm_eq_abs _).symm.le))

lemma snorm_mono {f : α → F} {g : α → G} (h : ∀ x, ‖f x‖ ≤ ‖g x‖) :
  snorm f p μ ≤ snorm g p μ :=
snorm_mono_ae (eventually_of_forall (λ x, h x))

lemma snorm_mono_real {f : α → F} {g : α → ℝ} (h : ∀ x, ‖f x‖ ≤ g x) :
  snorm f p μ ≤ snorm g p μ :=
snorm_mono_ae_real (eventually_of_forall (λ x, h x))

lemma snorm_ess_sup_le_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
  snorm_ess_sup f μ ≤ ennreal.of_real C:=
begin
  simp_rw [snorm_ess_sup, ← of_real_norm_eq_coe_nnnorm],
  refine ess_sup_le_of_ae_le (ennreal.of_real C) (hfC.mono (λ x hx, _)),
  exact ennreal.of_real_le_of_real hx,
end

lemma snorm_ess_sup_lt_top_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
  snorm_ess_sup f μ < ∞ :=
(snorm_ess_sup_le_of_ae_bound hfC).trans_lt ennreal.of_real_lt_top

lemma snorm_le_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
  snorm f p μ ≤ ((μ set.univ) ^ p.to_real⁻¹) * (ennreal.of_real C) :=
begin
  by_cases hμ : μ = 0,
  { simp [hμ] },
  haveI : μ.ae.ne_bot := ae_ne_bot.mpr hμ,
  by_cases hp : p = 0,
  { simp [hp] },
  have hC : 0 ≤ C, from le_trans (norm_nonneg _) hfC.exists.some_spec,
  have hC' : ‖C‖ = C := by rw [real.norm_eq_abs, abs_eq_self.mpr hC],
  have : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖(λ _, C) x‖, from hfC.mono (λ x hx, hx.trans (le_of_eq hC'.symm)),
  convert snorm_mono_ae this,
  rw [snorm_const _ hp hμ, mul_comm, ← of_real_norm_eq_coe_nnnorm, hC', one_div]
end

lemma snorm_congr_norm_ae {f : α → F} {g : α → G} (hfg : ∀ᵐ x ∂μ, ‖f x‖ = ‖g x‖) :
  snorm f p μ = snorm g p μ :=
le_antisymm (snorm_mono_ae $ eventually_eq.le hfg)
  (snorm_mono_ae $ (eventually_eq.symm hfg).le)

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

lemma snorm_sub_le
  {f g : α → E} (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) (hp1 : 1 ≤ p) :
  snorm (f - g) p μ ≤ snorm f p μ + snorm g p μ :=
calc snorm (f - g) p μ = snorm (f + - g) p μ : by rw sub_eq_add_neg
  -- We cannot use snorm_add_le on f and (-g) because we don't have `ae_measurable (-g) μ`, since
  -- we don't suppose `[borel_space E]`.
... = snorm (λ x, ‖f x + - g x‖) p μ : (snorm_norm (f + - g)).symm
... ≤ snorm (λ x, ‖f x‖ + ‖- g x‖) p μ : by
{ refine snorm_mono_real (λ x, _), rw norm_norm, exact norm_add_le _ _, }
... = snorm (λ x, ‖f x‖ + ‖g x‖) p μ : by simp_rw norm_neg
... ≤ snorm (λ x, ‖f x‖) p μ + snorm (λ x, ‖g x‖) p μ : snorm_add_le hf.norm hg.norm hp1
... = snorm f p μ + snorm g p μ : by rw [← snorm_norm f, ← snorm_norm g]

lemma snorm_add_lt_top_of_one_le {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ)
  (hq1 : 1 ≤ p) : snorm (f + g) p μ < ∞ :=
lt_of_le_of_lt (snorm_add_le hf.1 hg.1 hq1) (ennreal.add_lt_top.mpr ⟨hf.2, hg.2⟩)

lemma snorm'_add_lt_top_of_le_one
  {f g : α → E} (hf : ae_strongly_measurable f μ)
  (hf_snorm : snorm' f q μ < ∞) (hg_snorm : snorm' g q μ < ∞) (hq_pos : 0 < q) (hq1 : q ≤ 1) :
  snorm' (f + g) q μ < ∞ :=
calc (∫⁻ a, ↑‖(f + g) a‖₊ ^ q ∂μ) ^ (1 / q)
    ≤ (∫⁻ a, (((λ a, (‖f a‖₊ : ℝ≥0∞))
        + (λ a, (‖g a‖₊ : ℝ≥0∞))) a) ^ q ∂μ) ^ (1 / q) :
begin
  refine ennreal.rpow_le_rpow _ (by simp [hq_pos.le] : 0 ≤ 1 / q),
  refine lintegral_mono (λ a, ennreal.rpow_le_rpow _ hq_pos.le),
  simp [←ennreal.coe_add, nnnorm_add_le],
end
... ≤ (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ q + (‖g a‖₊ : ℝ≥0∞) ^ q ∂μ) ^ (1 / q) :
begin
  refine ennreal.rpow_le_rpow (lintegral_mono (λ a, _)) (by simp [hq_pos.le] : 0 ≤ 1 / q),
  exact ennreal.rpow_add_le_add_rpow _ _ hq_pos.le hq1,
end
... < ∞ :
begin
  refine ennreal.rpow_lt_top_of_nonneg (by simp [hq_pos.le] : 0 ≤ 1 / q) _,
  rw [lintegral_add_left' (hf.ennnorm.pow_const q), ennreal.add_ne_top],
  exact ⟨(lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top hq_pos hf_snorm).ne,
    (lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top hq_pos hg_snorm).ne⟩,
end

lemma snorm_add_lt_top {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  snorm (f + g) p μ < ∞ :=
begin
  by_cases h0 : p = 0,
  { simp [h0], },
  rw ←ne.def at h0,
  cases le_total 1 p with hp1 hp1,
  { exact snorm_add_lt_top_of_one_le hf hg hp1, },
  have hp_top : p ≠ ∞, from (lt_of_le_of_lt hp1 ennreal.coe_lt_top).ne,
  have hp_pos : 0 < p.to_real,
  { rw [← ennreal.zero_to_real, @ennreal.to_real_lt_to_real 0 p ennreal.coe_ne_top hp_top],
    exact ((zero_le p).lt_of_ne h0.symm), },
  have hp1_real : p.to_real ≤ 1,
  { rwa [← ennreal.one_to_real, @ennreal.to_real_le_to_real p 1 hp_top ennreal.coe_ne_top], },
  rw snorm_eq_snorm' h0 hp_top,
  rw [mem_ℒp, snorm_eq_snorm' h0 hp_top] at hf hg,
  exact snorm'_add_lt_top_of_le_one hf.1 hf.2 hg.2 hp_pos hp1_real,
end

lemma ae_le_of_snorm_ess_sup_le {f : α → F} {x : ℝ≥0∞} :
  snorm_ess_sup f μ ≤ x → ∀ᵐ y ∂μ, ↑‖f y‖₊ ≤ x :=
ae_le_of_ess_sup_le

lemma meas_lt_of_snorm_ess_sup_le {f : α → F} {x : ℝ≥0∞} :
  snorm_ess_sup f μ ≤ x → μ {y | x < ‖f y‖₊} = 0 :=
meas_lt_of_ess_sup_le

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

section borel_space
-- variable [borel_space E]

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

end borel_space

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]

lemma snorm'_const_smul {f : α → F} (c : 𝕜) (hq_pos : 0 < q) :
  snorm' (c • f) q μ = (‖c‖₊ : ℝ≥0∞) * snorm' f q μ :=
begin
  rw snorm',
  simp_rw [pi.smul_apply, nnnorm_smul, ennreal.coe_mul,
    ennreal.mul_rpow_of_nonneg _ _ hq_pos.le],
  suffices h_integral : ∫⁻ a, ↑(‖c‖₊) ^ q * ↑‖f a‖₊ ^ q ∂μ
    = (‖c‖₊ : ℝ≥0∞)^q * ∫⁻ a, ‖f a‖₊ ^ q ∂μ,
  { apply_fun (λ x, x ^ (1/q)) at h_integral,
    rw [h_integral, ennreal.mul_rpow_of_nonneg _ _ (by simp [hq_pos.le] : 0 ≤ 1 / q)],
    congr,
    simp_rw [←ennreal.rpow_mul, one_div, mul_inv_cancel hq_pos.ne.symm, ennreal.rpow_one], },
  rw lintegral_const_mul',
  rw ennreal.coe_rpow_of_nonneg _ hq_pos.le,
  exact ennreal.coe_ne_top,
end

lemma snorm_ess_sup_const_smul {f : α → F} (c : 𝕜) :
  snorm_ess_sup (c • f) μ = (‖c‖₊ : ℝ≥0∞) * snorm_ess_sup f μ :=
by simp_rw [snorm_ess_sup,  pi.smul_apply, nnnorm_smul, ennreal.coe_mul, ennreal.ess_sup_const_mul]

lemma snorm_const_smul {f : α → F} (c : 𝕜) :
  snorm (c • f) p μ = (‖c‖₊ : ℝ≥0∞) * snorm f p μ :=
begin
  by_cases h0 : p = 0,
  { simp [h0], },
  by_cases h_top : p = ∞,
  { simp [h_top, snorm_ess_sup_const_smul], },
  repeat { rw snorm_eq_snorm' h0 h_top, },
  rw ←ne.def at h0,
  exact snorm'_const_smul c (ennreal.to_real_pos h0 h_top),
end

lemma mem_ℒp.const_smul {f : α → E} (hf : mem_ℒp f p μ) (c : 𝕜) :
  mem_ℒp (c • f) p μ :=
⟨ae_strongly_measurable.const_smul hf.1 c,
  (snorm_const_smul c).le.trans_lt (ennreal.mul_lt_top ennreal.coe_ne_top hf.2.ne)⟩

lemma mem_ℒp.const_mul {f : α → 𝕜} (hf : mem_ℒp f p μ) (c : 𝕜) :
  mem_ℒp (λ x, c * f x) p μ :=
hf.const_smul c

lemma snorm'_smul_le_mul_snorm' {p q r : ℝ}
  {f : α → E} (hf : ae_strongly_measurable f μ) {φ : α → 𝕜} (hφ : ae_strongly_measurable φ μ)
  (hp0_lt : 0 < p) (hpq : p < q) (hpqr : 1/p = 1/q + 1/r) :
  snorm' (φ • f) p μ ≤ snorm' φ q μ * snorm' f r μ :=
begin
  simp_rw [snorm', pi.smul_apply', nnnorm_smul, ennreal.coe_mul],
  exact ennreal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hφ.ennnorm
    hf.ennnorm,
end

lemma snorm_smul_le_snorm_top_mul_snorm (p : ℝ≥0∞)
  {f : α → E} (hf : ae_strongly_measurable f μ) (φ : α → 𝕜) :
  snorm (φ • f) p μ ≤ snorm φ ∞ μ * snorm f p μ :=
begin
  by_cases hp_top : p = ∞,
  { simp_rw [hp_top, snorm_exponent_top, snorm_ess_sup, pi.smul_apply', nnnorm_smul,
      ennreal.coe_mul],
    exact ennreal.ess_sup_mul_le _ _, },
  by_cases hp_zero : p = 0,
  { simp only [hp_zero, snorm_exponent_zero, mul_zero, le_zero_iff], },
  simp_rw [snorm_eq_lintegral_rpow_nnnorm hp_zero hp_top, snorm_exponent_top, snorm_ess_sup],
  calc (∫⁻ x, ↑‖(φ • f) x‖₊ ^ p.to_real ∂μ) ^ (1 / p.to_real)
      = (∫⁻ x, ↑‖φ x‖₊ ^ p.to_real * ↑‖f x‖₊ ^ p.to_real ∂μ) ^ (1 / p.to_real) :
    begin
      congr,
      ext1 x,
      rw [pi.smul_apply', nnnorm_smul, ennreal.coe_mul,
        ennreal.mul_rpow_of_nonneg _ _ (ennreal.to_real_nonneg)],
    end
  ... ≤ (∫⁻ x, (ess_sup (λ x, ↑‖φ x‖₊) μ) ^ p.to_real * ↑‖f x‖₊ ^ p.to_real ∂μ) ^ (1 / p.to_real) :
    begin
      refine ennreal.rpow_le_rpow _ _,
      swap, { rw one_div_nonneg, exact ennreal.to_real_nonneg, },
      refine lintegral_mono_ae _,
      filter_upwards [@ennreal.ae_le_ess_sup _ _ μ (λ x, ↑‖φ x‖₊)] with x hx,
      exact mul_le_mul_right' (ennreal.rpow_le_rpow hx ennreal.to_real_nonneg) _
    end
  ... = ess_sup (λ x, ↑‖φ x‖₊) μ * (∫⁻ x, ↑‖f x‖₊ ^ p.to_real ∂μ) ^ (1 / p.to_real) :
    begin
      rw lintegral_const_mul'',
      swap, { exact hf.nnnorm.ae_measurable.coe_nnreal_ennreal.pow ae_measurable_const, },
      rw ennreal.mul_rpow_of_nonneg,
      swap, { rw one_div_nonneg, exact ennreal.to_real_nonneg, },
      rw [← ennreal.rpow_mul, one_div, mul_inv_cancel, ennreal.rpow_one],
      rw [ne.def, ennreal.to_real_eq_zero_iff, auto.not_or_eq],
      exact ⟨hp_zero, hp_top⟩,
    end
end

lemma snorm_smul_le_snorm_mul_snorm_top (p : ℝ≥0∞)
  (f : α → E) {φ : α → 𝕜} (hφ : ae_strongly_measurable φ μ) :
  snorm (φ • f) p μ ≤ snorm φ p μ * snorm f ∞ μ :=
begin
  rw ← snorm_norm,
  simp_rw [pi.smul_apply', norm_smul],
  have : (λ x, ‖φ x‖ * ‖f x‖) = (λ x, ‖f x‖) • (λ x, ‖φ x‖),
  { rw [smul_eq_mul, mul_comm], refl, },
  rw this,
  have h := snorm_smul_le_snorm_top_mul_snorm p hφ.norm (λ x, ‖f x‖),
  refine h.trans_eq _,
  simp_rw snorm_norm,
  rw mul_comm,
end

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of a scalar product `φ • f`. -/
lemma snorm_smul_le_mul_snorm {p q r : ℝ≥0∞}
  {f : α → E} (hf : ae_strongly_measurable f μ) {φ : α → 𝕜} (hφ : ae_strongly_measurable φ μ)
  (hpqr : 1/p = 1/q + 1/r) :
  snorm (φ • f) p μ ≤ snorm φ q μ * snorm f r μ :=
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
    exact snorm_smul_le_snorm_top_mul_snorm p hf φ, },
  by_cases hr_top : r = ∞,
  { have hpq : p = q,
    { simpa only [hr_top, one_div, ennreal.div_top, add_zero, inv_inj] using hpqr, },
    rw [← hpq, hr_top],
    exact snorm_smul_le_snorm_mul_snorm_top p f hφ, },
  have hpq : p < q,
  { suffices : 1 / q < 1 / p,
    { rwa [one_div, one_div, ennreal.inv_lt_inv] at this, },
    rw hpqr,
    refine ennreal.lt_add_right _ _,
    { simp only [hq_ne_zero, one_div, ne.def, ennreal.inv_eq_top, not_false_iff], },
    { simp only [hr_top, one_div, ne.def, ennreal.inv_eq_zero, not_false_iff], }, },
  rw [snorm_eq_snorm' hp_zero (hpq.trans_le le_top).ne, snorm_eq_snorm' hq_ne_zero hq_top,
    snorm_eq_snorm' hr_ne_zero hr_top],
  refine snorm'_smul_le_mul_snorm' hf hφ _ _ _,
  { exact ennreal.to_real_pos hp_zero (hpq.trans_le le_top).ne, },
  { exact ennreal.to_real_strict_mono hq_top hpq, },
  rw [← ennreal.one_to_real, ← ennreal.to_real_div, ← ennreal.to_real_div, ← ennreal.to_real_div,
    hpqr, ennreal.to_real_add],
  { simp only [hq_ne_zero, one_div, ne.def, ennreal.inv_eq_top, not_false_iff], },
  { simp only [hr_ne_zero, one_div, ne.def, ennreal.inv_eq_top, not_false_iff], },
end

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

end normed_space

section monotonicity

lemma snorm_le_mul_snorm_aux_of_nonneg {f : α → F} {g : α → G} {c : ℝ}
  (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) (hc : 0 ≤ c) (p : ℝ≥0∞) :
  snorm f p μ ≤ (ennreal.of_real c) * snorm g p μ :=
begin
  lift c to ℝ≥0 using hc,
  rw [ennreal.of_real_coe_nnreal, ← c.nnnorm_eq, ← snorm_norm g, ← snorm_const_smul (c : ℝ)],
  swap, apply_instance,
  refine snorm_mono_ae _,
  simpa
end

lemma snorm_le_mul_snorm_aux_of_neg {f : α → F} {g : α → G} {c : ℝ}
  (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) (hc : c < 0) (p : ℝ≥0∞) :
  snorm f p μ = 0 ∧ snorm g p μ = 0 :=
begin
  suffices : f =ᵐ[μ] 0 ∧ g =ᵐ[μ] 0,
    by simp [snorm_congr_ae this.1, snorm_congr_ae this.2],
  refine ⟨h.mono $ λ x hx, _, h.mono $ λ x hx, _⟩,
  { refine norm_le_zero_iff.1 (hx.trans _),
    exact mul_nonpos_of_nonpos_of_nonneg hc.le (norm_nonneg _) },
  { refine norm_le_zero_iff.1 (nonpos_of_mul_nonneg_right _ hc),
    exact (norm_nonneg _).trans hx }
end

lemma snorm_le_mul_snorm_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ}
  (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) (p : ℝ≥0∞) :
  snorm f p μ ≤ (ennreal.of_real c) * snorm g p μ :=
begin
  cases le_or_lt 0 c with hc hc,
  { exact snorm_le_mul_snorm_aux_of_nonneg h hc p },
  { simp [snorm_le_mul_snorm_aux_of_neg h hc p] }
end

lemma mem_ℒp.of_le_mul {f : α → E} {g : α → F} {c : ℝ}
  (hg : mem_ℒp g p μ) (hf : ae_strongly_measurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) :
  mem_ℒp f p μ :=
⟨hf, lt_of_le_of_lt (snorm_le_mul_snorm_of_ae_le_mul hfg p) $
  ennreal.mul_lt_top ennreal.of_real_ne_top hg.snorm_ne_top⟩

end monotonicity

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
  exact hf.of_le_mul hf.1.re (eventually_of_forall this),
end

lemma mem_ℒp.im (hf : mem_ℒp f p μ) : mem_ℒp (λ x, is_R_or_C.im (f x)) p μ :=
begin
  have : ∀ x, ‖is_R_or_C.im (f x)‖ ≤ 1 * ‖f x‖,
    by { intro x, rw one_mul, exact is_R_or_C.norm_im_le_norm (f x), },
  exact hf.of_le_mul hf.1.im (eventually_of_forall this),
end

end is_R_or_C

section inner_product
variables {E' 𝕜 : Type*} [is_R_or_C 𝕜] [normed_add_comm_group E'] [inner_product_space 𝕜 E']

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E' _ x y

lemma mem_ℒp.const_inner (c : E') {f : α → E'} (hf : mem_ℒp f p μ) :
  mem_ℒp (λ a, ⟪c, f a⟫) p μ :=
hf.of_le_mul (ae_strongly_measurable.inner ae_strongly_measurable_const hf.1)
  (eventually_of_forall (λ x, norm_inner_le_norm _ _))

lemma mem_ℒp.inner_const {f : α → E'} (hf : mem_ℒp f p μ) (c : E') :
  mem_ℒp (λ a, ⟪f a, c⟫) p μ :=
hf.of_le_mul (ae_strongly_measurable.inner hf.1 ae_strongly_measurable_const)
  (eventually_of_forall (λ x, by { rw mul_comm, exact norm_inner_le_norm _ _, }))

end inner_product

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

/-!
### Lp space

The space of equivalence classes of measurable functions for which `snorm f p μ < ∞`.
-/

@[simp] lemma snorm_ae_eq_fun {α E : Type*} [measurable_space α] {μ : measure α}
  [normed_add_comm_group E] {p : ℝ≥0∞} {f : α → E} (hf : ae_strongly_measurable f μ) :
  snorm (ae_eq_fun.mk f hf) p μ = snorm f p μ :=
snorm_congr_ae (ae_eq_fun.coe_fn_mk _ _)

lemma mem_ℒp.snorm_mk_lt_top {α E : Type*} [measurable_space α] {μ : measure α}
  [normed_add_comm_group E] {p : ℝ≥0∞} {f : α → E} (hfp : mem_ℒp f p μ) :
  snorm (ae_eq_fun.mk f hfp.1) p μ < ∞ :=
by simp [hfp.2]

/-- Lp space -/
def Lp {α} (E : Type*) {m : measurable_space α} [normed_add_comm_group E]
  (p : ℝ≥0∞) (μ : measure α . volume_tac) : add_subgroup (α →ₘ[μ] E) :=
{ carrier := {f | snorm f p μ < ∞},
  zero_mem' := by simp [snorm_congr_ae ae_eq_fun.coe_fn_zero, snorm_zero],
  add_mem' := λ f g hf hg, by simp [snorm_congr_ae (ae_eq_fun.coe_fn_add _ _),
    snorm_add_lt_top ⟨f.ae_strongly_measurable, hf⟩ ⟨g.ae_strongly_measurable, hg⟩],
  neg_mem' := λ f hf,
    by rwa [set.mem_set_of_eq, snorm_congr_ae (ae_eq_fun.coe_fn_neg _), snorm_neg] }

localized "notation (name := measure_theory.L1)
  α ` →₁[`:25 μ `] ` E := measure_theory.Lp E 1 μ" in measure_theory
localized "notation (name := measure_theory.L2)
  α ` →₂[`:25 μ `] ` E := measure_theory.Lp E 2 μ" in measure_theory

namespace mem_ℒp

/-- make an element of Lp from a function verifying `mem_ℒp` -/
def to_Lp (f : α → E) (h_mem_ℒp : mem_ℒp f p μ) : Lp E p μ :=
⟨ae_eq_fun.mk f h_mem_ℒp.1, h_mem_ℒp.snorm_mk_lt_top⟩

lemma coe_fn_to_Lp {f : α → E} (hf : mem_ℒp f p μ) : hf.to_Lp f =ᵐ[μ] f :=
ae_eq_fun.coe_fn_mk _ _

lemma to_Lp_congr {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) (hfg : f =ᵐ[μ] g) :
  hf.to_Lp f = hg.to_Lp g :=
by simp [to_Lp, hfg]

@[simp] lemma to_Lp_eq_to_Lp_iff {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  hf.to_Lp f = hg.to_Lp g ↔ f =ᵐ[μ] g :=
by simp [to_Lp]

@[simp] lemma to_Lp_zero (h : mem_ℒp (0 : α → E) p μ) : h.to_Lp 0 = 0 := rfl

lemma to_Lp_add {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  (hf.add hg).to_Lp (f + g) = hf.to_Lp f + hg.to_Lp g := rfl

lemma to_Lp_neg {f : α → E} (hf : mem_ℒp f p μ) : hf.neg.to_Lp (-f) = - hf.to_Lp f := rfl

lemma to_Lp_sub {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  (hf.sub hg).to_Lp (f - g) = hf.to_Lp f - hg.to_Lp g := rfl

end mem_ℒp

namespace Lp

instance : has_coe_to_fun (Lp E p μ) (λ _, α → E) := ⟨λ f, ((f : α →ₘ[μ] E) : α → E)⟩

@[ext] lemma ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g :=
begin
  cases f,
  cases g,
  simp only [subtype.mk_eq_mk],
  exact ae_eq_fun.ext h
end

lemma ext_iff {f g : Lp E p μ} : f = g ↔ f =ᵐ[μ] g :=
⟨λ h, by rw h, λ h, ext h⟩

lemma mem_Lp_iff_snorm_lt_top {f : α →ₘ[μ] E} : f ∈ Lp E p μ ↔ snorm f p μ < ∞ := iff.refl _

lemma mem_Lp_iff_mem_ℒp {f : α →ₘ[μ] E} : f ∈ Lp E p μ ↔ mem_ℒp f p μ :=
by simp [mem_Lp_iff_snorm_lt_top, mem_ℒp, f.strongly_measurable.ae_strongly_measurable]

protected lemma antitone [is_finite_measure μ] {p q : ℝ≥0∞} (hpq : p ≤ q) : Lp E q μ ≤ Lp E p μ :=
λ f hf, (mem_ℒp.mem_ℒp_of_exponent_le ⟨f.ae_strongly_measurable, hf⟩ hpq).2

@[simp] lemma coe_fn_mk {f : α →ₘ[μ] E} (hf : snorm f p μ < ∞) :
  ((⟨f, hf⟩ : Lp E p μ) : α → E) = f := rfl

@[simp] lemma coe_mk {f : α →ₘ[μ] E} (hf : snorm f p μ < ∞) :
  ((⟨f, hf⟩ : Lp E p μ) : α →ₘ[μ] E) = f := rfl

@[simp] lemma to_Lp_coe_fn (f : Lp E p μ) (hf : mem_ℒp f p μ) : hf.to_Lp f = f :=
by { cases f, simp [mem_ℒp.to_Lp] }

lemma snorm_lt_top (f : Lp E p μ) : snorm f p μ < ∞ := f.prop

lemma snorm_ne_top (f : Lp E p μ) : snorm f p μ ≠ ∞ := (snorm_lt_top f).ne

@[measurability]
protected lemma strongly_measurable (f : Lp E p μ) : strongly_measurable f :=
f.val.strongly_measurable

@[measurability]
protected lemma ae_strongly_measurable (f : Lp E p μ) : ae_strongly_measurable f μ :=
f.val.ae_strongly_measurable

protected lemma mem_ℒp (f : Lp E p μ) : mem_ℒp f p μ := ⟨Lp.ae_strongly_measurable f, f.prop⟩

variables (E p μ)
lemma coe_fn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0 := ae_eq_fun.coe_fn_zero
variables {E p μ}

lemma coe_fn_neg (f : Lp E p μ) : ⇑(-f) =ᵐ[μ] -f := ae_eq_fun.coe_fn_neg _

lemma coe_fn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] f + g := ae_eq_fun.coe_fn_add _ _

lemma coe_fn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] f - g := ae_eq_fun.coe_fn_sub _ _

lemma mem_Lp_const (α) {m : measurable_space α} (μ : measure α) (c : E) [is_finite_measure μ] :
  @ae_eq_fun.const α _ _ μ _ c ∈ Lp E p μ :=
(mem_ℒp_const c).snorm_mk_lt_top

instance : has_norm (Lp E p μ) := { norm := λ f, ennreal.to_real (snorm f p μ) }

instance : has_dist (Lp E p μ) := { dist := λ f g, ‖f - g‖}

instance : has_edist (Lp E p μ) := { edist := λ f g, snorm (f - g) p μ }

lemma norm_def (f : Lp E p μ) : ‖f‖ = ennreal.to_real (snorm f p μ) := rfl

@[simp] lemma norm_to_Lp (f : α → E) (hf : mem_ℒp f p μ) :
  ‖hf.to_Lp f‖ = ennreal.to_real (snorm f p μ) :=
by rw [norm_def, snorm_congr_ae (mem_ℒp.coe_fn_to_Lp hf)]

lemma dist_def (f g : Lp E p μ) : dist f g = (snorm (f - g) p μ).to_real :=
begin
  simp_rw [dist, norm_def],
  congr' 1,
  apply snorm_congr_ae (coe_fn_sub _ _),
end

lemma edist_def (f g : Lp E p μ) : edist f g = snorm (f - g) p μ :=
rfl

@[simp] lemma edist_to_Lp_to_Lp (f g : α → E) (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  edist (hf.to_Lp f) (hg.to_Lp g) = snorm (f - g) p μ :=
by { rw edist_def, exact snorm_congr_ae (hf.coe_fn_to_Lp.sub hg.coe_fn_to_Lp) }

@[simp] lemma edist_to_Lp_zero (f : α → E) (hf : mem_ℒp f p μ) :
  edist (hf.to_Lp f) 0 = snorm f p μ :=
by { convert edist_to_Lp_to_Lp f 0 hf zero_mem_ℒp, simp }

@[simp] lemma norm_zero : ‖(0 : Lp E p μ)‖ = 0 :=
begin
  change (snorm ⇑(0 : α →ₘ[μ] E) p μ).to_real = 0,
  simp [snorm_congr_ae ae_eq_fun.coe_fn_zero, snorm_zero]
end

lemma norm_eq_zero_iff {f : Lp E p μ} (hp : 0 < p) : ‖f‖ = 0 ↔ f = 0 :=
begin
  refine ⟨λ hf, _, λ hf, by simp [hf]⟩,
  rw [norm_def, ennreal.to_real_eq_zero_iff] at hf,
  cases hf,
  { rw snorm_eq_zero_iff (Lp.ae_strongly_measurable f) hp.ne.symm at hf,
    exact subtype.eq (ae_eq_fun.ext (hf.trans ae_eq_fun.coe_fn_zero.symm)), },
  { exact absurd hf (snorm_ne_top f), },
end

lemma eq_zero_iff_ae_eq_zero {f : Lp E p μ} : f = 0 ↔ f =ᵐ[μ] 0 :=
begin
  split,
  { assume h,
    rw h,
    exact ae_eq_fun.coe_fn_const _ _ },
  { assume h,
    ext1,
    filter_upwards [h, ae_eq_fun.coe_fn_const α (0 : E)] with _ ha h'a,
    rw ha,
    exact h'a.symm, },
end

@[simp] lemma norm_neg {f : Lp E p μ} : ‖-f‖ = ‖f‖ :=
by rw [norm_def, norm_def, snorm_congr_ae (coe_fn_neg _), snorm_neg]

lemma norm_le_mul_norm_of_ae_le_mul {c : ℝ} {f : Lp E p μ} {g : Lp F p μ}
  (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : ‖f‖ ≤ c * ‖g‖ :=
begin
  simp only [norm_def],
  cases le_or_lt 0 c with hc hc,
  { have := snorm_le_mul_snorm_of_ae_le_mul h p,
    rwa [← ennreal.to_real_le_to_real, ennreal.to_real_mul, ennreal.to_real_of_real hc] at this,
    { exact (Lp.mem_ℒp _).snorm_ne_top },
    { exact ennreal.mul_ne_top ennreal.of_real_ne_top (Lp.mem_ℒp _).snorm_ne_top } },
  { have := snorm_le_mul_snorm_aux_of_neg h hc p,
    simp [this] }
end

lemma norm_le_norm_of_ae_le {f : Lp E p μ} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
  ‖f‖ ≤ ‖g‖ :=
begin
  rw [norm_def, norm_def, ennreal.to_real_le_to_real (snorm_ne_top _) (snorm_ne_top _)],
  exact snorm_mono_ae h
end

lemma mem_Lp_of_ae_le_mul {c : ℝ} {f : α →ₘ[μ] E} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) :
  f ∈ Lp E p μ :=
mem_Lp_iff_mem_ℒp.2 $ mem_ℒp.of_le_mul (Lp.mem_ℒp g) f.ae_strongly_measurable h

lemma mem_Lp_of_ae_le {f : α →ₘ[μ] E} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
  f ∈ Lp E p μ :=
mem_Lp_iff_mem_ℒp.2 $ mem_ℒp.of_le (Lp.mem_ℒp g) f.ae_strongly_measurable h

lemma mem_Lp_of_ae_bound [is_finite_measure μ] {f : α →ₘ[μ] E} (C : ℝ) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
  f ∈ Lp E p μ :=
mem_Lp_iff_mem_ℒp.2 $ mem_ℒp.of_bound f.ae_strongly_measurable _ hfC

lemma norm_le_of_ae_bound [is_finite_measure μ] {f : Lp E p μ} {C : ℝ} (hC : 0 ≤ C)
  (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
  ‖f‖ ≤ (measure_univ_nnreal μ) ^ (p.to_real)⁻¹ * C :=
begin
  by_cases hμ : μ = 0,
  { by_cases hp : p.to_real⁻¹ = 0,
    { simpa [hp, hμ, norm_def] using hC },
    { simp [hμ, norm_def, real.zero_rpow hp] } },
  let A : ℝ≥0 := (measure_univ_nnreal μ) ^ (p.to_real)⁻¹ * ⟨C, hC⟩,
  suffices : snorm f p μ ≤ A,
  { exact ennreal.to_real_le_coe_of_le_coe this },
  convert snorm_le_of_ae_bound hfC,
  rw [← coe_measure_univ_nnreal μ, ennreal.coe_rpow_of_ne_zero (measure_univ_nnreal_pos hμ).ne',
    ennreal.coe_mul],
  congr,
  rw max_eq_left hC
end

instance [hp : fact (1 ≤ p)] : normed_add_comm_group (Lp E p μ) :=
{ edist := edist,
  edist_dist := λ f g, by
    rw [edist_def, dist_def, ←snorm_congr_ae (coe_fn_sub _ _),
      ennreal.of_real_to_real (snorm_ne_top (f - g))],
  ..add_group_norm.to_normed_add_comm_group
    { to_fun := (norm : Lp E p μ → ℝ),
      map_zero' := norm_zero,
      neg' := by simp,
      add_le' := λ f g, begin
        simp only [norm_def],
        rw ← ennreal.to_real_add (snorm_ne_top f) (snorm_ne_top g),
        suffices h_snorm : snorm ⇑(f + g) p μ ≤ snorm ⇑f p μ + snorm ⇑g p μ,
        { rwa ennreal.to_real_le_to_real (snorm_ne_top (f + g)),
          exact ennreal.add_ne_top.mpr ⟨snorm_ne_top f, snorm_ne_top g⟩, },
        rw [snorm_congr_ae (coe_fn_add _ _)],
        exact snorm_add_le (Lp.ae_strongly_measurable f) (Lp.ae_strongly_measurable g) hp.1,
      end,
      eq_zero_of_map_eq_zero' := λ f, (norm_eq_zero_iff $ zero_lt_one.trans_le hp.1).1 } }

-- check no diamond is created
example [fact (1 ≤ p)] :
  pseudo_emetric_space.to_has_edist = (Lp.has_edist : has_edist (Lp E p μ)) :=
rfl

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 E]

lemma mem_Lp_const_smul (c : 𝕜) (f : Lp E p μ) : c • ↑f ∈ Lp E p μ :=
begin
  rw [mem_Lp_iff_snorm_lt_top, snorm_congr_ae (ae_eq_fun.coe_fn_smul _ _), snorm_const_smul,
    ennreal.mul_lt_top_iff],
  exact or.inl ⟨ennreal.coe_lt_top, f.prop⟩,
end

variables (E p μ 𝕜)

/-- The `𝕜`-submodule of elements of `α →ₘ[μ] E` whose `Lp` norm is finite.  This is `Lp E p μ`,
with extra structure. -/
def Lp_submodule : submodule 𝕜 (α →ₘ[μ] E) :=
{ smul_mem' := λ c f hf, by simpa using mem_Lp_const_smul c ⟨f, hf⟩,
  .. Lp E p μ }

variables {E p μ 𝕜}

lemma coe_Lp_submodule : (Lp_submodule E p μ 𝕜).to_add_subgroup = Lp E p μ := rfl

instance : module 𝕜 (Lp E p μ) :=
{ .. (Lp_submodule E p μ 𝕜).module }

lemma coe_fn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f) =ᵐ[μ] c • f := ae_eq_fun.coe_fn_smul _ _

lemma norm_const_smul (c : 𝕜) (f : Lp E p μ) : ‖c • f‖ = ‖c‖ * ‖f‖ :=
by rw [norm_def, snorm_congr_ae (coe_fn_smul _ _), snorm_const_smul c,
  ennreal.to_real_mul, ennreal.coe_to_real, coe_nnnorm, norm_def]

instance [fact (1 ≤ p)] : normed_space 𝕜 (Lp E p μ) :=
{ norm_smul_le := λ _ _, by simp [norm_const_smul] }

end normed_space

end Lp

namespace mem_ℒp

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 E]

lemma to_Lp_const_smul {f : α → E} (c : 𝕜) (hf : mem_ℒp f p μ) :
  (hf.const_smul c).to_Lp (c • f) = c • hf.to_Lp f := rfl

end mem_ℒp

/-! ### Indicator of a set as an element of Lᵖ

For a set `s` with `(hs : measurable_set s)` and `(hμs : μ s < ∞)`, we build
`indicator_const_Lp p hs hμs c`, the element of `Lp` corresponding to `s.indicator (λ x, c)`.
-/

section indicator

variables {s : set α} {hs : measurable_set s} {c : E} {f : α → E} {hf : ae_strongly_measurable f μ}

lemma snorm_ess_sup_indicator_le (s : set α) (f : α → G) :
  snorm_ess_sup (s.indicator f) μ ≤ snorm_ess_sup f μ :=
begin
  refine ess_sup_mono_ae (eventually_of_forall (λ x, _)),
  rw [ennreal.coe_le_coe, nnnorm_indicator_eq_indicator_nnnorm],
  exact set.indicator_le_self s _ x,
end

lemma snorm_ess_sup_indicator_const_le (s : set α) (c : G) :
  snorm_ess_sup (s.indicator (λ x : α , c)) μ ≤ ‖c‖₊ :=
begin
  by_cases hμ0 : μ = 0,
  { rw [hμ0, snorm_ess_sup_measure_zero],
    exact zero_le _ },
  { exact (snorm_ess_sup_indicator_le s (λ x, c)).trans (snorm_ess_sup_const c hμ0).le, },
end

lemma snorm_ess_sup_indicator_const_eq (s : set α) (c : G) (hμs : μ s ≠ 0) :
  snorm_ess_sup (s.indicator (λ x : α , c)) μ = ‖c‖₊ :=
begin
  refine le_antisymm (snorm_ess_sup_indicator_const_le s c) _,
  by_contra' h,
  have h' := ae_iff.mp (ae_lt_of_ess_sup_lt h),
  push_neg at h',
  refine hμs (measure_mono_null (λ x hx_mem, _) h'),
  rw [set.mem_set_of_eq, set.indicator_of_mem hx_mem],
  exact le_rfl,
end

variables (hs)

lemma snorm_indicator_le {E : Type*} [normed_add_comm_group E] (f : α → E) :
  snorm (s.indicator f) p μ ≤ snorm f p μ :=
begin
  refine snorm_mono_ae (eventually_of_forall (λ x, _)),
  suffices : ‖s.indicator f x‖₊ ≤ ‖f x‖₊,
  { exact nnreal.coe_mono this },
  rw nnnorm_indicator_eq_indicator_nnnorm,
  exact s.indicator_le_self _ x,
end

variables {hs}

lemma snorm_indicator_const {c : G} (hs : measurable_set s) (hp : p ≠ 0) (hp_top : p ≠ ∞) :
  snorm (s.indicator (λ x, c)) p μ = ‖c‖₊ * (μ s) ^ (1 / p.to_real) :=
begin
  have hp_pos : 0 < p.to_real, from ennreal.to_real_pos hp hp_top,
  rw snorm_eq_lintegral_rpow_nnnorm hp hp_top,
  simp_rw [nnnorm_indicator_eq_indicator_nnnorm, ennreal.coe_indicator],
  have h_indicator_pow : (λ a : α, s.indicator (λ (x : α), (‖c‖₊ : ℝ≥0∞)) a ^ p.to_real)
    = s.indicator (λ (x : α), ↑‖c‖₊ ^ p.to_real),
  { rw set.comp_indicator_const (‖c‖₊ : ℝ≥0∞) (λ x, x ^ p.to_real) _,
    simp [hp_pos], },
  rw [h_indicator_pow, lintegral_indicator _ hs, set_lintegral_const, ennreal.mul_rpow_of_nonneg],
  { rw [← ennreal.rpow_mul, mul_one_div_cancel hp_pos.ne.symm, ennreal.rpow_one], },
  { simp [hp_pos.le], },
end

lemma snorm_indicator_const' {c : G} (hs : measurable_set s) (hμs : μ s ≠ 0) (hp : p ≠ 0) :
  snorm (s.indicator (λ _, c)) p μ = ‖c‖₊ * (μ s) ^ (1 / p.to_real) :=
begin
  by_cases hp_top : p = ∞,
  { simp [hp_top, snorm_ess_sup_indicator_const_eq s c hμs], },
  { exact snorm_indicator_const hs hp hp_top, },
end

lemma mem_ℒp.indicator (hs : measurable_set s) (hf : mem_ℒp f p μ) :
  mem_ℒp (s.indicator f) p μ :=
⟨hf.ae_strongly_measurable.indicator hs, lt_of_le_of_lt (snorm_indicator_le f) hf.snorm_lt_top⟩

lemma snorm_ess_sup_indicator_eq_snorm_ess_sup_restrict {f : α → F} (hs : measurable_set s) :
  snorm_ess_sup (s.indicator f) μ = snorm_ess_sup f (μ.restrict s) :=
begin
  simp_rw [snorm_ess_sup, nnnorm_indicator_eq_indicator_nnnorm, ennreal.coe_indicator],
  by_cases hs_null : μ s = 0,
  { rw measure.restrict_zero_set hs_null,
    simp only [ess_sup_measure_zero, ennreal.ess_sup_eq_zero_iff, ennreal.bot_eq_zero],
    have hs_empty : s =ᵐ[μ] (∅ : set α), by { rw ae_eq_set, simpa using hs_null, },
    refine (indicator_ae_eq_of_ae_eq_set hs_empty).trans _,
    rw set.indicator_empty,
    refl, },
  rw ess_sup_indicator_eq_ess_sup_restrict (eventually_of_forall (λ x, _)) hs hs_null,
  rw pi.zero_apply,
  exact zero_le _,
end

lemma snorm_indicator_eq_snorm_restrict {f : α → F} (hs : measurable_set s) :
  snorm (s.indicator f) p μ = snorm f p (μ.restrict s) :=
begin
  by_cases hp_zero : p = 0,
  { simp only [hp_zero, snorm_exponent_zero], },
  by_cases hp_top : p = ∞,
  { simp_rw [hp_top, snorm_exponent_top],
    exact snorm_ess_sup_indicator_eq_snorm_ess_sup_restrict hs, },
  simp_rw snorm_eq_lintegral_rpow_nnnorm hp_zero hp_top,
  suffices : ∫⁻ x, ‖s.indicator f x‖₊ ^ p.to_real ∂μ = ∫⁻ x in s, ‖f x‖₊ ^ p.to_real ∂μ,
    by rw this,
  rw ← lintegral_indicator _ hs,
  congr,
  simp_rw [nnnorm_indicator_eq_indicator_nnnorm, ennreal.coe_indicator],
  have h_zero : (λ x, x ^ p.to_real) (0 : ℝ≥0∞) = 0,
    by simp [ennreal.to_real_pos hp_zero hp_top],
  exact (set.indicator_comp_of_zero h_zero).symm,
end

lemma mem_ℒp_indicator_iff_restrict (hs : measurable_set s) :
  mem_ℒp (s.indicator f) p μ ↔ mem_ℒp f p (μ.restrict s) :=
by simp [mem_ℒp, ae_strongly_measurable_indicator_iff hs, snorm_indicator_eq_snorm_restrict hs]

lemma mem_ℒp_indicator_const (p : ℝ≥0∞) (hs : measurable_set s) (c : E) (hμsc : c = 0 ∨ μ s ≠ ∞) :
  mem_ℒp (s.indicator (λ _, c)) p μ :=
begin
  rw mem_ℒp_indicator_iff_restrict hs,
  by_cases hp_zero : p = 0,
  { rw hp_zero, exact mem_ℒp_zero_iff_ae_strongly_measurable.mpr ae_strongly_measurable_const, },
  by_cases hp_top : p = ∞,
  { rw hp_top,
    exact mem_ℒp_top_of_bound ae_strongly_measurable_const (‖c‖)
      (eventually_of_forall (λ x, le_rfl)), },
  rw [mem_ℒp_const_iff hp_zero hp_top, measure.restrict_apply_univ],
  cases hμsc,
  { exact or.inl hμsc, },
  { exact or.inr hμsc.lt_top, },
end

end indicator

section indicator_const_Lp

open set function

variables {s : set α} {hs : measurable_set s} {hμs : μ s ≠ ∞} {c : E}

/-- Indicator of a set as an element of `Lp`. -/
def indicator_const_Lp (p : ℝ≥0∞) (hs : measurable_set s) (hμs : μ s ≠ ∞) (c : E) : Lp E p μ :=
mem_ℒp.to_Lp (s.indicator (λ _, c)) (mem_ℒp_indicator_const p hs c (or.inr hμs))

lemma indicator_const_Lp_coe_fn : ⇑(indicator_const_Lp p hs hμs c) =ᵐ[μ] s.indicator (λ _, c) :=
mem_ℒp.coe_fn_to_Lp (mem_ℒp_indicator_const p hs c (or.inr hμs))

lemma indicator_const_Lp_coe_fn_mem :
  ∀ᵐ (x : α) ∂μ, x ∈ s → indicator_const_Lp p hs hμs c x = c :=
indicator_const_Lp_coe_fn.mono (λ x hx hxs, hx.trans (set.indicator_of_mem hxs _))

lemma indicator_const_Lp_coe_fn_nmem :
  ∀ᵐ (x : α) ∂μ, x ∉ s → indicator_const_Lp p hs hμs c x = 0 :=
indicator_const_Lp_coe_fn.mono (λ x hx hxs, hx.trans (set.indicator_of_not_mem hxs _))

lemma norm_indicator_const_Lp (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  ‖indicator_const_Lp p hs hμs c‖ = ‖c‖ * (μ s).to_real ^ (1 / p.to_real) :=
by rw [Lp.norm_def, snorm_congr_ae indicator_const_Lp_coe_fn,
    snorm_indicator_const hs hp_ne_zero hp_ne_top, ennreal.to_real_mul, ennreal.to_real_rpow,
    ennreal.coe_to_real, coe_nnnorm]

lemma norm_indicator_const_Lp_top (hμs_ne_zero : μ s ≠ 0) : ‖indicator_const_Lp ∞ hs hμs c‖ = ‖c‖ :=
by rw [Lp.norm_def, snorm_congr_ae indicator_const_Lp_coe_fn,
    snorm_indicator_const' hs hμs_ne_zero ennreal.top_ne_zero, ennreal.top_to_real, div_zero,
    ennreal.rpow_zero, mul_one, ennreal.coe_to_real, coe_nnnorm]

lemma norm_indicator_const_Lp' (hp_pos : p ≠ 0) (hμs_pos : μ s ≠ 0) :
  ‖indicator_const_Lp p hs hμs c‖ = ‖c‖ * (μ s).to_real ^ (1 / p.to_real) :=
begin
  by_cases hp_top : p = ∞,
  { rw [hp_top, ennreal.top_to_real, div_zero, real.rpow_zero, mul_one],
    exact norm_indicator_const_Lp_top hμs_pos, },
  { exact norm_indicator_const_Lp hp_pos hp_top, },
end

@[simp] lemma indicator_const_empty :
  indicator_const_Lp p measurable_set.empty (by simp : μ ∅ ≠ ∞) c = 0 :=
begin
  rw Lp.eq_zero_iff_ae_eq_zero,
  convert indicator_const_Lp_coe_fn,
  simp [set.indicator_empty'],
end

lemma mem_ℒp_add_of_disjoint {f g : α → E}
  (h : disjoint (support f) (support g)) (hf : strongly_measurable f) (hg : strongly_measurable g) :
  mem_ℒp (f + g) p μ ↔ mem_ℒp f p μ ∧ mem_ℒp g p μ :=
begin
  borelize E,
  refine ⟨λ hfg, ⟨_, _⟩, λ h, h.1.add h.2⟩,
  { rw ← indicator_add_eq_left h, exact hfg.indicator (measurable_set_support hf.measurable) },
  { rw ← indicator_add_eq_right h, exact hfg.indicator (measurable_set_support hg.measurable) }
end

/-- The indicator of a disjoint union of two sets is the sum of the indicators of the sets. -/
lemma indicator_const_Lp_disjoint_union {s t : set α} (hs : measurable_set s)
  (ht : measurable_set t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) (c : E) :
  (indicator_const_Lp p (hs.union ht) ((measure_union_le s t).trans_lt
      (lt_top_iff_ne_top.mpr (ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne c)
    = indicator_const_Lp p hs hμs c + indicator_const_Lp p ht hμt c :=
begin
  ext1,
  refine indicator_const_Lp_coe_fn.trans (eventually_eq.trans _ (Lp.coe_fn_add _ _).symm),
  refine eventually_eq.trans _
    (eventually_eq.add indicator_const_Lp_coe_fn.symm indicator_const_Lp_coe_fn.symm),
  rw set.indicator_union_of_disjoint (set.disjoint_iff_inter_eq_empty.mpr hst) _,
end

end indicator_const_Lp

lemma mem_ℒp.norm_rpow_div {f : α → E}
  (hf : mem_ℒp f p μ) (q : ℝ≥0∞) :
  mem_ℒp (λ (x : α), ‖f x‖ ^ q.to_real) (p/q) μ :=
begin
  refine ⟨(hf.1.norm.ae_measurable.pow_const q.to_real).ae_strongly_measurable, _⟩,
  by_cases q_top : q = ∞, { simp [q_top] },
  by_cases q_zero : q = 0,
  { simp [q_zero],
    by_cases p_zero : p = 0, { simp [p_zero] },
    rw ennreal.div_zero p_zero,
    exact (mem_ℒp_top_const (1 : ℝ)).2 },
  rw snorm_norm_rpow _ (ennreal.to_real_pos q_zero q_top),
  apply ennreal.rpow_lt_top_of_nonneg ennreal.to_real_nonneg,
  rw [ennreal.of_real_to_real q_top, div_eq_mul_inv, mul_assoc,
    ennreal.inv_mul_cancel q_zero q_top, mul_one],
  exact hf.2.ne
end

lemma mem_ℒp_norm_rpow_iff {q : ℝ≥0∞} {f : α → E} (hf : ae_strongly_measurable f μ)
  (q_zero : q ≠ 0) (q_top : q ≠ ∞) :
  mem_ℒp (λ (x : α), ‖f x‖ ^ q.to_real) (p/q) μ ↔ mem_ℒp f p μ :=
begin
  refine ⟨λ h, _, λ h, h.norm_rpow_div q⟩,
  apply (mem_ℒp_norm_iff hf).1,
  convert h.norm_rpow_div (q⁻¹),
  { ext x,
    rw [real.norm_eq_abs, real.abs_rpow_of_nonneg (norm_nonneg _), ← real.rpow_mul (abs_nonneg _),
      ennreal.to_real_inv, mul_inv_cancel, abs_of_nonneg (norm_nonneg _), real.rpow_one],
    simp [ennreal.to_real_eq_zero_iff, not_or_distrib, q_zero, q_top] },
  { rw [div_eq_mul_inv, inv_inv, div_eq_mul_inv, mul_assoc, ennreal.inv_mul_cancel q_zero q_top,
    mul_one] }
end

lemma mem_ℒp.norm_rpow {f : α → E}
  (hf : mem_ℒp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  mem_ℒp (λ (x : α), ‖f x‖ ^ p.to_real) 1 μ :=
begin
  convert hf.norm_rpow_div p,
  rw [div_eq_mul_inv, ennreal.mul_inv_cancel hp_ne_zero hp_ne_top],
end

end measure_theory

open measure_theory

/-!
### Composition on `L^p`

We show that Lipschitz functions vanishing at zero act by composition on `L^p`, and specialize
this to the composition with continuous linear maps, and to the definition of the positive
part of an `L^p` function.
-/

section composition

variables {g : E → F} {c : ℝ≥0}

lemma lipschitz_with.comp_mem_ℒp {α E F} {K} [measurable_space α] {μ : measure α}
  [normed_add_comm_group E] [normed_add_comm_group F] {f : α → E} {g : E → F}
  (hg : lipschitz_with K g) (g0 : g 0 = 0) (hL : mem_ℒp f p μ) : mem_ℒp (g ∘ f) p μ  :=
begin
  have : ∀ᵐ x ∂μ, ‖g (f x)‖ ≤ K * ‖f x‖,
  { apply filter.eventually_of_forall (λ x, _),
    rw [← dist_zero_right, ← dist_zero_right, ← g0],
    apply hg.dist_le_mul },
  exact hL.of_le_mul (hg.continuous.comp_ae_strongly_measurable hL.1) this,
end

lemma measure_theory.mem_ℒp.of_comp_antilipschitz_with {α E F} {K'}
  [measurable_space α] {μ : measure α} [normed_add_comm_group E] [normed_add_comm_group F]
  {f : α → E} {g : E → F} (hL : mem_ℒp (g ∘ f) p μ)
  (hg : uniform_continuous g) (hg' : antilipschitz_with K' g) (g0 : g 0 = 0) : mem_ℒp f p μ :=
begin
  have A : ∀ᵐ x ∂μ, ‖f x‖ ≤ K' * ‖g (f x)‖,
  { apply filter.eventually_of_forall (λ x, _),
    rw [← dist_zero_right, ← dist_zero_right, ← g0],
    apply hg'.le_mul_dist },
  have B : ae_strongly_measurable f μ :=
    ((hg'.uniform_embedding hg).embedding.ae_strongly_measurable_comp_iff.1 hL.1),
  exact hL.of_le_mul B A,
end

namespace lipschitz_with

lemma mem_ℒp_comp_iff_of_antilipschitz {α E F} {K K'} [measurable_space α] {μ : measure α}
  [normed_add_comm_group E] [normed_add_comm_group F]
  {f : α → E} {g : E → F} (hg : lipschitz_with K g) (hg' : antilipschitz_with K' g) (g0 : g 0 = 0) :
  mem_ℒp (g ∘ f) p μ ↔ mem_ℒp f p μ :=
⟨λ h, h.of_comp_antilipschitz_with hg.uniform_continuous hg' g0, λ h, hg.comp_mem_ℒp g0 h⟩

/-- When `g` is a Lipschitz function sending `0` to `0` and `f` is in `Lp`, then `g ∘ f` is well
defined as an element of `Lp`. -/
def comp_Lp (hg : lipschitz_with c g) (g0 : g 0 = 0) (f : Lp E p μ) : Lp F p μ :=
⟨ae_eq_fun.comp g hg.continuous (f : α →ₘ[μ] E),
begin
  suffices : ∀ᵐ x ∂μ, ‖ae_eq_fun.comp g hg.continuous (f : α →ₘ[μ] E) x‖ ≤ c * ‖f x‖,
  { exact Lp.mem_Lp_of_ae_le_mul this },
  filter_upwards [ae_eq_fun.coe_fn_comp g hg.continuous (f : α →ₘ[μ] E)] with a ha,
  simp only [ha],
  rw [← dist_zero_right, ← dist_zero_right, ← g0],
  exact hg.dist_le_mul (f a) 0,
end⟩

lemma coe_fn_comp_Lp (hg : lipschitz_with c g) (g0 : g 0 = 0) (f : Lp E p μ) :
  hg.comp_Lp g0 f =ᵐ[μ] g ∘ f :=
ae_eq_fun.coe_fn_comp _ _ _

@[simp] lemma comp_Lp_zero (hg : lipschitz_with c g) (g0 : g 0 = 0) :
  hg.comp_Lp g0 (0 : Lp E p μ) = 0 :=
begin
  rw Lp.eq_zero_iff_ae_eq_zero,
  apply (coe_fn_comp_Lp _ _ _).trans,
  filter_upwards [Lp.coe_fn_zero E p μ] with _ ha,
  simp [ha, g0],
end

lemma norm_comp_Lp_sub_le (hg : lipschitz_with c g) (g0 : g 0 = 0) (f f' : Lp E p μ) :
  ‖hg.comp_Lp g0 f - hg.comp_Lp g0 f'‖ ≤ c * ‖f - f'‖ :=
begin
  apply Lp.norm_le_mul_norm_of_ae_le_mul,
  filter_upwards [hg.coe_fn_comp_Lp g0 f, hg.coe_fn_comp_Lp g0 f',
    Lp.coe_fn_sub (hg.comp_Lp g0 f) (hg.comp_Lp g0 f'), Lp.coe_fn_sub f f'] with a ha1 ha2 ha3 ha4,
  simp [ha1, ha2, ha3, ha4, ← dist_eq_norm],
  exact hg.dist_le_mul (f a) (f' a)
end

lemma norm_comp_Lp_le (hg : lipschitz_with c g) (g0 : g 0 = 0) (f : Lp E p μ) :
  ‖hg.comp_Lp g0 f‖ ≤ c * ‖f‖ :=
by simpa using hg.norm_comp_Lp_sub_le g0 f 0

lemma lipschitz_with_comp_Lp [fact (1 ≤ p)] (hg : lipschitz_with c g) (g0 : g 0 = 0) :
  lipschitz_with c (hg.comp_Lp g0 : Lp E p μ → Lp F p μ) :=
lipschitz_with.of_dist_le_mul $ λ f g, by simp [dist_eq_norm, norm_comp_Lp_sub_le]

lemma continuous_comp_Lp [fact (1 ≤ p)] (hg : lipschitz_with c g) (g0 : g 0 = 0) :
  continuous (hg.comp_Lp g0 : Lp E p μ → Lp F p μ) :=
(lipschitz_with_comp_Lp hg g0).continuous

end lipschitz_with

namespace continuous_linear_map
variables {𝕜 : Type*} [nontrivially_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]

/-- Composing `f : Lp ` with `L : E →L[𝕜] F`. -/
def comp_Lp (L : E →L[𝕜] F) (f : Lp E p μ) : Lp F p μ :=
L.lipschitz.comp_Lp (map_zero L) f

lemma coe_fn_comp_Lp (L : E →L[𝕜] F) (f : Lp E p μ) :
  ∀ᵐ a ∂μ, (L.comp_Lp f) a = L (f a) :=
lipschitz_with.coe_fn_comp_Lp _ _ _

lemma coe_fn_comp_Lp' (L : E →L[𝕜] F) (f : Lp E p μ) :
  L.comp_Lp f =ᵐ[μ] λ a, L (f a) :=
L.coe_fn_comp_Lp f

lemma comp_mem_ℒp (L : E →L[𝕜] F) (f : Lp E p μ) : mem_ℒp (L ∘ f) p μ :=
(Lp.mem_ℒp (L.comp_Lp f)).ae_eq (L.coe_fn_comp_Lp' f)

lemma comp_mem_ℒp' (L : E →L[𝕜] F) {f : α → E} (hf : mem_ℒp f p μ) : mem_ℒp (L ∘ f) p μ :=
(L.comp_mem_ℒp (hf.to_Lp f)).ae_eq (eventually_eq.fun_comp (hf.coe_fn_to_Lp) _)

section is_R_or_C

variables {K : Type*} [is_R_or_C K]

lemma _root_.measure_theory.mem_ℒp.of_real
  {f : α → ℝ} (hf : mem_ℒp f p μ) : mem_ℒp (λ x, (f x : K)) p μ :=
(@is_R_or_C.of_real_clm K _).comp_mem_ℒp' hf

lemma _root_.measure_theory.mem_ℒp_re_im_iff {f : α → K} :
  mem_ℒp (λ x, is_R_or_C.re (f x)) p μ ∧ mem_ℒp (λ x, is_R_or_C.im (f x)) p μ ↔
  mem_ℒp f p μ :=
begin
  refine ⟨_, λ hf, ⟨hf.re, hf.im⟩⟩,
  rintro ⟨hre, him⟩,
  convert hre.of_real.add (him.of_real.const_mul is_R_or_C.I),
  { ext1 x,
    rw [pi.add_apply, mul_comm, is_R_or_C.re_add_im] },
  all_goals { apply_instance }
end

end is_R_or_C

lemma add_comp_Lp (L L' : E →L[𝕜] F) (f : Lp E p μ) :
  (L + L').comp_Lp f = L.comp_Lp f + L'.comp_Lp f :=
begin
  ext1,
  refine (coe_fn_comp_Lp' (L + L') f).trans _,
  refine eventually_eq.trans _ (Lp.coe_fn_add _ _).symm,
  refine eventually_eq.trans _
    (eventually_eq.add (L.coe_fn_comp_Lp' f).symm (L'.coe_fn_comp_Lp' f).symm),
  refine eventually_of_forall (λ x, _),
  refl,
end

lemma smul_comp_Lp {𝕜'} [normed_field 𝕜'] [normed_space 𝕜' F] [smul_comm_class 𝕜 𝕜' F]
  (c : 𝕜') (L : E →L[𝕜] F) (f : Lp E p μ) :
  (c • L).comp_Lp f = c • L.comp_Lp f :=
begin
  ext1,
  refine (coe_fn_comp_Lp' (c • L) f).trans _,
  refine eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm,
  refine (L.coe_fn_comp_Lp' f).mono (λ x hx, _),
  rw [pi.smul_apply, hx],
  refl,
end

lemma norm_comp_Lp_le (L : E →L[𝕜] F) (f : Lp E p μ)  : ‖L.comp_Lp f‖ ≤ ‖L‖ * ‖f‖ :=
lipschitz_with.norm_comp_Lp_le _ _ _

variables (μ p)

/-- Composing `f : Lp E p μ` with `L : E →L[𝕜] F`, seen as a `𝕜`-linear map on `Lp E p μ`. -/
def comp_Lpₗ (L : E →L[𝕜] F) : (Lp E p μ) →ₗ[𝕜] (Lp F p μ) :=
{ to_fun := λ f, L.comp_Lp f,
  map_add' := begin
    intros f g,
    ext1,
    filter_upwards [Lp.coe_fn_add f g, coe_fn_comp_Lp L (f + g), coe_fn_comp_Lp L f,
      coe_fn_comp_Lp L g, Lp.coe_fn_add (L.comp_Lp f) (L.comp_Lp g)],
    assume a ha1 ha2 ha3 ha4 ha5,
    simp only [ha1, ha2, ha3, ha4, ha5, map_add, pi.add_apply],
  end,
  map_smul' := begin
    intros c f,
    dsimp,
    ext1,
    filter_upwards [Lp.coe_fn_smul c f, coe_fn_comp_Lp L (c • f), Lp.coe_fn_smul c (L.comp_Lp f),
      coe_fn_comp_Lp L f] with _ ha1 ha2 ha3 ha4,
    simp only [ha1, ha2, ha3, ha4, smul_hom_class.map_smul, pi.smul_apply],
  end }

/-- Composing `f : Lp E p μ` with `L : E →L[𝕜] F`, seen as a continuous `𝕜`-linear map on
`Lp E p μ`. See also the similar
* `linear_map.comp_left` for functions,
* `continuous_linear_map.comp_left_continuous` for continuous functions,
* `continuous_linear_map.comp_left_continuous_bounded` for bounded continuous functions,
* `continuous_linear_map.comp_left_continuous_compact` for continuous functions on compact spaces.
-/
def comp_LpL [fact (1 ≤ p)] (L : E →L[𝕜] F) : (Lp E p μ) →L[𝕜] (Lp F p μ) :=
linear_map.mk_continuous (L.comp_Lpₗ p μ) ‖L‖ L.norm_comp_Lp_le

variables {μ p}

lemma coe_fn_comp_LpL [fact (1 ≤ p)] (L : E →L[𝕜] F) (f : Lp E p μ) :
  L.comp_LpL p μ f =ᵐ[μ] λ a, L (f a) :=
L.coe_fn_comp_Lp f

lemma add_comp_LpL [fact (1 ≤ p)] (L L' : E →L[𝕜] F) :
  (L + L').comp_LpL p μ = L.comp_LpL p μ + L'.comp_LpL p μ :=
by { ext1 f, exact add_comp_Lp L L' f }

lemma smul_comp_LpL [fact (1 ≤ p)] (c : 𝕜) (L : E →L[𝕜] F) :
  (c • L).comp_LpL p μ  = c • (L.comp_LpL p μ) :=
by { ext1 f, exact smul_comp_Lp c L f }

/-- TODO: written in an "apply" way because of a missing `has_smul` instance. -/
lemma smul_comp_LpL_apply [fact (1 ≤ p)] {𝕜'} [normed_field 𝕜'] [normed_space 𝕜' F]
  [smul_comm_class 𝕜 𝕜' F] (c : 𝕜') (L : E →L[𝕜] F) (f : Lp E p μ) :
  (c • L).comp_LpL p μ f = c • (L.comp_LpL p μ f) :=
smul_comp_Lp c L f

lemma norm_compLpL_le [fact (1 ≤ p)] (L : E →L[𝕜] F) :
  ‖L.comp_LpL p μ‖ ≤ ‖L‖ :=
linear_map.mk_continuous_norm_le _ (norm_nonneg _) _

end continuous_linear_map

namespace measure_theory

lemma indicator_const_Lp_eq_to_span_singleton_comp_Lp {s : set α} [normed_space ℝ F]
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : F) :
  indicator_const_Lp 2 hs hμs x =
    (continuous_linear_map.to_span_singleton ℝ x).comp_Lp (indicator_const_Lp 2 hs hμs (1 : ℝ)) :=
begin
  ext1,
  refine indicator_const_Lp_coe_fn.trans _,
  have h_comp_Lp := (continuous_linear_map.to_span_singleton ℝ x).coe_fn_comp_Lp
    (indicator_const_Lp 2 hs hμs (1 : ℝ)),
  rw ← eventually_eq at h_comp_Lp,
  refine eventually_eq.trans _ h_comp_Lp.symm,
  refine (@indicator_const_Lp_coe_fn _ _ _ 2 μ _ s hs hμs (1 : ℝ)).mono (λ y hy, _),
  dsimp only,
  rw hy,
  simp_rw [continuous_linear_map.to_span_singleton_apply],
  by_cases hy_mem : y ∈ s; simp [hy_mem, continuous_linear_map.lsmul_apply],
end

namespace Lp
section pos_part

lemma lipschitz_with_pos_part : lipschitz_with 1 (λ (x : ℝ), max x 0) :=
lipschitz_with.of_dist_le_mul $ λ x y, by simp [real.dist_eq, abs_max_sub_max_le_abs]

lemma _root_.measure_theory.mem_ℒp.pos_part {f : α → ℝ} (hf : mem_ℒp f p μ) :
  mem_ℒp (λ x, max (f x) 0) p μ :=
lipschitz_with_pos_part.comp_mem_ℒp  (max_eq_right le_rfl) hf

lemma _root_.measure_theory.mem_ℒp.neg_part {f : α → ℝ} (hf : mem_ℒp f p μ) :
  mem_ℒp (λ x, max (-f x) 0) p μ :=
lipschitz_with_pos_part.comp_mem_ℒp (max_eq_right le_rfl) hf.neg

/-- Positive part of a function in `L^p`. -/
def pos_part (f : Lp ℝ p μ) : Lp ℝ p μ :=
lipschitz_with_pos_part.comp_Lp (max_eq_right le_rfl) f

/-- Negative part of a function in `L^p`. -/
def neg_part (f : Lp ℝ p μ) : Lp ℝ p μ := pos_part (-f)

@[norm_cast]
lemma coe_pos_part (f : Lp ℝ p μ) : (pos_part f : α →ₘ[μ] ℝ) = (f : α →ₘ[μ] ℝ).pos_part := rfl

lemma coe_fn_pos_part (f : Lp ℝ p μ) : ⇑(pos_part f) =ᵐ[μ] λ a, max (f a) 0 :=
ae_eq_fun.coe_fn_pos_part _

lemma coe_fn_neg_part_eq_max (f : Lp ℝ p μ) : ∀ᵐ a ∂μ, neg_part f a = max (- f a) 0 :=
begin
  rw neg_part,
  filter_upwards [coe_fn_pos_part (-f), coe_fn_neg f] with _ h₁ h₂,
  rw [h₁, h₂, pi.neg_apply],
end

lemma coe_fn_neg_part (f : Lp ℝ p μ) : ∀ᵐ a ∂μ, neg_part f a = - min (f a) 0 :=
(coe_fn_neg_part_eq_max f).mono $ assume a h,
by rw [h, ← max_neg_neg, neg_zero]

lemma continuous_pos_part [fact (1 ≤ p)] : continuous (λf : Lp ℝ p μ, pos_part f) :=
lipschitz_with.continuous_comp_Lp _ _

lemma continuous_neg_part [fact (1 ≤ p)] : continuous (λf : Lp ℝ p μ, neg_part f) :=
have eq : (λf : Lp ℝ p μ, neg_part f) = (λf : Lp ℝ p μ, pos_part (-f)) := rfl,
by { rw eq, exact continuous_pos_part.comp continuous_neg }

end pos_part
end Lp
end measure_theory

end composition



/-!
## `L^p` is a complete space

We show that `L^p` is a complete space for `1 ≤ p`.
-/

section complete_space

namespace measure_theory
namespace Lp

lemma snorm'_lim_eq_lintegral_liminf {ι} [nonempty ι] [linear_order ι] {f : ι → α → G} {p : ℝ}
  (hp_nonneg : 0 ≤ p) {f_lim : α → G}
  (h_lim : ∀ᵐ (x : α) ∂μ, tendsto (λ n, f n x) at_top (𝓝 (f_lim x))) :
  snorm' f_lim p μ = (∫⁻ a, at_top.liminf (λ m, (‖f m a‖₊ : ℝ≥0∞)^p) ∂μ) ^ (1/p) :=
begin
  suffices h_no_pow : (∫⁻ a, ‖f_lim a‖₊ ^ p ∂μ)
    = (∫⁻ a, at_top.liminf (λ m, (‖f m a‖₊ : ℝ≥0∞)^p) ∂μ),
  { rw [snorm', h_no_pow], },
  refine lintegral_congr_ae (h_lim.mono (λ a ha, _)),
  rw tendsto.liminf_eq,
  simp_rw [ennreal.coe_rpow_of_nonneg _ hp_nonneg, ennreal.tendsto_coe],
  refine ((nnreal.continuous_rpow_const hp_nonneg).tendsto (‖f_lim a‖₊)).comp _,
  exact (continuous_nnnorm.tendsto (f_lim a)).comp ha,
end

lemma snorm'_lim_le_liminf_snorm' {E} [normed_add_comm_group E] {f : ℕ → α → E} {p : ℝ}
  (hp_pos : 0 < p) (hf : ∀ n, ae_strongly_measurable (f n) μ) {f_lim : α → E}
  (h_lim : ∀ᵐ (x : α) ∂μ, tendsto (λ n, f n x) at_top (𝓝 (f_lim x)))  :
  snorm' f_lim p μ ≤ at_top.liminf (λ n, snorm' (f n) p μ) :=
begin
  rw snorm'_lim_eq_lintegral_liminf hp_pos.le h_lim,
  rw [←ennreal.le_rpow_one_div_iff (by simp [hp_pos] : 0 < 1 / p), one_div_one_div],
  refine (lintegral_liminf_le' (λ m, ((hf m).ennnorm.pow_const _))).trans_eq _,
  have h_pow_liminf : at_top.liminf (λ n, snorm' (f n) p μ) ^ p
    = at_top.liminf (λ n, (snorm' (f n) p μ) ^ p),
  { have h_rpow_mono := ennreal.strict_mono_rpow_of_pos hp_pos,
    have h_rpow_surj := (ennreal.rpow_left_bijective hp_pos.ne.symm).2,
    refine (h_rpow_mono.order_iso_of_surjective _ h_rpow_surj).liminf_apply _ _ _ _,
    all_goals { is_bounded_default }, },
  rw h_pow_liminf,
  simp_rw [snorm', ← ennreal.rpow_mul, one_div, inv_mul_cancel hp_pos.ne.symm, ennreal.rpow_one],
end

lemma snorm_exponent_top_lim_eq_ess_sup_liminf {ι} [nonempty ι] [linear_order ι] {f : ι → α → G}
  {f_lim : α → G}
  (h_lim : ∀ᵐ (x : α) ∂μ, tendsto (λ n, f n x) at_top (𝓝 (f_lim x))) :
  snorm f_lim ∞ μ = ess_sup (λ x, at_top.liminf (λ m, (‖f m x‖₊ : ℝ≥0∞))) μ :=
begin
  rw [snorm_exponent_top, snorm_ess_sup],
  refine ess_sup_congr_ae (h_lim.mono (λ x hx, _)),
  rw tendsto.liminf_eq,
  rw ennreal.tendsto_coe,
  exact (continuous_nnnorm.tendsto (f_lim x)).comp hx,
end

lemma snorm_exponent_top_lim_le_liminf_snorm_exponent_top {ι} [nonempty ι] [countable ι]
  [linear_order ι] {f : ι → α → F} {f_lim : α → F}
  (h_lim : ∀ᵐ (x : α) ∂μ, tendsto (λ n, f n x) at_top (𝓝 (f_lim x))) :
  snorm f_lim ∞ μ ≤ at_top.liminf (λ n, snorm (f n) ∞ μ) :=
begin
  rw snorm_exponent_top_lim_eq_ess_sup_liminf h_lim,
  simp_rw [snorm_exponent_top, snorm_ess_sup],
  exact ennreal.ess_sup_liminf_le (λ n, (λ x, (‖f n x‖₊ : ℝ≥0∞))),
end

lemma snorm_lim_le_liminf_snorm {E} [normed_add_comm_group E]
  {f : ℕ → α → E} (hf : ∀ n, ae_strongly_measurable (f n) μ) (f_lim : α → E)
  (h_lim : ∀ᵐ (x : α) ∂μ, tendsto (λ n, f n x) at_top (𝓝 (f_lim x))) :
  snorm f_lim p μ ≤ at_top.liminf (λ n, snorm (f n) p μ) :=
begin
  by_cases hp0 : p = 0,
  { simp [hp0], },
  rw ← ne.def at hp0,
  by_cases hp_top : p = ∞,
  { simp_rw [hp_top],
    exact snorm_exponent_top_lim_le_liminf_snorm_exponent_top h_lim, },
  simp_rw snorm_eq_snorm' hp0 hp_top,
  have hp_pos : 0 < p.to_real, from ennreal.to_real_pos hp0 hp_top,
  exact snorm'_lim_le_liminf_snorm' hp_pos hf h_lim,
end

/-! ### `Lp` is complete iff Cauchy sequences of `ℒp` have limits in `ℒp` -/

lemma tendsto_Lp_iff_tendsto_ℒp' {ι} {fi : filter ι} [fact (1 ≤ p)]
  (f : ι → Lp E p μ) (f_lim : Lp E p μ) :
  fi.tendsto f (𝓝 f_lim) ↔ fi.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0) :=
begin
  rw tendsto_iff_dist_tendsto_zero,
  simp_rw dist_def,
  rw [← ennreal.zero_to_real, ennreal.tendsto_to_real_iff (λ n, _) ennreal.zero_ne_top],
  rw snorm_congr_ae (Lp.coe_fn_sub _ _).symm,
  exact Lp.snorm_ne_top _,
end

lemma tendsto_Lp_iff_tendsto_ℒp {ι} {fi : filter ι} [fact (1 ≤ p)]
  (f : ι → Lp E p μ) (f_lim : α → E) (f_lim_ℒp : mem_ℒp f_lim p μ) :
  fi.tendsto f (𝓝 (f_lim_ℒp.to_Lp f_lim)) ↔ fi.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0) :=
begin
  rw tendsto_Lp_iff_tendsto_ℒp',
  suffices h_eq : (λ n, snorm (f n - mem_ℒp.to_Lp f_lim f_lim_ℒp) p μ)
      = (λ n, snorm (f n - f_lim) p μ),
    by rw h_eq,
  exact funext (λ n, snorm_congr_ae (eventually_eq.rfl.sub (mem_ℒp.coe_fn_to_Lp f_lim_ℒp))),
end

lemma tendsto_Lp_iff_tendsto_ℒp'' {ι} {fi : filter ι} [fact (1 ≤ p)]
  (f : ι → α → E) (f_ℒp : ∀ n, mem_ℒp (f n) p μ) (f_lim : α → E) (f_lim_ℒp : mem_ℒp f_lim p μ) :
  fi.tendsto (λ n, (f_ℒp n).to_Lp (f n)) (𝓝 (f_lim_ℒp.to_Lp f_lim))
    ↔ fi.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0) :=
begin
  convert Lp.tendsto_Lp_iff_tendsto_ℒp' _ _,
  ext1 n,
  apply snorm_congr_ae,
  filter_upwards [((f_ℒp n).sub f_lim_ℒp).coe_fn_to_Lp,
    Lp.coe_fn_sub ((f_ℒp n).to_Lp (f n)) (f_lim_ℒp.to_Lp f_lim)] with _ hx₁ hx₂,
  rw ← hx₂,
  exact hx₁.symm,
end

lemma tendsto_Lp_of_tendsto_ℒp {ι} {fi : filter ι} [hp : fact (1 ≤ p)]
  {f : ι → Lp E p μ} (f_lim : α → E) (f_lim_ℒp : mem_ℒp f_lim p μ)
  (h_tendsto : fi.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0)) :
  fi.tendsto f (𝓝 (f_lim_ℒp.to_Lp f_lim)) :=
(tendsto_Lp_iff_tendsto_ℒp f f_lim f_lim_ℒp).mpr h_tendsto

lemma cauchy_seq_Lp_iff_cauchy_seq_ℒp {ι} [nonempty ι] [semilattice_sup ι] [hp : fact (1 ≤ p)]
  (f : ι → Lp E p μ) :
  cauchy_seq f ↔ tendsto (λ (n : ι × ι), snorm (f n.fst - f n.snd) p μ) at_top (𝓝 0) :=
begin
  simp_rw [cauchy_seq_iff_tendsto_dist_at_top_0, dist_def],
  rw [← ennreal.zero_to_real, ennreal.tendsto_to_real_iff (λ n, _) ennreal.zero_ne_top],
  rw snorm_congr_ae (Lp.coe_fn_sub _ _).symm,
  exact snorm_ne_top _,
end

lemma complete_space_Lp_of_cauchy_complete_ℒp [hp : fact (1 ≤ p)]
  (H : ∀ (f : ℕ → α → E) (hf : ∀ n, mem_ℒp (f n) p μ) (B : ℕ → ℝ≥0∞) (hB : ∑' i, B i < ∞)
      (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N),
    ∃ (f_lim : α → E) (hf_lim_meas : mem_ℒp f_lim p μ),
      at_top.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0)) :
  complete_space (Lp E p μ) :=
begin
  let B := λ n : ℕ, ((1:ℝ) / 2) ^ n,
  have hB_pos : ∀ n, 0 < B n, from λ n, pow_pos (div_pos zero_lt_one zero_lt_two) n,
  refine metric.complete_of_convergent_controlled_sequences B hB_pos (λ f hf, _),
  rsuffices ⟨f_lim, hf_lim_meas, h_tendsto⟩ : ∃ (f_lim : α → E) (hf_lim_meas : mem_ℒp f_lim p μ),
    at_top.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0),
  { exact ⟨hf_lim_meas.to_Lp f_lim, tendsto_Lp_of_tendsto_ℒp f_lim hf_lim_meas h_tendsto⟩, },
  have hB : summable B, from summable_geometric_two,
  cases hB with M hB,
  let B1 := λ n, ennreal.of_real (B n),
  have hB1_has : has_sum B1 (ennreal.of_real M),
  { have h_tsum_B1 : ∑' i, B1 i = (ennreal.of_real M),
    { change (∑' (n : ℕ), ennreal.of_real (B n)) = ennreal.of_real M,
      rw ←hB.tsum_eq,
      exact (ennreal.of_real_tsum_of_nonneg (λ n, le_of_lt (hB_pos n)) hB.summable).symm, },
    have h_sum := (@ennreal.summable _ B1).has_sum,
    rwa h_tsum_B1 at h_sum, },
  have hB1 : ∑' i, B1 i < ∞, by {rw hB1_has.tsum_eq, exact ennreal.of_real_lt_top, },
  let f1 : ℕ → α → E := λ n, f n,
  refine H f1 (λ n, Lp.mem_ℒp (f n)) B1 hB1 (λ N n m hn hm, _),
  specialize hf N n m hn hm,
  rw dist_def at hf,
  simp_rw [f1, B1],
  rwa ennreal.lt_of_real_iff_to_real_lt,
  rw snorm_congr_ae (Lp.coe_fn_sub _ _).symm,
  exact Lp.snorm_ne_top _,
end

/-! ### Prove that controlled Cauchy sequences of `ℒp` have limits in `ℒp` -/

private lemma snorm'_sum_norm_sub_le_tsum_of_cauchy_snorm' {f : ℕ → α → E}
  (hf : ∀ n, ae_strongly_measurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p)
  {B : ℕ → ℝ≥0∞} (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm' (f n - f m) p μ < B N) (n : ℕ) :
  snorm' (λ x, ∑ i in finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i :=
begin
  let f_norm_diff := λ i x, ‖f (i + 1) x - f i x‖,
  have hgf_norm_diff : ∀ n, (λ x, ∑ i in finset.range (n + 1), ‖f (i + 1) x - f i x‖)
      = ∑ i in finset.range (n + 1), f_norm_diff i,
    from λ n, funext (λ x, by simp [f_norm_diff]),
  rw hgf_norm_diff,
  refine (snorm'_sum_le (λ i _, ((hf (i+1)).sub (hf i)).norm) hp1).trans _,
  simp_rw [←pi.sub_apply, snorm'_norm],
  refine (finset.sum_le_sum _).trans (sum_le_tsum _ (λ m _, zero_le _) ennreal.summable),
  exact λ m _, (h_cau m (m + 1) m (nat.le_succ m) (le_refl m)).le,
end

private lemma lintegral_rpow_sum_coe_nnnorm_sub_le_rpow_tsum {f : ℕ → α → E}
  (hf : ∀ n, ae_strongly_measurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (n : ℕ)
  (hn : snorm' (λ x, ∑ i in finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i) :
  ∫⁻ a, (∑ i in finset.range (n + 1), ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)^p ∂μ
    ≤ (∑' i, B i) ^ p :=
begin
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1,
  rw [←one_div_one_div p, @ennreal.le_rpow_one_div_iff _ _ (1/p) (by simp [hp_pos]),
    one_div_one_div p],
  simp_rw snorm' at hn,
  have h_nnnorm_nonneg :
    (λ a, (‖∑ i in finset.range (n + 1), ‖f (i + 1) a - f i a‖‖₊ : ℝ≥0∞) ^ p)
    = λ a, (∑ i in finset.range (n + 1), (‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)) ^ p,
  { ext1 a,
    congr,
    simp_rw ←of_real_norm_eq_coe_nnnorm,
    rw ←ennreal.of_real_sum_of_nonneg,
    { rw real.norm_of_nonneg _,
      exact finset.sum_nonneg (λ x hx, norm_nonneg _), },
    { exact λ x hx, norm_nonneg _, }, },
  change (∫⁻ a, (λ x, ↑‖∑ i in finset.range (n + 1), ‖f (i+1) x - f i x‖‖₊^p) a ∂μ)^(1/p)
    ≤ ∑' i, B i at hn,
  rwa h_nnnorm_nonneg at hn,
end

private lemma lintegral_rpow_tsum_coe_nnnorm_sub_le_tsum {f : ℕ → α → E}
  (hf : ∀ n, ae_strongly_measurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞}
  (h : ∀ n, ∫⁻ a, (∑ i in finset.range (n + 1), ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)^p ∂μ
    ≤ (∑' i, B i) ^ p) :
  (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)^p ∂μ) ^ (1/p) ≤ ∑' i, B i :=
begin
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1,
  suffices h_pow : ∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)^p ∂μ ≤ (∑' i, B i) ^ p,
    by rwa [←ennreal.le_rpow_one_div_iff (by simp [hp_pos] : 0 < 1 / p), one_div_one_div],
  have h_tsum_1 : ∀ g : ℕ → ℝ≥0∞,
      ∑' i, g i = at_top.liminf (λ n, ∑ i in finset.range (n + 1), g i),
    by { intro g, rw [ennreal.tsum_eq_liminf_sum_nat, ← liminf_nat_add _ 1], },
  simp_rw h_tsum_1 _,
  rw ← h_tsum_1,
  have h_liminf_pow : ∫⁻ a, at_top.liminf (λ n, ∑ i in finset.range (n + 1),
      (‖f (i + 1) a - f i a‖₊))^p ∂μ
    = ∫⁻ a, at_top.liminf (λ n, (∑ i in finset.range (n + 1), (‖f (i + 1) a - f i a‖₊))^p) ∂μ,
  { refine lintegral_congr (λ x, _),
    have h_rpow_mono := ennreal.strict_mono_rpow_of_pos (zero_lt_one.trans_le hp1),
    have h_rpow_surj := (ennreal.rpow_left_bijective hp_pos.ne.symm).2,
    refine (h_rpow_mono.order_iso_of_surjective _ h_rpow_surj).liminf_apply _ _ _ _,
    all_goals { is_bounded_default }, },
  rw h_liminf_pow,
  refine (lintegral_liminf_le' _).trans _,
  { exact λ n, (finset.ae_measurable_sum (finset.range (n+1))
      (λ i _, ((hf (i+1)).sub (hf i)).ennnorm)).pow_const _, },
  { exact liminf_le_of_frequently_le' (frequently_of_forall h), },
end

private lemma tsum_nnnorm_sub_ae_lt_top
  {f : ℕ → α → E} (hf : ∀ n, ae_strongly_measurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞}
  (hB : ∑' i, B i ≠ ∞)
  (h : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)^p ∂μ) ^ (1/p) ≤ ∑' i, B i) :
  ∀ᵐ x ∂μ, (∑' i, ‖f (i + 1) x - f i x‖₊ : ℝ≥0∞) < ∞ :=
begin
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1,
  have h_integral : ∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)^p ∂μ < ∞,
  { have h_tsum_lt_top : (∑' i, B i) ^ p < ∞,
      from ennreal.rpow_lt_top_of_nonneg hp_pos.le hB,
    refine lt_of_le_of_lt _ h_tsum_lt_top,
    rwa [←ennreal.le_rpow_one_div_iff (by simp [hp_pos] : 0 < 1 / p), one_div_one_div] at h, },
  have rpow_ae_lt_top : ∀ᵐ x ∂μ, (∑' i, ‖f (i + 1) x - f i x‖₊ : ℝ≥0∞)^p < ∞,
  { refine ae_lt_top' (ae_measurable.pow_const _ _) h_integral.ne,
    exact ae_measurable.ennreal_tsum (λ n, ((hf (n+1)).sub (hf n)).ennnorm), },
  refine rpow_ae_lt_top.mono (λ x hx, _),
  rwa [←ennreal.lt_rpow_one_div_iff hp_pos,
    ennreal.top_rpow_of_pos (by simp [hp_pos] : 0 < 1 / p)] at hx,
end

lemma ae_tendsto_of_cauchy_snorm' [complete_space E] {f : ℕ → α → E} {p : ℝ}
  (hf : ∀ n, ae_strongly_measurable (f n) μ) (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
  (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm' (f n - f m) p μ < B N) :
  ∀ᵐ x ∂μ, ∃ l : E, at_top.tendsto (λ n, f n x) (𝓝 l) :=
begin
  have h_summable : ∀ᵐ x ∂μ, summable (λ (i : ℕ), f (i + 1) x - f i x),
  { have h1 : ∀ n, snorm' (λ x, ∑ i in finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ
        ≤ ∑' i, B i,
      from snorm'_sum_norm_sub_le_tsum_of_cauchy_snorm' hf hp1 h_cau,
    have h2 : ∀ n, ∫⁻ a, (∑ i in finset.range (n + 1), ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)^p ∂μ
        ≤ (∑' i, B i) ^ p,
      from λ n, lintegral_rpow_sum_coe_nnnorm_sub_le_rpow_tsum hf hp1 n (h1 n),
    have h3 : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)^p ∂μ) ^ (1/p) ≤ ∑' i, B i,
      from lintegral_rpow_tsum_coe_nnnorm_sub_le_tsum hf hp1 h2,
    have h4 : ∀ᵐ x ∂μ, (∑' i, ‖f (i + 1) x - f i x‖₊ : ℝ≥0∞) < ∞,
      from tsum_nnnorm_sub_ae_lt_top hf hp1 hB h3,
    exact h4.mono (λ x hx, summable_of_summable_nnnorm
      (ennreal.tsum_coe_ne_top_iff_summable.mp (lt_top_iff_ne_top.mp hx))), },
  have h : ∀ᵐ x ∂μ, ∃ l : E,
    at_top.tendsto (λ n, ∑ i in finset.range n, (f (i + 1) x - f i x)) (𝓝 l),
  { refine h_summable.mono (λ x hx, _),
    let hx_sum := hx.has_sum.tendsto_sum_nat,
    exact ⟨∑' i, (f (i + 1) x - f i x), hx_sum⟩, },
  refine h.mono (λ x hx, _),
  cases hx with l hx,
  have h_rw_sum : (λ n, ∑ i in finset.range n, (f (i + 1) x - f i x)) = λ n, f n x - f 0 x,
  { ext1 n,
    change ∑ (i : ℕ) in finset.range n, ((λ m, f m x) (i + 1) - (λ m, f m x) i) = f n x - f 0 x,
    rw finset.sum_range_sub, },
  rw h_rw_sum at hx,
  have hf_rw : (λ n, f n x) = λ n, f n x - f 0 x + f 0 x, by { ext1 n, abel, },
  rw hf_rw,
  exact ⟨l + f 0 x, tendsto.add_const _ hx⟩,
end

lemma ae_tendsto_of_cauchy_snorm [complete_space E] {f : ℕ → α → E}
  (hf : ∀ n, ae_strongly_measurable (f n) μ) (hp : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
  (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N) :
  ∀ᵐ x ∂μ, ∃ l : E, at_top.tendsto (λ n, f n x) (𝓝 l) :=
begin
  by_cases hp_top : p = ∞,
  { simp_rw [hp_top] at *,
    have h_cau_ae : ∀ᵐ x ∂μ, ∀ N n m, N ≤ n → N ≤ m → (‖(f n - f m) x‖₊ : ℝ≥0∞) < B N,
    { simp_rw ae_all_iff,
      exact λ N n m hnN hmN, ae_lt_of_ess_sup_lt (h_cau N n m hnN hmN), },
    simp_rw [snorm_exponent_top, snorm_ess_sup] at h_cau,
    refine h_cau_ae.mono (λ x hx, cauchy_seq_tendsto_of_complete _),
    refine cauchy_seq_of_le_tendsto_0 (λ n, (B n).to_real) _ _,
    { intros n m N hnN hmN,
      specialize hx N n m hnN hmN,
      rw [dist_eq_norm, ←ennreal.to_real_of_real (norm_nonneg _),
        ennreal.to_real_le_to_real ennreal.of_real_ne_top
        (ennreal.ne_top_of_tsum_ne_top hB N)],
      rw ←of_real_norm_eq_coe_nnnorm at hx,
      exact hx.le, },
    { rw ← ennreal.zero_to_real,
      exact tendsto.comp (ennreal.tendsto_to_real ennreal.zero_ne_top)
        (ennreal.tendsto_at_top_zero_of_tsum_ne_top hB), }, },
  have hp1 : 1 ≤ p.to_real,
  { rw [← ennreal.of_real_le_iff_le_to_real hp_top, ennreal.of_real_one],
    exact hp, },
  have h_cau' : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm' (f n - f m) (p.to_real) μ < B N,
  { intros N n m hn hm,
    specialize h_cau N n m hn hm,
    rwa snorm_eq_snorm' (zero_lt_one.trans_le hp).ne.symm hp_top at h_cau, },
  exact ae_tendsto_of_cauchy_snorm' hf hp1 hB h_cau',
end

lemma cauchy_tendsto_of_tendsto {f : ℕ → α → E} (hf : ∀ n, ae_strongly_measurable (f n) μ)
  (f_lim : α → E) {B : ℕ → ℝ≥0∞}
  (hB : ∑' i, B i ≠ ∞) (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N)
  (h_lim : ∀ᵐ (x : α) ∂μ, tendsto (λ n, f n x) at_top (𝓝 (f_lim x))) :
  at_top.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0) :=
begin
  rw ennreal.tendsto_at_top_zero,
  intros ε hε,
  have h_B : ∃ (N : ℕ), B N ≤ ε,
  { suffices h_tendsto_zero : ∃ (N : ℕ), ∀ n : ℕ, N ≤ n → B n ≤ ε,
      from ⟨h_tendsto_zero.some, h_tendsto_zero.some_spec _ le_rfl⟩,
    exact (ennreal.tendsto_at_top_zero.mp (ennreal.tendsto_at_top_zero_of_tsum_ne_top hB))
      ε hε, },
  cases h_B with N h_B,
  refine ⟨N, λ n hn, _⟩,
  have h_sub : snorm (f n - f_lim) p μ ≤ at_top.liminf (λ m, snorm (f n - f m) p μ),
  { refine snorm_lim_le_liminf_snorm (λ m, (hf n).sub (hf m)) (f n - f_lim) _,
    refine h_lim.mono (λ x hx, _),
    simp_rw sub_eq_add_neg,
    exact tendsto.add tendsto_const_nhds (tendsto.neg hx), },
  refine h_sub.trans _,
  refine liminf_le_of_frequently_le' (frequently_at_top.mpr _),
  refine λ N1, ⟨max N N1, le_max_right _ _, _⟩,
  exact (h_cau N n (max N N1) hn (le_max_left _ _)).le.trans h_B,
end

lemma mem_ℒp_of_cauchy_tendsto (hp : 1 ≤ p) {f : ℕ → α → E} (hf : ∀ n, mem_ℒp (f n) p μ)
  (f_lim : α → E) (h_lim_meas : ae_strongly_measurable f_lim μ)
  (h_tendsto : at_top.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0)) :
  mem_ℒp f_lim p μ :=
begin
  refine ⟨h_lim_meas, _⟩,
  rw ennreal.tendsto_at_top_zero at h_tendsto,
  cases (h_tendsto 1 zero_lt_one) with N h_tendsto_1,
  specialize h_tendsto_1 N (le_refl N),
  have h_add : f_lim = f_lim - f N + f N, by abel,
  rw h_add,
  refine lt_of_le_of_lt (snorm_add_le (h_lim_meas.sub (hf N).1) (hf N).1 hp) _,
  rw ennreal.add_lt_top,
  split,
  { refine lt_of_le_of_lt _ ennreal.one_lt_top,
    have h_neg : f_lim - f N = -(f N - f_lim), by simp,
    rwa [h_neg, snorm_neg], },
  { exact (hf N).2, },
end

lemma cauchy_complete_ℒp [complete_space E] (hp : 1 ≤ p)
  {f : ℕ → α → E} (hf : ∀ n, mem_ℒp (f n) p μ) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
  (h_cau : ∀ (N n m : ℕ), N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N) :
  ∃ (f_lim : α → E) (hf_lim_meas : mem_ℒp f_lim p μ),
    at_top.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0) :=
begin
  obtain ⟨f_lim, h_f_lim_meas, h_lim⟩ : ∃ (f_lim : α → E) (hf_lim_meas : strongly_measurable f_lim),
      ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (nhds (f_lim x)),
    from exists_strongly_measurable_limit_of_tendsto_ae (λ n, (hf n).1)
      (ae_tendsto_of_cauchy_snorm (λ n, (hf n).1) hp hB h_cau),
  have h_tendsto' : at_top.tendsto (λ n, snorm (f n - f_lim) p μ) (𝓝 0),
    from cauchy_tendsto_of_tendsto (λ m, (hf m).1) f_lim hB h_cau h_lim,
  have h_ℒp_lim : mem_ℒp f_lim p μ,
    from mem_ℒp_of_cauchy_tendsto hp hf f_lim h_f_lim_meas.ae_strongly_measurable h_tendsto',
  exact ⟨f_lim, h_ℒp_lim, h_tendsto'⟩,
end

/-! ### `Lp` is complete for `1 ≤ p` -/

instance [complete_space E] [hp : fact (1 ≤ p)] : complete_space (Lp E p μ) :=
complete_space_Lp_of_cauchy_complete_ℒp $
  λ f hf B hB h_cau, cauchy_complete_ℒp hp.elim hf hB.ne h_cau

end Lp
end measure_theory

end complete_space

/-! ### Continuous functions in `Lp` -/

open_locale bounded_continuous_function
open bounded_continuous_function

section

variables [topological_space α] [borel_space α] [second_countable_topology_either α E]
variables (E p μ)

/-- An additive subgroup of `Lp E p μ`, consisting of the equivalence classes which contain a
bounded continuous representative. -/
def measure_theory.Lp.bounded_continuous_function : add_subgroup (Lp E p μ) :=
add_subgroup.add_subgroup_of
  ((continuous_map.to_ae_eq_fun_add_hom μ).comp (to_continuous_map_add_hom α E)).range
  (Lp E p μ)

variables {E p μ}

/-- By definition, the elements of `Lp.bounded_continuous_function E p μ` are the elements of
`Lp E p μ` which contain a bounded continuous representative. -/
lemma measure_theory.Lp.mem_bounded_continuous_function_iff {f : (Lp E p μ)} :
  f ∈ measure_theory.Lp.bounded_continuous_function E p μ
    ↔ ∃ f₀ : (α →ᵇ E), f₀.to_continuous_map.to_ae_eq_fun μ = (f : α →ₘ[μ] E) :=
add_subgroup.mem_add_subgroup_of

namespace bounded_continuous_function

variables [is_finite_measure μ]

/-- A bounded continuous function on a finite-measure space is in `Lp`. -/
lemma mem_Lp (f : α →ᵇ E) :
  f.to_continuous_map.to_ae_eq_fun μ ∈ Lp E p μ :=
begin
  refine Lp.mem_Lp_of_ae_bound (‖f‖) _,
  filter_upwards [f.to_continuous_map.coe_fn_to_ae_eq_fun μ] with x _,
  convert f.norm_coe_le_norm x
end

/-- The `Lp`-norm of a bounded continuous function is at most a constant (depending on the measure
of the whole space) times its sup-norm. -/
lemma Lp_norm_le (f : α →ᵇ E) :
  ‖(⟨f.to_continuous_map.to_ae_eq_fun μ, mem_Lp f⟩ : Lp E p μ)‖
  ≤ (measure_univ_nnreal μ) ^ (p.to_real)⁻¹ * ‖f‖ :=
begin
  apply Lp.norm_le_of_ae_bound (norm_nonneg f),
  { refine (f.to_continuous_map.coe_fn_to_ae_eq_fun μ).mono _,
    intros x hx,
    convert f.norm_coe_le_norm x },
  { apply_instance }
end

variables (p μ)

/-- The normed group homomorphism of considering a bounded continuous function on a finite-measure
space as an element of `Lp`. -/
def to_Lp_hom [fact (1 ≤ p)] : normed_add_group_hom (α →ᵇ E) (Lp E p μ) :=
{ bound' := ⟨_, Lp_norm_le⟩,
  .. add_monoid_hom.cod_restrict
      ((continuous_map.to_ae_eq_fun_add_hom μ).comp (to_continuous_map_add_hom α E))
      (Lp E p μ)
      mem_Lp }

lemma range_to_Lp_hom [fact (1 ≤ p)] :
  ((to_Lp_hom p μ).range : add_subgroup (Lp E p μ))
    = measure_theory.Lp.bounded_continuous_function E p μ :=
begin
  symmetry,
  convert add_monoid_hom.add_subgroup_of_range_eq_of_le
    ((continuous_map.to_ae_eq_fun_add_hom μ).comp (to_continuous_map_add_hom α E))
    (by { rintros - ⟨f, rfl⟩, exact mem_Lp f } : _ ≤ Lp E p μ),
end

variables (𝕜 : Type*) [fact (1 ≤ p)]

/-- The bounded linear map of considering a bounded continuous function on a finite-measure space
as an element of `Lp`. -/
def to_Lp [normed_field 𝕜] [normed_space 𝕜 E] :
  (α →ᵇ E) →L[𝕜] (Lp E p μ) :=
linear_map.mk_continuous
  (linear_map.cod_restrict
    (Lp.Lp_submodule E p μ 𝕜)
    ((continuous_map.to_ae_eq_fun_linear_map μ).comp (to_continuous_map_linear_map α E 𝕜))
    mem_Lp)
  _
  Lp_norm_le

lemma coe_fn_to_Lp [normed_field 𝕜] [normed_space 𝕜 E] (f : α →ᵇ E) :
  to_Lp p μ 𝕜 f =ᵐ[μ] f := ae_eq_fun.coe_fn_mk f _

variables {𝕜}

lemma range_to_Lp [normed_field 𝕜] [normed_space 𝕜 E] :
  ((linear_map.range (to_Lp p μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E p μ)).to_add_subgroup)
    = measure_theory.Lp.bounded_continuous_function E p μ :=
range_to_Lp_hom p μ

variables {p}

lemma to_Lp_norm_le [nontrivially_normed_field 𝕜] [normed_space 𝕜 E]:
  ‖(to_Lp p μ 𝕜 : (α →ᵇ E) →L[𝕜] (Lp E p μ))‖ ≤ (measure_univ_nnreal μ) ^ (p.to_real)⁻¹ :=
linear_map.mk_continuous_norm_le _ ((measure_univ_nnreal μ) ^ (p.to_real)⁻¹).coe_nonneg _

lemma to_Lp_inj {f g : α →ᵇ E} [μ.is_open_pos_measure] [normed_field 𝕜] [normed_space 𝕜 E] :
  to_Lp p μ 𝕜 f = to_Lp p μ 𝕜 g ↔ f = g :=
begin
  refine ⟨λ h, _, by tauto⟩,
  rw [←fun_like.coe_fn_eq, ←(map_continuous f).ae_eq_iff_eq μ (map_continuous g)],
  refine (coe_fn_to_Lp p μ 𝕜 f).symm.trans (eventually_eq.trans _ $ coe_fn_to_Lp p μ 𝕜 g),
  rw h,
end

lemma to_Lp_injective [μ.is_open_pos_measure] [normed_field 𝕜] [normed_space 𝕜 E] :
  function.injective ⇑(to_Lp p μ 𝕜 : (α →ᵇ E) →L[𝕜] (Lp E p μ)) := λ f g hfg, (to_Lp_inj μ).mp hfg

end bounded_continuous_function

namespace continuous_map

variables [compact_space α] [is_finite_measure μ]
variables (𝕜 : Type*) (p μ) [fact (1 ≤ p)]

/-- The bounded linear map of considering a continuous function on a compact finite-measure
space `α` as an element of `Lp`.  By definition, the norm on `C(α, E)` is the sup-norm, transferred
from the space `α →ᵇ E` of bounded continuous functions, so this construction is just a matter of
transferring the structure from `bounded_continuous_function.to_Lp` along the isometry. -/
def to_Lp [normed_field 𝕜] [normed_space 𝕜 E] :
  C(α, E) →L[𝕜] (Lp E p μ) :=
(bounded_continuous_function.to_Lp p μ 𝕜).comp
  (linear_isometry_bounded_of_compact α E 𝕜).to_linear_isometry.to_continuous_linear_map

variables {𝕜}

lemma range_to_Lp [normed_field 𝕜] [normed_space 𝕜 E] :
  (linear_map.range (to_Lp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ)).to_add_subgroup
    = measure_theory.Lp.bounded_continuous_function E p μ :=
begin
  refine set_like.ext' _,
  have := (linear_isometry_bounded_of_compact α E 𝕜).surjective,
  convert function.surjective.range_comp this (bounded_continuous_function.to_Lp p μ 𝕜),
  rw ←bounded_continuous_function.range_to_Lp p μ,
  refl,
end

variables {p}

lemma coe_fn_to_Lp [normed_field 𝕜] [normed_space 𝕜 E] (f : C(α,  E)) :
  to_Lp p μ 𝕜 f =ᵐ[μ] f :=
ae_eq_fun.coe_fn_mk f _

lemma to_Lp_def [normed_field 𝕜] [normed_space 𝕜 E] (f : C(α, E)) :
  to_Lp p μ 𝕜 f
  = bounded_continuous_function.to_Lp p μ 𝕜 (linear_isometry_bounded_of_compact α E 𝕜 f) :=
rfl

@[simp] lemma to_Lp_comp_to_continuous_map [normed_field 𝕜] [normed_space 𝕜 E] (f : α →ᵇ E) :
  to_Lp p μ 𝕜 f.to_continuous_map
  = bounded_continuous_function.to_Lp p μ 𝕜 f :=
rfl

@[simp] lemma coe_to_Lp [normed_field 𝕜] [normed_space 𝕜 E] (f : C(α, E)) :
  (to_Lp p μ 𝕜 f : α →ₘ[μ] E) = f.to_ae_eq_fun μ :=
rfl

lemma to_Lp_injective [μ.is_open_pos_measure] [normed_field 𝕜] [normed_space 𝕜 E] :
  function.injective ⇑(to_Lp p μ 𝕜 : C(α, E) →L[𝕜] (Lp E p μ)) :=
(bounded_continuous_function.to_Lp_injective _).comp
  (linear_isometry_bounded_of_compact α E 𝕜).injective

lemma to_Lp_inj {f g : C(α, E)} [μ.is_open_pos_measure] [normed_field 𝕜] [normed_space 𝕜 E] :
  to_Lp p μ 𝕜 f = to_Lp p μ 𝕜 g ↔ f = g :=
(to_Lp_injective μ).eq_iff

variables {μ}

/-- If a sum of continuous functions `g n` is convergent, and the same sum converges in `Lᵖ` to `h`,
then in fact `g n` converges uniformly to `h`.  -/
lemma has_sum_of_has_sum_Lp {β : Type*} [μ.is_open_pos_measure] [normed_field 𝕜] [normed_space 𝕜 E]
  {g : β → C(α, E)} {f : C(α, E)} (hg : summable g)
  (hg2 : has_sum (to_Lp p μ 𝕜 ∘ g) (to_Lp p μ 𝕜 f)) : has_sum g f :=
begin
  convert summable.has_sum hg,
  exact to_Lp_injective μ (hg2.unique ((to_Lp p μ 𝕜).has_sum $ summable.has_sum hg)),
end

variables (μ) [nontrivially_normed_field 𝕜] [normed_space 𝕜 E]

lemma to_Lp_norm_eq_to_Lp_norm_coe :
  ‖(to_Lp p μ 𝕜 : C(α, E) →L[𝕜] (Lp E p μ))‖
  = ‖(bounded_continuous_function.to_Lp p μ 𝕜 : (α →ᵇ E) →L[𝕜] (Lp E p μ))‖ :=
continuous_linear_map.op_norm_comp_linear_isometry_equiv _ _

/-- Bound for the operator norm of `continuous_map.to_Lp`. -/
lemma to_Lp_norm_le :
  ‖(to_Lp p μ 𝕜 : C(α, E) →L[𝕜] (Lp E p μ))‖ ≤ (measure_univ_nnreal μ) ^ (p.to_real)⁻¹ :=
by { rw to_Lp_norm_eq_to_Lp_norm_coe, exact bounded_continuous_function.to_Lp_norm_le μ }

end continuous_map

end

namespace measure_theory

namespace Lp

lemma pow_mul_meas_ge_le_norm (f : Lp E p μ)
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (ε : ℝ≥0∞) :
  (ε * μ {x | ε ≤ ‖f x‖₊ ^ p.to_real}) ^ (1 / p.to_real) ≤ (ennreal.of_real ‖f‖) :=
(ennreal.of_real_to_real (snorm_ne_top f)).symm ▸
  pow_mul_meas_ge_le_snorm μ hp_ne_zero hp_ne_top (Lp.ae_strongly_measurable f) ε

lemma mul_meas_ge_le_pow_norm (f : Lp E p μ)
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (ε : ℝ≥0∞) :
  ε * μ {x | ε ≤ ‖f x‖₊ ^ p.to_real} ≤ (ennreal.of_real ‖f‖) ^ p.to_real :=
(ennreal.of_real_to_real (snorm_ne_top f)).symm ▸
  mul_meas_ge_le_pow_snorm μ hp_ne_zero hp_ne_top (Lp.ae_strongly_measurable f) ε

/-- A version of Markov's inequality with elements of Lp. -/
lemma mul_meas_ge_le_pow_norm' (f : Lp E p μ)
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (ε : ℝ≥0∞) :
  ε ^ p.to_real * μ {x | ε ≤ ‖f x‖₊} ≤ (ennreal.of_real ‖f‖) ^ p.to_real :=
(ennreal.of_real_to_real (snorm_ne_top f)).symm ▸
  mul_meas_ge_le_pow_snorm' μ hp_ne_zero hp_ne_top (Lp.ae_strongly_measurable f) ε

lemma meas_ge_le_mul_pow_norm (f : Lp E p μ)
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  μ {x | ε ≤ ‖f x‖₊} ≤ ε⁻¹ ^ p.to_real * (ennreal.of_real ‖f‖) ^ p.to_real :=
(ennreal.of_real_to_real (snorm_ne_top f)).symm ▸
  meas_ge_le_mul_pow_snorm μ hp_ne_zero hp_ne_top (Lp.ae_strongly_measurable f) hε

end Lp

end measure_theory
