/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.moments
import probability.kernel.condexp
import probability.independence.basic
import probability.independence.cond_indep

/-!
# Dominated Cgf

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open measure_theory set filter topological_space real

open_locale ennreal measure_theory probability_theory

namespace probability_theory

section dominated_cgfₖ
variables {α β : Type*} {mα : measurable_space α} {mβ : measurable_space β} {κ : kernel α β}
  {μ : measure α} {X : β → ℝ} {f : ℝ → ℝ}

def dominated_cgfₖ {mα : measurable_space α} {mβ : measurable_space β}
  (X : β → ℝ) (f : ℝ → ℝ) (κ : kernel α β) (μ : measure α) : Prop :=
∀ᵐ a ∂μ, (∀ t, integrable (λ ω, exp (t * X ω)) (κ a)) ∧ cgf X (κ a) ≤ f

lemma dominated_cgfₖ.ae_integrable_exp_mul (h : dominated_cgfₖ X f κ μ) :
  ∀ᵐ a ∂μ, ∀ t, integrable (λ ω, exp (t * X ω)) (κ a) :=
by filter_upwards [h] with a ha using ha.1

lemma dominated_cgfₖ.ae_cgf_le (h : dominated_cgfₖ X f κ μ) :
  ∀ᵐ a ∂μ, cgf X (κ a) ≤ f :=
by filter_upwards [h] with a ha using ha.2

lemma dominated_cgfₖ.ae_mgf_le (h : dominated_cgfₖ X f κ μ) :
  ∀ᵐ a ∂μ, mgf X (κ a) ≤ λ t, exp (f t) :=
begin
  filter_upwards [h.ae_cgf_le] with a ha,
  exact λ t, (le_exp_log _).trans (exp_monotone (ha t)),
end

/-- This is a trivial application of `indep_funₖ.comp` but it will come up frequently. -/
lemma indep_funₖ.exp_mul {X Y : β → ℝ} (h_indep : indep_funₖ X Y κ μ) (s t : ℝ) :
  indep_funₖ (λ ω, exp (s * X ω)) (λ ω, exp (t * Y ω)) κ μ :=
begin
  have h_meas : ∀ t, measurable (λ x, exp (t * x)) := λ t, (measurable_id'.const_mul t).exp,
  change indep_funₖ ((λ x, exp (s * x)) ∘ X) ((λ x, exp (t * x)) ∘ Y) κ μ,
  exact indep_funₖ.comp h_indep (h_meas s) (h_meas t),
end

lemma indep_funₖ.mgf_add {X Y : β → ℝ} (h_indep : indep_funₖ X Y κ μ)
  --(hX : ae_strongly_measurable (λ ω, exp (t * X ω)) μ)
  --(hY : ae_strongly_measurable (λ ω, exp (t * Y ω)) μ)
  :
  ∀ᵐ a ∂μ, ∀ t, mgf (X + Y) (κ a) t = mgf X (κ a) t * mgf Y (κ a) t :=
begin
  simp_rw [mgf, pi.add_apply, mul_add, exp_add],
  rw indep_fun.integral_mul,
  exact (h_indep.exp_mul t t).integral_mul hX hY,
end

lemma indep_fun.mgf_add' {X Y : Ω → ℝ} (h_indep : indep_fun X Y μ)
  (hX : ae_strongly_measurable X μ) (hY : ae_strongly_measurable Y μ) :
  mgf (X + Y) μ t = mgf X μ t * mgf Y μ t :=
begin
  have A : continuous (λ (x : ℝ), exp (t * x)), by continuity,
  have h'X : ae_strongly_measurable (λ ω, exp (t * X ω)) μ :=
    A.ae_strongly_measurable.comp_ae_measurable hX.ae_measurable,
  have h'Y : ae_strongly_measurable (λ ω, exp (t * Y ω)) μ :=
    A.ae_strongly_measurable.comp_ae_measurable hY.ae_measurable,
  exact h_indep.mgf_add h'X h'Y
end

lemma indep_fun.cgf_add {X Y : Ω → ℝ} (h_indep : indep_fun X Y μ)
  (h_int_X : integrable (λ ω, exp (t * X ω)) μ)
  (h_int_Y : integrable (λ ω, exp (t * Y ω)) μ) :
  cgf (X + Y) μ t = cgf X μ t + cgf Y μ t :=
begin
  by_cases hμ : μ = 0,
  { simp [hμ], },
  simp only [cgf, h_indep.mgf_add h_int_X.ae_strongly_measurable h_int_Y.ae_strongly_measurable],
  exact log_mul (mgf_pos' hμ h_int_X).ne' (mgf_pos' hμ h_int_Y).ne',
end

lemma indep_funₖ.ae_integrable_exp_mul_add {X Y : β → ℝ} (h_indep : indep_funₖ X Y κ μ)
  (h_int_X : ∀ᵐ a ∂μ, ∀ t, integrable (λ ω, exp (t * X ω)) (κ a))
  (h_int_Y : ∀ᵐ a ∂μ, ∀ t, integrable (λ ω, exp (t * Y ω)) (κ a)) :
  ∀ᵐ a ∂μ, ∀ t, integrable (λ ω, exp (t * (X + Y) ω)) (κ a) :=

lemma dominated_cgfₖ.add_indep_funₖ {Y : β → ℝ} {fX fY : ℝ → ℝ} (hX : dominated_cgfₖ X fX κ μ)
  (hY : dominated_cgfₖ Y fY κ μ) (hindep : indep_funₖ X Y κ μ) :
  dominated_cgfₖ (X + Y) (fX + fY) κ μ :=
begin
  rw dominated_cgfₖ,
  filter_upwards
    [hindep.ae_integrable_exp_mul_add hX.ae_integrable_exp_mul hY.ae_integrable_exp_mul]
    with a ha,
  refine ⟨λ t, , _⟩,
  rw hindep.cgf_add (hX.integrable_exp_mul t) (hY.integrable_exp_mul t),
  calc cgf X μ t + cgf Y μ t
      ≤ cX * t ^ 2 / 2 + cY * t ^ 2 / 2 : add_le_add (hX.cgf_le t) (hY.cgf_le t)
  ... = (cX + cY) * t ^ 2 / 2 : by ring,
end

end dominated_cgfₖ

section cond_dominated_cgf

variables {Ω : Type*} [topological_space Ω] {m : measurable_space Ω} [mΩ : measurable_space Ω]
  [polish_space Ω] [borel_space Ω] [nonempty Ω]
  {μ : measure Ω} [is_finite_measure μ]

def cond_dominated_cgf {Ω : Type*} [topological_space Ω] [polish_space Ω] [nonempty Ω]
  (X : Ω → ℝ) (f : ℝ → ℝ)
  (m : measurable_space Ω) [mΩ : measurable_space Ω] [borel_space Ω] (hm : m ≤ mΩ)
  (μ : measure Ω) [is_finite_measure μ] : Prop :=
dominated_cgfₖ X f (condexp_kernel μ m) (μ.trim hm)

end cond_dominated_cgf

section dominated_cgf

variables {α : Type*} {mα : measurable_space α} {μ : measure α} {X : α → ℝ} {f : ℝ → ℝ}

def dominated_cgf {mα : measurable_space α} (X : α → ℝ) (f : ℝ → ℝ) (μ : measure α) : Prop :=
(∀ t, integrable (λ ω, real.exp (t * X ω)) μ) ∧ cgf X μ ≤ f

lemma dominated_cgf_iff_dominated_cgfₖ :
  dominated_cgf X f μ ↔ dominated_cgfₖ X f (kernel.const unit μ) (measure.dirac ()) :=
by rw [dominated_cgf, dominated_cgfₖ, ae_dirac_eq, eventually_pure, kernel.const_apply]

end dominated_cgf

end probability_theory
