/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.moments
import probability.kernel.condexp

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
