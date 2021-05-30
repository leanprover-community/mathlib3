/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.tactic
import measure_theory.lp_space

open_locale big_operators ennreal

variables {α β : Type*} [measurable_space α] [measurable_space β]
  {f g : α → β} {s₁ s₂ : set α} {t₁ t₂ : set β} {μ ν : measure_theory.measure α}

-- Test the use of assumption

example (hf : measurable f) : measurable f := by measurability

-- Test that intro does not unfold `measurable`

example : measurable f → measurable f := by measurability

-- Test the use of apply_assumption to get (h i) from an hypothesis (h : ∀ i, ...).

example  {F : ℕ → α → β} (hF : ∀ i, measurable (F i)) :
  measurable (F 0) :=
by measurability

example {ι} [encodable ι] {S₁ S₂ : ι → set α} (hS₁ : ∀ i, measurable_set (S₁ i))
  (hS₂ : ∀ i, measurable_set (S₂ i)) :
  measurable_set (⋃ i, (S₁ i) ∪ (S₂ i)) :=
by measurability

-- Tests on sets

example (hs₁ : measurable_set s₁) (hs₂ : measurable_set s₂) :
  measurable_set (s₁ ∪ s₁) :=
by measurability

example {ι} [encodable ι] {S : ι → set α} (hs : ∀ i, measurable_set (S i)) :
  measurable_set (⋃ i, S i) :=
by measurability

example (hf : measurable f) (hs₁ : measurable_set s₁) (ht₂ : measurable_set t₂) :
  measurable_set ((f ⁻¹' t₂) ∩ s₁) :=
by measurability

-- Tests on functions

example [has_add β] [has_measurable_add₂ β] (hf : measurable f) (hg : measurable g) :
  measurable (λ x, f x + g x) :=
by measurability

example [has_add β] [has_measurable_add₂ β] (hf : measurable f) (hg : ae_measurable g μ) :
  ae_measurable (λ x, f x + g x) μ :=
by measurability

example [has_div β] [has_measurable_div₂ β] (hf : measurable f) (hg : measurable g)
  (ht : measurable_set t₂):
  measurable_set ((λ x, f x / g x) ⁻¹' t₂) :=
by measurability

example [topological_space α] [topological_space β] [opens_measurable_space α] [borel_space β]
  (hf : continuous f) :
  measurable f :=
by measurability

example [add_comm_monoid β] [has_measurable_add₂ β] {s : finset ℕ} {F : ℕ → α → β}
  (hF : ∀ i, ae_measurable (F i) μ) :
  ae_measurable (∑ i in s, (λ x, F (i+1) x + F i x)) μ :=
by measurability

example [normed_group β] [has_measurable_sub₂ β] {f : ℕ → α → β}
  (hf : ∀ i, ae_measurable (f i) μ) (p : ℝ) (i : ℕ) :
  ae_measurable (λ (a : α), f (i + 1) a - f i a) μ :=
by measurability?

example [normed_group β] [borel_space β] {f : ℕ → α → β}
  (hf : ∀ i, ae_measurable (f i) μ) (p : ℝ) (i : ℕ) :
  ae_measurable (λ (a : α), f (i + 1) a - f i a) μ :=
by measurability?

example [normed_group β] [borel_space β] {f : ℕ → α → β}
  (hf : ∀ i, ae_measurable (f i) μ) (p : ℝ) :
  ∀ n, ae_measurable
    (λ a, (∑ i in finset.range (n + 1), (nnnorm (f (i + 1) a - f i a) : ℝ≥0∞) ^ p)) μ :=
begin
  intro n,
  refine finset.ae_measurable_sum _ _,
  intros i hi,
  refine ae_measurable.pow_const _ _,
  refine ae_measurable.ennnorm _,
  refine ae_measurable.sub _ _,
end
