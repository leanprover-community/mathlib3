/-
Copyright (c) 2022 Rishikesh Vaishnav. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rishikesh Vaishnav
-/
import probability.independence

/-!
# Conditional Probability

This file defines conditional probability and includes basic results relating to it.

Given some measure `μ` defined on a measure space on some type `α` and some `s : set α`,
we define the measure of `μ` conditioned on `s` as the restricted measure scaled by
the inverse of the measure of `s`: `cond μ s = (μ s)⁻¹ • μ.restrict s`. The scaling
ensures that this is a probability measure (when `μ` is a finite measure).

From this definition, we derive the "axiomatic" definition of conditional probability
based on application: for any `s t : set α`, we have `μ[t|s] = (μ s)⁻¹ * μ (s ∩ t)`.

## Main Statements

* `cond_cond_eq_cond_inter`: conditioning on one set and then another is equivalent
  to conditioning on their intersection.
* `cond_eq_inv_mul_cond_mul`: Bayes' Theorem, `μ[t|s] = (μ s)⁻¹ * μ[s|t] * (μ t)`.

## Notations

This file uses the local notation `μ[|s]` the measure of `μ` conditioned on `s`,
and `μ[t|s]` for the probability of `t` given `s` under `μ` (equivalent to the
application `μ[|s] t`).

## Implementation notes

Because we have the alternative measure restriction application principles
`measure.restrict_apply` and `measure.restrict_apply'`, which require 
measurability of the restricted and restricting sets, respectively,
many of the theorems here will have corresponding alternatives as well.
For the sake of brevity, we've chosen to only go with `measure.restrict_apply'`
for now, but the alternative theorems can be added if needed.

Use of `@[simp]` generally follows the rule of removing conditions on a measure
when possible.

Hypotheses that are used to "define" a conditional distribution by requiring that
the conditioning set has non-zero measure should be named using the abbreviation
"c" (which stands for "conditionable") rather than "nz". For example `(hci : μ (s ∩ t) ≠ 0)`
(rather than `hnzi`) should be used for a hypothesis ensuring that `μ[|s ∩ t]` is defined.

## Tags
conditional, conditioned, bayes
-/

noncomputable theory

open measure_theory measurable_space

variables {α : Type*} {m : measurable_space α} (μ : measure α) {s t : set α}

namespace probability_theory

section definitions

/-- The conditional probability measure of measure `μ` on set `s` is `μ` restricted to `s` 
and scaled by the inverse of `μ s` (to make it a probability measure):
`(μ s)⁻¹ • μ.restrict s`. -/
def cond (s : set α) : measure α :=
  (μ s)⁻¹ • μ.restrict s

end definitions

local notation  μ `[` s `|` t `]` := cond μ t s
local notation  μ `[|`:60 t`]` := cond μ t

/-- The conditional probability measure of any finite measure on any set of positive measure
is a probability measure. -/
lemma cond_is_probability_measure [is_finite_measure μ] (hcs : μ s ≠ 0) :
  is_probability_measure $ μ[|s] :=
⟨by { rw [cond, measure.smul_apply, measure.restrict_apply measurable_set.univ,
  set.univ_inter], exact ennreal.inv_mul_cancel hcs (measure_ne_top _ s) }⟩

section bayes

@[simp] lemma cond_univ [is_probability_measure μ] :
  μ[|set.univ] = μ :=
by simp [cond, measure_univ, measure.restrict_univ]

/-- The axiomatic definition of conditional probability derived from a measure-theoretic one. -/
@[simp] lemma cond_apply (hms : measurable_set s) (t : set α) :
  μ[t|s] = (μ s)⁻¹ * μ (s ∩ t) :=
by { rw [cond, measure.smul_apply, measure.restrict_apply' hms, set.inter_comm], refl }

lemma inter_pos_of_cond_ne_zero (hms : measurable_set s) (hcst : μ[t|s] ≠ 0) :
  0 < μ (s ∩ t) :=
begin
  refine pos_iff_ne_zero.mpr (right_ne_zero_of_mul _),
  { exact (μ s)⁻¹ },
  convert hcst,
  simp [hms, set.inter_comm]
end

variable [is_finite_measure μ]

lemma cond_pos_of_inter_ne_zero (hms : measurable_set s) (hci : μ (s ∩ t) ≠ 0) :
  0 < μ[|s] t :=
begin
  rw cond_apply _ hms,
  refine ennreal.mul_pos _ hci,
  exact ennreal.inv_ne_zero.mpr (measure_ne_top _ _),
end

/-- Conditioning first on `s` and then on `t` results in the same measure as conditioning
on `s ∩ t`. -/
@[simp] lemma cond_cond_eq_cond_inter
  (hms : measurable_set s) (hmt : measurable_set t) (hci : μ (s ∩ t) ≠ 0) :
  μ[|s][|t] = μ[|s ∩ t] :=
begin
  have := hms.inter hmt,
  have := measure_ne_top μ s,
  have hcs : μ s ≠ 0 := (μ.to_outer_measure.pos_of_subset_ne_zero
    (set.inter_subset_left _ _) hci).ne',
  ext1,
  haveI := cond_is_probability_measure μ hcs,
  simp only [*, cond_apply, ←mul_assoc, ←set.inter_assoc],
  congr,
  simp [*, ennreal.mul_inv, mul_comm, ←mul_assoc, ennreal.inv_mul_cancel]
end

@[simp] lemma cond_mul_eq_inter (hms : measurable_set s) (hcs : μ s ≠ 0) (t : set α) :
  μ[t|s] * μ s = μ (s ∩ t) :=
by rw [cond_apply μ hms t, mul_comm, ←mul_assoc,
  ennreal.mul_inv_cancel hcs (measure_ne_top _ s), one_mul]

/-- **Bayes' Theorem** -/
theorem cond_eq_inv_mul_cond_mul (hms : measurable_set s) (hmt : measurable_set t) (ht : μ t ≠ 0) :
  μ[t|s] = (μ s)⁻¹ * μ[s|t] * (μ t) :=
by rw [mul_assoc, cond_mul_eq_inter μ hmt ht s, set.inter_comm, cond_apply _ hms]

end bayes

end probability_theory
