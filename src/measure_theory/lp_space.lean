/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rémy Degenne.
-/
import measure_theory.l1_space
import analysis.special_functions.pow

/-!
# ℒp space

This file describes the subtype of measurable functions with finite semi-norm
`(∫⁻ a, (nnnorm (f a))^(p : ℝ) ∂μ) ^ (1/p)` for `p:ℝ` with `1 ≤ p`.

## Main definitions and results

* `ℒp α β hp1 μ` : the type of measurable functions `α → β` with finite p-seminorm for measure `μ`,
                    for `hp1 : 1 ≤ p`,
* `in_ℒp hp1 μ f`: the property 'f belongs to ℒp for measure μ' and real p such that `hp1 : 1 ≤ p`.

## Notation

* `snorm' f ` : `(∫⁻ a, (nnnorm (f a))^(p : ℝ) ∂μ) ^ (1/p)` for `f : α → β`
* `snorm f`   : `(∫⁻ a, (nnnorm (f.val a))^(p : ℝ) ∂μ) ^ (1/p)` for `f : ℒp α β (1≤p) μ`

-/

open measure_theory

section ℒp_space_definition
variables {α β : Type*} [measurable_space α] [measurable_space β] [normed_group β]

def in_ℒp {p : ℝ} (hp1 : 1 ≤ p) (μ : measure α) (f : α → β) : Prop :=
measurable f ∧ ∫⁻ a, (nnnorm (f a)) ^ p ∂μ < ⊤

def ℒp (α β : Type*) [measurable_space α] [measurable_space β] [normed_group β]
  {p : ℝ} (hp1 : 1 ≤ p) (μ : measure α) : Type* := {f : α → β // in_ℒp hp1 μ f}

protected lemma ℒp.in_ℒp {α β : Type*} [measurable_space α] [measurable_space β] [normed_group β]
  {p : ℝ} {hp1 : 1 ≤ p} {μ : measure α} (f : ℒp α β hp1 μ) : in_ℒp hp1 μ f.val := f.prop

lemma in_ℒp_one_iff_integrable (μ : measure α) :
  ∀ f : α → β, in_ℒp (le_refl 1) μ f ↔ integrable f μ :=
begin
  intro f,
  unfold integrable, unfold has_finite_integral, unfold in_ℒp,
  simp only [ennreal.rpow_one, nnreal.coe_one],
end

variables {p : ℝ} {hp1 : 1 ≤ p} {μ : measure α}

lemma lintegral_rpow_nnnorm_zero (hp0_lt : 0 < p) :
  ∫⁻ a, (nnnorm ((0 : α → β) a))^p ∂μ = 0 :=
begin
  simp_rw pi.zero_apply,
  rw nnnorm_zero,
  rw lintegral_const,
  rw mul_eq_zero,
  left,
  exact ennreal.zero_rpow_of_pos hp0_lt,
end

lemma zero_in_ℒp : in_ℒp hp1 μ (0 : α → β) :=
begin
  split,
  exact measurable_zero,
  refine lt_of_le_of_lt _ with_top.zero_lt_top,
  rw lintegral_rpow_nnnorm_zero (lt_of_lt_of_le zero_lt_one hp1),
  exact le_refl 0,
  exact _inst_2,
end

protected def ℒp.zero : ℒp α β hp1 μ := ⟨(0 : α → β), zero_in_ℒp⟩

instance : has_zero (ℒp α β hp1 μ) := ⟨ℒp.zero⟩

instance : inhabited (ℒp α β hp1 μ) := ⟨0⟩

end ℒp_space_definition


noncomputable theory

namespace ℒp
variables {α β : Type*} [measurable_space α] [measurable_space β] [normed_group β]
  {p : ℝ} {hp1 : 1 ≤ p} {μ : measure α}

def snorm' (hp1 : 1 ≤ p) {f : α → β} (hf : measurable f) (μ : measure α) : ennreal :=
(∫⁻ a, (nnnorm (f a))^(p : ℝ) ∂μ) ^ (1/p)

def snorm (f : ℒp α β hp1 μ) : ennreal := (∫⁻ a, (nnnorm (f.val a))^(p : ℝ) ∂μ) ^ (1/p)

lemma snorm_eq_snorm' (f : ℒp α β hp1 μ) : snorm f = snorm' hp1 f.prop.1 μ := rfl

lemma snorm'_lt_top {f : α → β} (hfp : in_ℒp hp1 μ f) : snorm' hp1 hfp.left μ < ⊤ :=
begin
  unfold snorm',
  refine ennreal.rpow_lt_top_of_nonneg _ (ne_of_lt hfp.right),
  rw [one_div, inv_nonneg],
  exact le_trans zero_le_one hp1,
end

lemma snorm'_ne_top {f : α → β} (hfp : in_ℒp hp1 μ f) : snorm' hp1 hfp.left μ ≠ ⊤ :=
ne_of_lt (snorm'_lt_top hfp)

lemma snorm_lt_top {f : ℒp α β hp1 μ} : snorm f < ⊤ :=
by {rw snorm_eq_snorm', exact snorm'_lt_top f.in_ℒp, }

lemma snorm_ne_top (f : ℒp α β hp1 μ) : snorm f ≠ ⊤ := ne_of_lt snorm_lt_top

lemma snorm_zero : snorm (0 : ℒp α β hp1 μ) = 0 :=
begin
  have hp0_lt : 0 < p, from lt_of_lt_of_le zero_lt_one hp1,
  have h : ∫⁻ a, (nnnorm ((0 : ℒp α β hp1 μ).val a))^(p : ℝ) ∂μ = 0,
  from lintegral_rpow_nnnorm_zero hp0_lt,
  unfold snorm, rw h,
  rw ennreal.rpow_eq_zero_iff,
  left,
  split,
  refl,
  rw [one_div, inv_pos], exact hp0_lt,
end

end ℒp
