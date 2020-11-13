/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rémy Degenne.
-/
import measure_theory.l1_space
import analysis.special_functions.pow

/-!
# ℒp space

This file describes the type of measurable functions with finite seminorm
`(∫⁻ a, (nnnorm (f a))^(p : ℝ) ∂μ) ^ (1/p)` for `p:ℝ` with `1 ≤ p`.

## Main definitions and results

* `ℒp α β hp1 μ` : the type of measurable functions `α → β` with finite p-seminorm for
                      measure `μ`, for `hp1 : 1 ≤ p`,
* `in_ℒp p μ f`  : the property 'f belongs to ℒp for measure μ' and real p.

## Notation

* `snorm' f ` : `(∫⁻ a, (nnnorm (f a))^(p : ℝ) ∂μ) ^ (1/p)` for `f : α → β`
* `snorm f`   : `(∫⁻ a, (nnnorm (f.val a))^(p : ℝ) ∂μ) ^ (1/p)` for `f : ℒp α β (1≤p) μ`

-/

open measure_theory

section ℒp_space_definition
variables {α β γ : Type*} [measurable_space α] [measurable_space β] [normed_group β]
  [normed_group γ]

/-- The property 'f belongs to ℒp for measure μ and real p' -/
def in_ℒp (p : ℝ) (μ : measure α) (f : α → β) : Prop :=
measurable f ∧ ∫⁻ a, (nnnorm (f a)) ^ p ∂μ < ⊤

/-- The type of measurable functions `α → β` with finite p-seminorm for measure `μ`, for `1 ≤ p` -/
structure ℒp (α β : Type*) [measurable_space α] [measurable_space β] [normed_group β]
  {p : ℝ} (hp1 : 1 ≤ p) (μ : measure α) :=
(val : α → β)
(measurable : measurable val)
(lintegral_lt_top : ∫⁻ a, (nnnorm (val a))^p ∂μ < ⊤)
(one_le_p : 1 ≤ p)

variables {p : ℝ} {hp1 : 1 ≤ p} {μ : measure α}

protected lemma ℒp.eq : ∀ {f g : ℒp α β hp1 μ}, f.val = g.val → f = g
| ⟨x, h11, h12, h14⟩ ⟨.(x), h21, h22, h23⟩ rfl := rfl

protected lemma ℒp.in_ℒp (f : ℒp α β hp1 μ) : in_ℒp p μ f.val :=
begin
  split,
  exact f.measurable,
  exact f.lintegral_lt_top,
end

/-- Build an element of ℒp from a function with the in_ℒp property -/
def ℒp.mk_of_in_ℒp (hp1 : 1 ≤ p) {f : α → β} (h : in_ℒp p μ f) : ℒp α β hp1 μ :=
⟨f, h.left, h.right, hp1⟩

lemma ℒp.mk_of_in_ℒp_in_ℒp_eq_self (f : ℒp α β hp1 μ) : ℒp.mk_of_in_ℒp hp1 f.in_ℒp = f :=
begin
  refine ℒp.eq _, refl,
end

lemma in_ℒp_one_iff_integrable :
  ∀ f : α → β, in_ℒp 1 μ f ↔ integrable f μ :=
begin
  intro f,
  unfold integrable, unfold has_finite_integral, unfold in_ℒp,
  simp only [ennreal.rpow_one, nnreal.coe_one],
end

lemma lintegral_rpow_nnnorm_zero (hp0_lt : 0 < p) : ∫⁻ a, (nnnorm ((0 : α → γ) a))^p ∂μ = 0 :=
begin
  simp_rw pi.zero_apply,
  rw nnnorm_zero,
  rw lintegral_const,
  rw mul_eq_zero,
  left,
  exact ennreal.zero_rpow_of_pos hp0_lt,
end

lemma zero_in_ℒp (hp0_lt : 0 < p): in_ℒp p μ (0 : α → β) :=
begin
  split,
  exact measurable_zero,
  exact lt_of_le_of_lt (le_of_eq (lintegral_rpow_nnnorm_zero hp0_lt)) with_top.zero_lt_top,
end

/-- The zero function is the 0 in ℒp -/
protected def ℒp.zero : ℒp α β hp1 μ :=
ℒp.mk_of_in_ℒp hp1 (zero_in_ℒp (lt_of_lt_of_le zero_lt_one hp1))

instance : has_zero (ℒp α β hp1 μ) := ⟨ℒp.zero⟩

instance : inhabited (ℒp α β hp1 μ) := ⟨0⟩

end ℒp_space_definition


noncomputable theory

namespace ℒp_space
variables {α β γ: Type*} [measurable_space α] [measurable_space β] [normed_group β]
  [normed_group γ]
  {p : ℝ} {hp1 : 1 ≤ p} {μ : measure α}

/-- seminorm on ℒp, with function and measure as arguments \ -/
def snorm' (f : α → γ) (p : ℝ) (μ : measure α) : ennreal := (∫⁻ a, (nnnorm (f a))^p ∂μ) ^ (1/p)

/-- seminorm on ℒp -/
def snorm (f : ℒp α β hp1 μ) : ennreal := (∫⁻ a, (nnnorm (f.val a))^(p : ℝ) ∂μ) ^ (1/p)

lemma snorm_eq_snorm' (f : ℒp α β hp1 μ) : snorm f = snorm' f.val p μ := rfl

lemma snorm'_lt_top {f : α → β} (hp0 : 0 ≤ p) (hfp : in_ℒp p μ f) : snorm' f p μ < ⊤ :=
begin
  unfold snorm',
  refine ennreal.rpow_lt_top_of_nonneg _ (ne_of_lt hfp.right),
  rw [one_div, inv_nonneg],
  exact hp0,
end

lemma snorm'_ne_top {f : α → β} (hp0 : 0 ≤ p) (hfp : in_ℒp p μ f) : snorm' f p μ ≠ ⊤ :=
ne_of_lt (snorm'_lt_top hp0 hfp)

lemma snorm_lt_top {f : ℒp α β hp1 μ} : snorm f < ⊤ :=
by {rw snorm_eq_snorm', exact snorm'_lt_top (le_trans zero_le_one f.one_le_p) f.in_ℒp, }

lemma snorm_ne_top {f : ℒp α β hp1 μ} : snorm f ≠ ⊤ := ne_of_lt snorm_lt_top

lemma snorm_zero : snorm (0 : ℒp α β hp1 μ) = 0 :=
begin
  have hp0_lt : 0 < p, from lt_of_lt_of_le zero_lt_one hp1,
  have h : ∫⁻ a, (nnnorm ((0 : ℒp α β hp1 μ).val a))^(p : ℝ) ∂μ = 0,
  from lintegral_rpow_nnnorm_zero hp0_lt,
  unfold snorm,
  rw [h, ennreal.rpow_eq_zero_iff],
  left,
  split,
  refl,
  rw [one_div, inv_pos], exact hp0_lt,
end

end ℒp_space
