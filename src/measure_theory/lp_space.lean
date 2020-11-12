/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rémy Degenne.
-/
import measure_theory.l1_space
import analysis.special_functions.pow
import analysis.convex.specific_functions

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

section borel_space
variables [borel_space β] [topological_space.second_countable_topology β]

section measurability_lemmas

lemma real.measurable_rpow {p : ℝ} (hp0 : 0 < p) : measurable (λ a : ℝ, a^ p) :=
begin
  have h : continuous (λ a : ℝ, a ^ p),
  { change continuous (λ a : ℝ, (id a) ^ ((λ a : ℝ, p) a)),
    refine real.continuous_rpow _ continuous_id continuous_const,
    intro a, right, change 0 < p, exact hp0, },
  exact continuous.measurable h,
end

lemma nnreal.measurable_rpow {p : ℝ} (hp0 : 0 < p) : measurable (λ a : nnreal, a ^ p) :=
begin
  have h_rw : (λ (a : nnreal), a ^ p) = (λ (a : nnreal), nnreal.of_real(↑a ^ p)),
  { ext1 a, rw ←nnreal.coe_rpow, rw nnreal.of_real_coe, },
  rw h_rw,
  refine measurable.nnreal_of_real _,
  change measurable ((λ a : ℝ, a ^ p) ∘ (λ a : nnreal, ↑a)),
  exact measurable.comp (real.measurable_rpow hp0) (nnreal.measurable_coe),
end

lemma ennreal.measurable_rpow_coe {p : ℝ} (hp0 : 0 < p) :
  measurable (λ a : nnreal, (a : ennreal) ^ p) :=
begin
  simp_rw ennreal.coe_rpow_of_nonneg _ (le_of_lt hp0),
  exact measurable.ennreal_coe (nnreal.measurable_rpow hp0),
end

lemma measurable_nnnorm_rpow {f : α → β} {p : ℝ} (hp0 : 0 < p) (hf : measurable f) :
  measurable (λ (a : α), (nnnorm (f a)) ^ p) :=
measurable.comp (nnreal.measurable_rpow hp0) (measurable.comp measurable_nnnorm hf)

lemma measurable_nnnorm_rpow_coe {f : α → β} {p : ℝ} (hp0 : 0 < p) (hf : measurable f) :
  measurable (λ (a : α), (nnnorm (f a) : ennreal) ^ p) :=
measurable.comp (ennreal.measurable_rpow_coe hp0) (measurable.comp measurable_nnnorm hf)

end measurability_lemmas

lemma add_in_ℒp {f g : α → β} :
  in_ℒp hp1 μ f → in_ℒp hp1 μ g → in_ℒp hp1 μ (f+g) :=
begin
  have hp0 : 0 ≤ p, from le_trans zero_le_one hp1,
  have hp0_lt : 0 < p, from lt_of_lt_of_le zero_lt_one hp1,
  have hp0_sub1 : 0 ≤ p - 1, by { simp only [sub_nonneg], exact hp1, },
  intros hf hg,
  split,
  exact measurable.add hf.1 hg.1,
  simp_rw pi.add_apply,
  refine lt_of_le_of_lt _ _,
  exact ∫⁻ a, (2^(p-1) * (nnnorm (f a) : ennreal) ^ p + 2^(p-1) * (nnnorm (g a) : ennreal) ^ p) ∂ μ,
  have h_zero_lt_half : (0 : nnreal) < 1 / 2,
  by { simp only [one_div, nnreal.inv_pos, zero_lt_bit0], exact zero_lt_one, },
  { refine lintegral_mono _,
    intro a, simp only,
    -- go from ennreal to nnreal
    simp_rw [←@ennreal.coe_two, ennreal.coe_rpow_of_nonneg _ hp0,
      ennreal.coe_rpow_of_nonneg _ hp0_sub1, ←ennreal.coe_mul, ←ennreal.coe_add, ennreal.coe_le_coe],
    -- continue the proof with nnreal
    have h_zero_lt : (0 : nnreal) < (1 / 2) ^ p,
    { rw [←nnreal.zero_rpow (ne_of_lt hp0_lt).symm, nnreal.rpow_lt_rpow_iff hp0_lt],
      exact h_zero_lt_half, },
    rw [←mul_le_mul_left (h_zero_lt), mul_add],
    repeat {rw ←mul_pow,}, repeat {rw ← mul_assoc},
    have h_rw : (1 / 2) ^ p * (2:nnreal) ^ (p - 1) = 1 / 2,
    { rw [nnreal.rpow_sub, nnreal.div_rpow], simp only [one_div, nnreal.rpow_one, nnreal.one_rpow],
      rw [←mul_div_assoc, inv_mul_cancel, one_div],
      simp only [not_and, nnreal.rpow_eq_zero_iff, not_not, nnreal.coe_eq_zero, ne.def],
      intro h_absurd, exfalso, exact two_ne_zero h_absurd,
      exact two_ne_zero, },
    repeat {rw h_rw,},
    have h_nnnorm_add_le : ((1/2) * (nnnorm (f a + g a))) ^ p
      ≤ ((1/2) * (nnnorm (f a)) + (1/2) * (nnnorm (g a))) ^ p,
    { refine nnreal.rpow_le_rpow _ hp0,
      rw [← mul_add, mul_le_mul_left h_zero_lt_half],
      exact nnnorm_add_le (f a) (g a), },
    rw ←nnreal.mul_rpow,
    refine le_trans h_nnnorm_add_le _,
    repeat {rw ←smul_eq_mul},
    -- go from nnreal to ℝ to use convexity (which is not defined for nnreal)
    suffices h_R :
      (((1 / (2:nnreal)) • nnnorm (f a) + (1 / (2:nnreal)) • nnnorm (g a)) ^ p).val
      ≤ ((1 / (2:nnreal)) • nnnorm (f a) ^ p + (1 / (2:nnreal)) • nnnorm (g a) ^ p).val,
    { exact h_R, },
    have h_eq_left :
      (((1 / (2:nnreal)) • nnnorm (f a) + (1 / (2:nnreal)) • nnnorm (g a)) ^ p).val
      = ((1 / (2:real)) • norm (f a) + (1 / (2:real)) • norm (g a)) ^ p,
    { simp only [one_div, algebra.id.smul_eq_mul, nnreal.val_eq_coe, nnreal.coe_inv, nnreal.coe_add,
        coe_nnnorm, nnreal.coe_rpow, nnreal.coe_one, nnreal.coe_bit0, nnreal.coe_mul], },
    have h_eq_right :
      ((1 / (2:nnreal)) • nnnorm (f a) ^ p + (1 / (2:nnreal)) • nnnorm (g a) ^ p).val
      = (1 / (2:real)) • norm (f a) ^ p + (1 / (2:real)) • norm (g a) ^ p,
    { simp only [one_div, algebra.id.smul_eq_mul, nnreal.val_eq_coe, nnreal.coe_inv, nnreal.coe_add,
        coe_nnnorm, nnreal.coe_rpow, nnreal.coe_one, nnreal.coe_bit0, nnreal.coe_mul], },
    rw [h_eq_left, h_eq_right],
    -- use convexity of rpow
    refine (convex_on_rpow hp1).right _ _ _ _ _,
    rw set.mem_Ici, exact norm_nonneg (f a),
    rw set.mem_Ici, exact norm_nonneg (g a),
    exact le_of_lt h_zero_lt_half, exact le_of_lt h_zero_lt_half,
    ring, },
  { rw lintegral_add, simp_rw mul_comm, repeat {rw lintegral_mul_const},
    rw ennreal.add_lt_top,
    split; rw ennreal.mul_lt_top_iff; left;
    { split, try { exact hf.2, }, try { exact hg.2, },
      refine ennreal.rpow_lt_top_of_nonneg hp0_sub1 ennreal.coe_ne_top, },
    -- finish by proving the measurability of all functions involved
    exact measurable_nnnorm_rpow_coe hp0_lt hg.left,
    exact measurable_nnnorm_rpow_coe hp0_lt hf.left,
    all_goals { simp_rw [←@ennreal.coe_two, ennreal.coe_rpow_of_nonneg _ hp0,
      ennreal.coe_rpow_of_nonneg _ hp0_sub1, ←ennreal.coe_mul],
      refine measurable.ennreal_coe _, },
    refine measurable.const_mul (measurable_nnnorm_rpow hp0_lt hf.1) _,
    refine measurable.const_mul (measurable_nnnorm_rpow hp0_lt hg.1) _, },
end

lemma neg_in_ℒp {f : α → β} :
  in_ℒp hp1 μ f → in_ℒp hp1 μ (-f) :=
begin
  intro hf,
  split,
  exact measurable.neg hf.1,
  simp only [hf.right, pi.neg_apply, nnnorm_neg],
end

lemma is_add_subgroup {μ : measure α}:
  is_add_subgroup {f : α → β | in_ℒp hp1 μ f} :=
{ zero_mem := @zero_in_ℒp α β _ _ _ p hp1 μ,
  add_mem := λ _ _, @ℒp.add_in_ℒp α β _ _ _ p hp1 μ _ _ _ _,
  neg_mem := λ _, @ℒp.neg_in_ℒp α β _ _ _ p hp1 μ _ _ _ }

instance {p : ℝ} {hp1 : 1 ≤ p} {μ : measure α} : add_comm_group (ℒp α β hp1 μ) :=
@subtype.add_comm_group _ _ {f : α → β | in_ℒp hp1 μ f} (is_add_subgroup)

end borel_space

end ℒp
