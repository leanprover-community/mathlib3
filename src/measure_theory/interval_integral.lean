/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/

import measure_theory.set_integral
import analysis.calculus.deriv
import tactic.apply

/-!
# Interval integral

Integrate a function over a real interval.

## Main results

The fundamental theorem of calculus is proved in this file.

## Notation

`∫ x in a..b, f x` stands for
`if a ≤ b then integral (indicator [a, b] f) else - integral (indicator [a, b] f))`
-/

noncomputable theory
open set filter topological_space measure_theory
open_locale classical topological_space interval

set_option class.instance_max_depth 50

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

section measurable_on
variables [topological_space α] [decidable_linear_order α] [order_closed_topology α]
          [measurable_space β] [has_zero β] {a b c x y : α} {s : set α} {f : α → β}

lemma measurable_on.subinterval (hx : x ∈ [a, b]) (hy : y ∈ [a, b]) (h : measurable_on [a, b] f) :
  measurable_on [x, y] f :=
h.subset is_measurable_interval (interval_subset_interval hx hy)

lemma measurable_on.subinterval_left (hx : x ∈ [a, b]) (h : measurable_on [a, b] f) :
  measurable_on [a, x] f :=
h.subinterval left_mem_interval hx

lemma measurable_on.subinterval_right (hx : x ∈ [a, b]) (h : measurable_on [a, b] f) :
  measurable_on [x, b] f :=
h.subinterval hx right_mem_interval

lemma measurable_on.Icc_of_interval : measurable_on [a, b] f → measurable_on (Icc a b) f :=
measurable_on.subset is_measurable_Icc Icc_subset_interval

lemma measurable_on.Icc_of_interval' : measurable_on [a, b] f → measurable_on (Icc b a) f :=
by { rw interval_swap, exact measurable_on.Icc_of_interval }

lemma measurable_on.interval_combine (hab : measurable_on [a, b] f) (hbc : measurable_on [b, c] f) :
  measurable_on [a, c] f :=
begin
  wlog ac : a ≤ c := le_total a c using [a c, c a],
  { cases le_total b c with bc cb,
    cases le_total a b with ab ba,
    { simp only [interval_of_le ab, interval_of_le ac, interval_of_le bc] at *,
      rw ← Icc_union_Icc_eq_Icc ab bc,
      exact measurable_on.union is_measurable_Icc is_measurable_Icc hab hbc },
    { exact hbc.subinterval (Icc_subset_interval ⟨ba, ac⟩) right_mem_interval },
    { exact hab.subinterval left_mem_interval (Icc_subset_interval ⟨ac, cb⟩) } },
  let h := interval_swap,
  rw [h b a, h c b, h c a] at this,
  apply' this,
  assumption'
end

lemma measurable_on.interval_split_left (hac : measurable_on [a, c] f) (hab : measurable_on [a, b] f) :
  measurable_on [b, c] f :=
by { rw [interval_swap] at hab, exact hab.interval_combine hac }

lemma measurable_on.interval_split_right (hac : measurable_on [a, c] f) (hbc : measurable_on [b, c] f) :
  measurable_on [a, b] f :=
by { rw [interval_swap] at hbc, exact hac.interval_combine hbc }

end measurable_on

section integrable_on
variables [normed_group β] {s t : set ℝ} {f g : ℝ → β} {a b c x y : ℝ}

lemma integrable_on.Icc_of_interval :
  integrable_on [a, b] f → integrable_on (Icc a b) f :=
integrable_on.subset Icc_subset_interval

lemma integrable_on.Icc_of_interval' :
  integrable_on [a, b] f → integrable_on (Icc b a) f :=
by { rw interval_swap, exact integrable_on.Icc_of_interval }

lemma integrable_on_interval_const {a b : ℝ} {c : β} : integrable_on [a, b] (λx:ℝ, c) :=
integrable_on_const_of_volume is_measurable_interval
  (by { rw real.volume_interval, exact ennreal.coe_lt_top }) _

lemma integrable_on.subinterval (hx : x ∈ [a, b]) (hy : y ∈ [a, b]) (h : integrable_on [a, b] f) :
  integrable_on [x, y] f :=
h.subset (interval_subset_interval hx hy)

lemma integrable_on.subinterval_left (hx : x ∈ [a, b]) (h : integrable_on [a, b] f) :
  integrable_on [a, x] f :=
h.subinterval left_mem_interval hx

lemma integrable_on.subinterval_right (hx : x ∈ [a, b]) (h : integrable_on [a, b] f) :
  integrable_on [x, b] f :=
h.subinterval hx right_mem_interval

lemma integrable_on.interval_combine
  (hfm : measurable_on [a, b] f) (hfi : integrable_on [a, b] f)
  (hfm' : measurable_on [b, c] f) (hfi' : integrable_on [b, c] f) :
  integrable_on [a, c] f :=
begin
  wlog ac : a ≤ c := le_total a c using [a c, c a],
  { cases le_total b c with bc cb,
    cases le_total a b with ab ba,
    { simp only [interval_of_le ab, interval_of_le ac, interval_of_le bc] at *,
      rw ← Icc_union_Icc_eq_Icc ab bc,
      refine integrable_on.union is_measurable_Icc is_measurable_Icc _ _ _ _, assumption' },
    { exact hfi'.subinterval (Icc_subset_interval ⟨ba, ac⟩) right_mem_interval },
    { exact hfi.subinterval left_mem_interval (Icc_subset_interval ⟨ac, cb⟩) } },
  rw [interval_swap c b, interval_swap b a, interval_swap c a] at this,
  apply this,
  assumption'
end

lemma integrable_on.interval_split_left
  (hfm : measurable_on [a, c] f) (hfi : integrable_on [a, c] f)
  (hfm' : measurable_on [a, b] f) (hfi' : integrable_on [a, b] f) :
  integrable_on [b, c] f :=
by { rw [interval_swap] at hfm' hfi', apply hfi'.interval_combine hfm', assumption' }

lemma integrable_on.interval_split_right
  (hfm : measurable_on [a, c] f) (hfi : integrable_on [a, c] f)
  (hfm' : measurable_on [b, c] f) (hfi' : integrable_on [b, c] f) :
  integrable_on [a, b] f :=
by { rw [interval_swap] at hfm' hfi', apply hfi.interval_combine hfm, assumption' }

end integrable_on

namespace real

open set

variables [normed_group β] [second_countable_topology β] [normed_space ℝ β] [complete_space β]
  {f f' g g' : ℝ → β} {a b c : ℝ} {x₀ : ℝ}

notation `∫` binders ` in ` a `..` b `, ` r:(scoped f, if a ≤ b then measure_theory.integral (set.indicator [a, b] f) else - measure_theory.integral (set.indicator [a, b] f)) := r

lemma integral_self : (∫ x in a..a, f x) = 0 :=
by { rw if_pos (le_refl _), apply integral_on_volume_zero, rw [interval_self, volume_singleton] }

lemma integral_of_le (h : a ≤ b) (f : ℝ → β) :
  (∫ x in a..b, f x) = ∫ x in [a, b], f x :=
if_pos h

lemma integral_of_not_le (h : ¬ a ≤ b) (f : ℝ → β) :
  (∫ x in a..b, f x) = - ∫ x in [a, b], f x :=
if_neg h

lemma integral_of_le' (h : b ≤ a) (f : ℝ → β) :
  (∫ x in a..b, f x) = - ∫ x in [a, b], f x :=
begin
  split_ifs with h',
  { rw [le_antisymm h h', integral_on_interval_self, neg_zero] },
  refl
end

lemma integral_eq_neg_swap (a b : ℝ) : (∫ x in a..b, f x) = - (∫ x in b..a, f x) :=
begin
  cases le_total a b with ab ba,
  { rw [integral_of_le ab, integral_of_le' ab, interval_swap, neg_neg] },
  { rw [integral_of_le ba, integral_of_le' ba, interval_swap] }
end

lemma integral_undef (h : ¬ (measurable_on [a, b] f ∧ integrable_on [a, b] f)) :
  (∫ x in a..b, f x) = 0 :=
begin
  split_ifs with hab,
  { simp only [interval_of_le hab] at *, exact integral_undef h },
  { simp only [interval_of_not_le hab] at *, rw [integral_undef h, neg_zero] }
end

lemma integral_congr (h : ∀ x, x ∈ [a, b] → f x = g x) : (∫ x in a..b, f x) = ∫ x in a..b, g x :=
begin
  split_ifs with h',
  { simp only [interval_of_le h'] at *,
    exact integral_on_congr h },
  { simp only [interval_of_not_le h'] at *,
    rw integral_on_congr h }
end

lemma integral_congr_ae (h : ∀ₘ x, x ∈ [a, b] → f x = g x)
  (hfm : measurable_on [a, b] f) (hgm : measurable_on [a, b] g) :
  (∫ x in a..b, f x) = (∫ x in a..b, g x) :=
begin
  split_ifs with h,
  { simp only [interval_of_le h] at *,
    rw integral_on_congr_of_ae_eq,
    assumption' },
  { simp only [interval_of_not_le h] at *,
    rw integral_on_congr_of_ae_eq,
    assumption' }
end

lemma integral_add (hfm : measurable_on [a, b] f) (hfi : integrable_on [a, b] f)
  (hgm : measurable_on [a, b] g) (hgi : integrable_on [a, b] g) :
  (∫ x in a..b, f x + g x) = (∫ x in a..b, f x) + (∫ x in a..b, g x) :=
begin
  split_ifs with h,
  { simp only [interval_of_le h] at *,
    rw [integral_on_add], assumption' },
  { simp only [interval_of_not_le h] at *,
    rw [← neg_add, integral_on_add], assumption' }
end

lemma integral_const {c : β} : (∫ x in a..b, c) = (b - a) • c :=
begin
  split_ifs with h,
  { rw [integral_on_const, volume_interval, ← ennreal.of_real, ennreal.to_real_of_real, abs_of_nonneg],
    exact sub_nonneg_of_le h, exact abs_nonneg _, exact is_measurable_interval },
  { rw [integral_on_const, volume_interval, ← ennreal.of_real, ennreal.to_real_of_real,
      abs_of_nonpos, ← neg_smul, neg_neg],
    exact sub_nonpos_of_le (le_of_not_ge h), exact abs_nonneg _, exact is_measurable_interval }
end

lemma norm_integral_le_abs (a b : ℝ) (f : ℝ → β):
  ∥(∫ x in a..b, f x)∥ ≤ abs (∫ x in a..b, ∥f x∥) :=
begin
  split_ifs with h,
  { simp only [interval_of_le h] at *,
    rw abs_of_nonneg,
    { apply norm_integral_on_le },
    exact integral_on_nonneg (λ _ _, norm_nonneg _) },
  { simp only [interval_of_ge (le_of_not_ge h)] at *,
    rw [abs_of_nonpos, neg_neg, norm_neg],
    { apply norm_integral_on_le },
    rw neg_nonpos,
    exact integral_on_nonneg (λ _ _, norm_nonneg _) }
end

lemma abs_integral_le_of_ae_le {f g : ℝ → ℝ}
  (hf : ∀ₘ x, x ∈ [a, b] → 0 ≤ f x) (hfg : ∀ₘ x, x ∈ [a, b] → f x ≤ g x)
  (hgm : measurable_on [a, b] g) (hgi : integrable_on [a, b] g) :
  abs (∫ x in a..b, f x) ≤ abs (∫ x in a..b, g x) :=
begin
  by_cases H : measurable_on [a, b] f ∧ integrable_on [a, b] f,
  { have H1 := H.1, have H2 := H.2,
    split_ifs,
    { simp only [interval_of_le h] at *,
      rw [abs_of_nonneg (integral_on_nonneg_of_ae _), abs_of_nonneg (integral_on_nonneg_of_ae _)],
      { apply integral_on_le_integral_on_ae, assumption' },
      { filter_upwards [hf, hfg] λ a hf hfg h, le_trans (hf h) (hfg h) },
      { filter_upwards [hf] λ a hf, hf } },
    { simp only [interval_of_ge (le_of_not_ge h)] at *,
      rw [abs_of_nonpos, abs_of_nonpos, neg_neg, neg_neg],
      { apply integral_on_le_integral_on_ae, assumption' },
      { rw [neg_nonpos], apply integral_on_nonneg_of_ae,
        filter_upwards [hf, hfg] λ a hf hfg h, le_trans (hf h) (hfg h)  },
      { rw [neg_nonpos], apply integral_on_nonneg_of_ae,
        filter_upwards [hf] λ a hf, hf } } },
  rw [integral_undef H, abs_zero],
  exact abs_nonneg _
end

lemma abs_integral_le_of_le {f g : ℝ → ℝ}
  (hf : ∀ x ∈ [a, b], 0 ≤ f x) (hfg : ∀ x ∈ [a, b], f x ≤ g x)
  (hgm : measurable_on [a, b] g) (hgi : integrable_on [a, b] g) :
  abs (∫ x in a..b, f x) ≤ abs (∫ x in a..b, g x) :=
abs_integral_le_of_ae_le (univ_mem_sets' hf) (univ_mem_sets' hfg) hgm hgi

lemma integral_Icc_combine (hab : a ≤ b) (hbc : b ≤ c)
  (hfm : measurable_on [a, b] f) (hfi : integrable_on [a, b] f)
  (hfm' : measurable_on [b, c] f) (hfi' : integrable_on [b, c] f) :
  (∫ x in Icc a b, f x) + (∫ x in Icc b c, f x) = ∫ x in Icc a c, f x :=
begin
  simp only [interval_of_le hab, interval_of_le hbc] at *,
  have : Icc a c = Icc a b ∪ Icc b c, { rw Icc_union_Icc_eq_Icc; assumption },
  rw [this, integral_on_union_ae],
  assumption',
  repeat { exact is_measurable_Icc },
  rw all_ae_not_mem_iff,
  rw Icc_inter_Icc_eq_singleton hab hbc,
  exact volume_singleton
end

lemma integral_combine
  (hfm : measurable_on [a, b] f) (hfi : integrable_on [a, b] f)
  (hfm' : measurable_on [b, c] f) (hfi' : integrable_on [b, c] f) :
  (∫ x in a..b, f x) + (∫ x in b..c, f x) = ∫ x in a..c, f x :=
begin
  wlog ac : a ≤ c := le_total a c using [a c, c a],
  { have acm : measurable_on [a, c] f := hfm.interval_combine hfm',
    have aci : integrable_on [a, c] f := hfi.interval_combine hfm hfm' hfi',
    split_ifs with ab bc bc,
    { rw [interval_of_le ab, interval_of_le bc, interval_of_le ac],
      exact integral_Icc_combine ab bc hfm hfi hfm' hfi' },
    { rw [add_neg_eq_iff_eq_add, eq_comm],
      have cb : c ≤ b := le_of_not_ge bc,
      rw [interval_of_le ab, interval_of_ge cb, interval_of_le ac],
      refine integral_Icc_combine ac cb acm aci _ _,
      rwa [interval_swap], rwa [interval_swap] },
    { rw [neg_add_eq_iff_eq_add, eq_comm],
      have ba : b ≤ a := le_of_not_ge ab,
      rw [interval_of_ge ba, interval_of_le ac, interval_of_le bc],
      refine integral_Icc_combine ba ac _ _ acm aci,
      rwa [interval_swap], rwa [interval_swap] },
    { have := le_trans ac (le_of_not_ge bc), contradiction }, },
    show (∫ x in a..b, f x) + (∫ x in b..c, f x) = ∫ x in a..c, f x,
    let h := integral_eq_neg_swap,
    rw [h a b, h b c, h a c, ← neg_add, add_comm],
    congr' 1,
    simp only [interval_swap] at *,
    apply this,
    assumption'
end

lemma integral_split_left
  (hfm : measurable_on [a, c] f) (hfi : integrable_on [a, c] f)
  (hfm' : measurable_on [a, b] f) (hfi' : integrable_on [a, b] f) :
  (∫ x in a..c, f x) - (∫ x in a..b, f x) = (∫ x in b..c, f x) :=
begin
  replace hfi : integrable_on [b, c] f := hfi.interval_split_left hfm hfm' hfi',
  replace hfm := hfm.interval_split_left hfm',
  rw [← integral_combine hfm' hfi' hfm hfi, add_sub_cancel']
end

lemma integral_split_right
  (hfm : measurable_on [a, c] f) (hfi : integrable_on [a, c] f)
  (hfm' : measurable_on [b, c] f) (hfi' : integrable_on [b, c] f) :
  (∫ x in a..c, f x) - (∫ x in b..c, f x) = (∫ x in a..b, f x) :=
begin
  replace hfi : integrable_on [a, b] f := hfi.interval_split_right hfm hfm' hfi',
  replace hfm := hfm.interval_split_right hfm',
  rw [← integral_combine hfm hfi hfm' hfi', add_sub_cancel]
end

theorem has_deriv_within_at_integral_of_continuous_within_at (hx : x₀ ∈ [a, b])
  (hfm : measurable_on [a, b] f) (hfi : integrable_on [a, b] f) (hfc : continuous_within_at f [a, b] x₀) :
  has_deriv_within_at (λu, ∫ x in a..u, f x) (f x₀) [a, b] x₀ :=
begin
  simp only [has_deriv_within_at_iff_tendsto_slope, metric.tendsto_nhds_within_nhds,
    continuous_within_at, dist_eq_norm] at *,
  assume ε ε0,
  rcases hfc (ε/2) (half_pos ε0) with ⟨δ, δ0, h⟩,
  refine ⟨δ, δ0, λ y y_mem y_x₀, _⟩,
  have y_mem_ab : y ∈ [a, b] := diff_subset _ _ y_mem,
  have xy_sub_ab : [x₀, y] ⊆ [a, b] := interval_subset_interval hx y_mem_ab,
  have hfm' : measurable_on [x₀, y] f := hfm.subset is_measurable_interval xy_sub_ab,
  have hfi' : integrable_on [x₀, y] f := hfi.subset xy_sub_ab,
  have hm_const : measurable_on [x₀, y] (λ (x : ℝ), f x₀) := measurable_on_const is_measurable_interval,
  have hi_const : integrable_on [x₀, y] (λa, f x₀) := integrable_on_interval_const,
  have y_ne_x : y - x₀ ≠ 0,
    { rw [mem_diff, mem_singleton_iff, ← sub_eq_zero_iff_eq] at y_mem, exact y_mem.2 },
  calc ∥(y - x₀)⁻¹ • ((∫ x in a..y, f x) - ∫ x in a..x₀, f x) - f x₀∥ =
       ∥(y - x₀)⁻¹ • (∫ x in x₀..y, f x) - f x₀∥ :
    by rw integral_split_left (hfm.subinterval_left y_mem_ab) (hfi.subinterval_left y_mem_ab)
      (hfm.subinterval_left hx) (hfi.subinterval_left hx)
    ... = ∥(y - x₀)⁻¹ • (∫ x in x₀..y, f x₀ + (f x - f x₀)) - f x₀∥ :
    by simp only [add_sub_cancel'_right]
    ... = (abs(y - x₀))⁻¹ * ∥(∫ x in x₀..y, f x - f x₀)∥ :
    by rwa [integral_add hm_const hi_const (hfm'.sub hm_const) (hfi'.sub hfm' hm_const hi_const),
          integral_const, smul_add, smul_smul, inv_mul_cancel, one_smul,
          add_sub_cancel', norm_smul, normed_field.norm_inv, real.norm_eq_abs]
    ... ≤ (abs(y - x₀))⁻¹ * abs(∫ x in x₀..y, ε / 2) :
    begin
      rw mul_le_mul_left,
      refine le_trans (norm_integral_le_abs x₀ y _)
        (abs_integral_le_of_le (λ _ _, norm_nonneg _) _ _ _),
      { assume x hx, refine le_of_lt (h (xy_sub_ab hx) _),
        simp only [norm_eq_abs] at *,
        exact lt_of_le_of_lt (abs_sub_left_of_mem_interval hx) y_x₀ },
      { exact measurable_on_const is_measurable_interval },
      { apply integrable_on_interval_const },
      refine inv_pos _,
      rwa abs_pos_iff
    end
    ... < ε :
    begin
      rw [integral_const, smul_eq_mul, abs_mul, ← mul_assoc, inv_mul_cancel, one_mul, abs_of_pos (half_pos ε0)],
      { exact half_lt_self ε0 },
      simpa only [ne.def, abs_eq_zero],
    end
end

end real
