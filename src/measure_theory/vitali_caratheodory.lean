/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import measure_theory.regular
import topology.semicontinuous
import measure_theory.bochner_integration
import topology.instances.ereal

open_locale ennreal nnreal

open measure_theory measure_theory.measure

variables {α : Type*} [topological_space α] [measurable_space α] [borel_space α] (μ : measure α)
  [weakly_regular μ]

namespace measure_theory

local infixr ` →ₛ `:25 := simple_func


/-- Given a measurable function `f` with values in `ℝ≥0`, there exists a lower semicontinuous
function `g ≥ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
lemma simple_func.exists_le_lower_semicontinuous_lintegral_ge :
  ∀ (f : α →ₛ ℝ≥0), ∀ {ε : ℝ≥0∞} (εpos : 0 < ε),
  ∃ g : α → ℝ≥0, (∀ x, f x ≤ g x) ∧ lower_semicontinuous g ∧
    (∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ + ε) :=
begin
  refine simple_func.induction _ _,
  sorry,
  /-{ assume c s hs ε εpos,
    let f := simple_func.piecewise s hs (simple_func.const α c) (simple_func.const α 0),
    by_cases h : ∫⁻ x, f x ∂μ = ⊤,
    { refine ⟨λ x, c, λ x, _, lower_semicontinuous_const,
             by simp only [ennreal.top_add, le_top, h]⟩,
      simp only [simple_func.coe_const, simple_func.const_zero, simple_func.coe_zero,
        set.piecewise_eq_indicator, simple_func.coe_piecewise],
      exact set.indicator_le_self _ _ _ },
    by_cases hc : c = 0,
    { refine ⟨λ x, 0, _, lower_semicontinuous_const, _⟩,
      { simp only [hc, set.indicator_zero', pi.zero_apply, simple_func.const_zero, implies_true_iff,
          eq_self_iff_true, simple_func.coe_zero, set.piecewise_eq_indicator,
          simple_func.coe_piecewise, le_zero_iff] },
      { simp only [lintegral_const, zero_mul, zero_le, ennreal.coe_zero] } },
    have : μ s < μ s + ε / c,
    { have : (0 : ℝ≥0∞) < ε / c := ennreal.div_pos_iff.2 ⟨εpos.ne', ennreal.coe_ne_top⟩,
      simpa using (ennreal.add_lt_add_iff_left _).2 this,
      simpa only [hs, hc, lt_top_iff_ne_top, true_and, simple_func.coe_const, function.const_apply,
        lintegral_const, ennreal.coe_indicator, set.univ_inter, ennreal.coe_ne_top,
        measurable_set.univ, with_top.mul_eq_top_iff, simple_func.const_zero, or_false,
        lintegral_indicator, ennreal.coe_eq_zero, ne.def, not_false_iff, simple_func.coe_zero,
        set.piecewise_eq_indicator, simple_func.coe_piecewise, false_and, restrict_apply] using h },
    obtain ⟨u, u_open, su, μu⟩ : ∃ u, is_open u ∧ s ⊆ u ∧ μ u < μ s + ε / c :=
      hs.exists_is_open_lt_of_lt _ this,
    refine ⟨set.indicator u (λ x, c), λ x, _, u_open.lower_semicontinuous_indicator (zero_le _), _⟩,
    { simp only [simple_func.coe_const, simple_func.const_zero, simple_func.coe_zero,
        set.piecewise_eq_indicator, simple_func.coe_piecewise],
      exact set.indicator_le_indicator_of_subset su (λ x, zero_le _) _ },
    { suffices : (c : ℝ≥0∞) * μ u ≤ c * μ s + ε, by
        simpa only [hs, u_open.measurable_set, simple_func.coe_const, function.const_apply,
          lintegral_const, ennreal.coe_indicator, set.univ_inter, measurable_set.univ,
          simple_func.const_zero, lintegral_indicator, simple_func.coe_zero,
          set.piecewise_eq_indicator, simple_func.coe_piecewise, restrict_apply],
      calc (c : ℝ≥0∞) * μ u ≤ c * (μ s + ε / c) : ennreal.mul_le_mul (le_refl _) μu.le
      ... = c * μ s + ε :
        begin
          simp_rw [mul_add],
          rw ennreal.mul_div_cancel' _ ennreal.coe_ne_top,
          simpa using hc,
        end } },-/

end

#exit


/-- Given a measurable function `f` with values in `ℝ≥0`, there exists a lower semicontinuous
function `g ≥ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
lemma exists_le_lower_semicontinuous_lintegral_ge
  (f : α → ℝ≥0∞) (hf : measurable f) {ε : ℝ≥0∞} (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0∞, (∀ x, f x ≤ g x) ∧ lower_semicontinuous g ∧ (∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ + ε) :=
begin
  by_cases int_f : ∫⁻ x, f x ∂μ = ∞,
  { refine ⟨λ x, ∞, λ x, le_top, lower_semicontinuous_const, by simp [int_f]⟩ },
  sorry
end

#exit

/-- Given a measurable function `f` with values in `ℝ≥0` in a sigma-finite space, there exists a
lower semicontinuous function `g > f` with integral arbitrarily close to that of `f`.
Formulation in terms of `lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
lemma exists_lt_lower_semicontinuous_lintegral_ge [sigma_finite μ]
  (f : α → ℝ≥0) (fmeas : measurable f) {ε : ℝ≥0} (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0∞, (∀ x, (f x : ℝ≥0∞) < g x) ∧ lower_semicontinuous g ∧
    (∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ + ε) :=
begin
  rcases exists_integrable_pos_of_sigma_finite μ (nnreal.half_pos εpos) with ⟨w, wpos, wmeas, wint⟩,
  let f' := λ x, ((f x + w x : ℝ≥0) : ℝ≥0∞),
  rcases exists_le_lower_semicontinuous_lintegral_ge μ f' (fmeas.add wmeas).coe_nnreal_ennreal
    (ennreal.coe_pos.2 (nnreal.half_pos εpos)) with ⟨g, le_g, gcont, gint⟩,
  refine ⟨g, λ x, _, gcont, _⟩,
  { calc (f x : ℝ≥0∞) < f' x : by simpa [← ennreal.coe_lt_coe] using add_lt_add_left (wpos x) (f x)
    ... ≤ g x : le_g x },
  { calc ∫⁻ (x : α), g x ∂μ
        ≤ ∫⁻ (x : α), f x + w x ∂μ + (ε / 2 : ℝ≥0) : gint
    ... = ∫⁻ (x : α), f x ∂ μ + ∫⁻ (x : α), w x ∂ μ + (ε / 2 : ℝ≥0) :
      by rw lintegral_add fmeas.coe_nnreal_ennreal wmeas.coe_nnreal_ennreal
    ... ≤ ∫⁻ (x : α), f x ∂ μ + (ε / 2 : ℝ≥0) + (ε / 2 : ℝ≥0) :
      add_le_add_right (add_le_add_left wint.le _) _
    ... = ∫⁻ (x : α), f x ∂μ + ε : by rw [add_assoc, ← ennreal.coe_add, nnreal.add_halves] },
end

variable {μ}

/-- Given an integrable function `f` with values in `ℝ≥0` in a sigma-finite space, there exists a
lower semicontinuous function `g > f` with integral arbitrarily close to that of `f`.
Formulation in terms of `integral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
lemma exists_lt_lower_semicontinuous_integral_gt_nnreal [sigma_finite μ] (f : α → ℝ≥0)
  (fmeas : measurable f) (fint : integrable (λ x, (f x : ℝ)) μ) {ε : ℝ} (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0∞, (∀ x, (f x : ℝ≥0∞) < g x) ∧ lower_semicontinuous g ∧ (∀ᵐ x ∂ μ, g x < ⊤)
  ∧ (integrable (λ x, (g x).to_real) μ) ∧ (∫ x, (g x).to_real ∂μ < ∫ x, f x ∂μ + ε) :=
begin
  let δ : ℝ≥0 := ⟨ε/2, (half_pos εpos).le⟩,
  have δpos : 0 < δ := half_pos εpos,
  have int_f_lt_top : ∫⁻ (a : α), (f a) ∂μ < ⊤ :=
    has_finite_integral_iff_of_nnreal.1 fint.has_finite_integral,
  rcases exists_lt_lower_semicontinuous_lintegral_ge μ f fmeas δpos with ⟨g, f_lt_g, gcont, gint⟩,
  have gint_lt : ∫⁻ (x : α), g x ∂μ < ∞ := calc
    ∫⁻ (x : α), g x ∂μ ≤ ∫⁻ (x : α), ↑(f x) ∂μ + δ : gint
      ... < ⊤ : by simpa using int_f_lt_top,
  have g_lt_top : ∀ᵐ (x : α) ∂μ, g x < ⊤ := ae_lt_top gcont.measurable gint_lt,
  have Ig : ∫⁻ (a : α), ennreal.of_real (g a).to_real ∂μ = ∫⁻ (a : α), g a ∂μ,
  { apply lintegral_congr_ae,
    filter_upwards [g_lt_top],
    assume x hx,
    simp only [hx.ne, ennreal.of_real_to_real, ne.def, not_false_iff] },
  refine ⟨g, f_lt_g, gcont, g_lt_top, _, _⟩,
  { refine ⟨gcont.measurable.ennreal_to_real.ae_measurable, _⟩,
    simp [has_finite_integral_iff_norm, real.norm_eq_abs, abs_of_nonneg],
    convert gint_lt using 1 },
  { rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae],
    { calc
      ennreal.to_real (∫⁻ (a : α), ennreal.of_real (g a).to_real ∂μ)
          = ennreal.to_real (∫⁻ (a : α), g a ∂μ) : by congr' 1
      ... ≤ ennreal.to_real (∫⁻ (a : α), f a ∂μ + δ) :
        begin
          apply ennreal.to_real_mono _ gint,
          simpa using int_f_lt_top.ne,
        end
      ... = ennreal.to_real (∫⁻ (a : α), f a ∂μ) + δ :
        by rw [ennreal.to_real_add int_f_lt_top.ne ennreal.coe_ne_top, ennreal.coe_to_real]
      ... < ennreal.to_real (∫⁻ (a : α), f a ∂μ) + ε :
        add_lt_add_left (by simp [δ, half_lt_self εpos]) _
      ... = (∫⁻ (a : α), ennreal.of_real ↑(f a) ∂μ).to_real + ε :
        by simp },
    { apply filter.eventually_of_forall (λ x, _), simp },
    { exact fmeas.coe_nnreal_real.ae_measurable, },
    { apply filter.eventually_of_forall (λ x, _), simp },
    { apply gcont.measurable.ennreal_to_real.ae_measurable } }
end

/-- Given an integrable function `f` with values in `ℝ≥0`, there exists an upper semicontinuous
function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
lemma exists_upper_semicontinuous_le_lintegral_le
  (f : α → ℝ≥0) (hf : measurable f) (int_f : ∫⁻ x, f x ∂μ < ∞) {ε : ℝ≥0} (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0, (∀ x, g x ≤ f x) ∧ upper_semicontinuous g ∧ (∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x ∂μ + ε) :=
begin
  sorry
end

/-- Given an integrable function `f` with values in `ℝ≥0`, there exists an upper semicontinuous
function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`integral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
lemma exists_upper_semicontinuous_le_integral_le (f : α → ℝ≥0) (hf : measurable f)
  (fint : integrable (λ x, (f x : ℝ)) μ) {ε : ℝ} (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0, (∀ x, g x ≤ f x) ∧ upper_semicontinuous g ∧ (integrable (λ x, (g x : ℝ)) μ)
  ∧ (∫ x, (f x : ℝ) ∂μ - ε ≤ ∫ x, g x ∂μ) :=
begin
  let δ : ℝ≥0 := ⟨ε, εpos.le⟩,
  have δpos : 0 < δ := εpos,
  have If : ∫⁻ x, f x ∂ μ < ∞ := has_finite_integral_iff_of_nnreal.1 fint.has_finite_integral,
  rcases exists_upper_semicontinuous_le_lintegral_le f hf If δpos with ⟨g, gf, gcont, gint⟩,
  have Ig : ∫⁻ x, g x ∂ μ < ∞,
  { apply lt_of_le_of_lt (lintegral_mono (λ x, _)) If,
    simpa using gf x },
  refine ⟨g, gf, gcont, _, _⟩,
  { refine integrable.mono fint gcont.measurable.coe_nnreal_real.ae_measurable _,
    exact filter.eventually_of_forall (λ x, by simp [gf x]) },
  { rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae],
    { rw sub_le_iff_le_add,
      convert ennreal.to_real_mono _ gint,
      { simp, },
      { rw ennreal.to_real_add Ig.ne ennreal.coe_ne_top, simp },
      { simpa using Ig.ne } },
    { apply filter.eventually_of_forall, simp },
    { exact gcont.measurable.coe_nnreal_real.ae_measurable },
    { apply filter.eventually_of_forall, simp },
    { exact hf.coe_nnreal_real.ae_measurable } }
end

/-- Vitali-Carathéodory theorem: given an integrable real function `f`, there exists an integrable
function `g > f` which is lower semicontinuous, with integral arbitrarily close to that of `f`.
This function has to be `ereal`-valued in general. -/
lemma exists_lt_lower_semicontinuous_integral_lt [sigma_finite μ]
  (f : α → ℝ) (fmeas : measurable f) (hf : integrable f μ) (ε : ℝ) (εpos : 0 < ε) :
  ∃ g : α → ereal, (∀ x, (f x : ereal) < g x) ∧ lower_semicontinuous g ∧
  (integrable (λ x, ereal.to_real (g x)) μ) ∧ (∀ᵐ x ∂ μ, g x < ⊤) ∧
  (∫ x, ereal.to_real (g x) ∂μ < ∫ x, f x ∂μ + ε) :=
begin
  let δ : ℝ≥0 := ⟨ε/2, (half_pos εpos).le⟩,
  have δpos : 0 < δ := half_pos εpos,
  let fp : α → ℝ≥0 := λ x, real.to_nnreal (f x),
  have int_fp : integrable (λ x, (fp x : ℝ)) μ := hf.real_to_nnreal,
  rcases exists_lt_lower_semicontinuous_integral_gt_nnreal fp fmeas.real_to_nnreal int_fp δpos with
    ⟨gp, fp_lt_gp, gpcont, gp_lt_top, gp_integrable, gpint⟩,
  let fm : α → ℝ≥0 := λ x, real.to_nnreal (-f x),
  have int_fm : integrable (λ x, (fm x : ℝ)) μ := hf.neg.real_to_nnreal,
  rcases exists_upper_semicontinuous_le_integral_le fm fmeas.neg.real_to_nnreal int_fm δpos with
    ⟨gm, gm_le_fm, gmcont, gm_integrable, gmint⟩,
  let g : α → ereal := λ x, (gp x : ereal) - (gm x),
  have ae_g : ∀ᵐ x ∂ μ, (g x).to_real = (gp x : ereal).to_real - (gm x : ereal).to_real,
  { filter_upwards [gp_lt_top],
    assume x hx,
    rw ereal.to_real_sub;
    simp [hx.ne] },
  refine ⟨g, _, _, _, _, _⟩,
  show integrable (λ x, ereal.to_real (g x)) μ,
  { rw integrable_congr ae_g,
    convert gp_integrable.sub gm_integrable,
    ext x,
    simp },
  show ∫ (x : α), (g x).to_real ∂μ < ∫ (x : α), f x ∂μ + ε, from calc
    ∫ (x : α), (g x).to_real ∂μ = ∫ (x : α), ereal.to_real (gp x) - ereal.to_real (gm x) ∂μ :
      integral_congr_ae ae_g
    ... = ∫ (x : α), ereal.to_real (gp x) ∂ μ - ∫ (x : α), gm x ∂μ :
      begin
        simp only [ereal.to_real_coe_ennreal, ennreal.coe_to_real, coe_coe],
        exact integral_sub gp_integrable gm_integrable,
      end
    ... < ∫ (x : α), ↑(fp x) ∂μ + ↑δ - ∫ (x : α), gm x ∂μ :
      begin
        apply sub_lt_sub_right,
        convert gpint,
        simp only [ereal.to_real_coe_ennreal],
      end
    ... ≤ ∫ (x : α), ↑(fp x) ∂μ + ↑δ - (∫ (x : α), fm x ∂μ - δ) :
      sub_le_sub_left gmint _
    ... = ∫ (x : α), f x ∂μ + 2 * δ :
      by { simp_rw [integral_eq_integral_pos_part_sub_integral_neg_part hf, fp, fm], ring }
    ... = ∫ (x : α), f x ∂μ + ε :
      by { congr' 1, field_simp [δ, mul_comm] },
  show ∀ᵐ (x : α) ∂μ, g x < ⊤,
  { filter_upwards [gp_lt_top],
    assume x hx,
    simp [g, ereal.sub_eq_add_neg, lt_top_iff_ne_top, lt_top_iff_ne_top.1 hx] },
  show ∀ x, (f x : ereal) < g x,
  { assume x,
    rw ereal.coe_real_ereal_eq_coe_to_nnreal_sub_coe_to_nnreal (f x),
    refine ereal.sub_lt_sub_of_lt_of_le _ _ _ _,
    { simp only [ereal.coe_ennreal_lt_coe_ennreal_iff, coe_coe], exact (fp_lt_gp x) },
    { simp only [ennreal.coe_le_coe, ereal.coe_ennreal_le_coe_ennreal_iff, coe_coe],
      exact (gm_le_fm x) },
    { simp only [ereal.coe_ennreal_ne_bot, ne.def, not_false_iff, coe_coe] },
    { simp only [ereal.coe_nnreal_ne_top, ne.def, not_false_iff, coe_coe] } },
  show lower_semicontinuous g,
  { apply lower_semicontinuous.add',
    { exact continuous_coe_ennreal_ereal.comp_lower_semicontinuous gpcont
        (λ x y hxy, ereal.coe_ennreal_le_coe_ennreal_iff.2 hxy) },
    { apply ereal.continuous_neg.comp_upper_semicontinuous_antimono _
        (λ x y hxy, ereal.neg_le_neg_iff.2 hxy),
      dsimp,
      apply continuous_coe_ennreal_ereal.comp_upper_semicontinuous _
        (λ x y hxy, ereal.coe_ennreal_le_coe_ennreal_iff.2 hxy),
      exact ennreal.continuous_coe.comp_upper_semicontinuous gmcont
        (λ x y hxy, ennreal.coe_le_coe.2 hxy) },
    { assume x,
      exact ereal.continuous_at_add (by simp) (by simp) } }
end

end measure_theory
