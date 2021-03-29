/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich
-/
import measure_theory.integration
import probability_theory.independence

/-!
# Integration in Probability Theory

Integration results for independent random variables. Specifically, for two
independent random variables X and Y over the extended non-negative
reals, `E[X * Y] = E[X] * E[Y]`, and similar results.
-/

noncomputable theory
open set measure_theory
open_locale ennreal

variables {α : Type*}

namespace probability_theory

/-- This (roughly) proves that if a random variable `f` is independent of an event `T`,
   then if you restrict the random variable to `T`, then
   `E[f * indicator T c 0]=E[f] * E[indicator T c 0]`. It is useful for
   `lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space`. -/
lemma lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator
  {Mf : measurable_space α} [M : measurable_space α] {μ : measure α}
  (hMf : Mf ≤ M) (c : ℝ≥0∞) {T : set α} (h_meas_T : M.measurable_set' T)
  (h_ind : indep_sets Mf.measurable_set' {T} μ)
  {f : α → ℝ≥0∞} (h_meas_f : @measurable α ℝ≥0∞ Mf _ f) :
  ∫⁻ a, f a * T.indicator (λ _, c) a ∂μ =
  ∫⁻ a, f a ∂μ * ∫⁻ a, T.indicator (λ _, c) a ∂μ :=
begin
  revert f,
  have h_mul_indicator : ∀ g, measurable g → measurable (λ a, g a * T.indicator (λ x, c) a) :=
  λ g h_mg, h_mg.mul (measurable_const.indicator h_meas_T),
  apply measurable.ennreal_induction,
  { intros c' s' h_meas_s',
    simp_rw [← inter_indicator_mul],
    rw [lintegral_indicator _ (measurable_set.inter (hMf _ h_meas_s') (h_meas_T)),
        lintegral_indicator _ (hMf _ h_meas_s'),
        lintegral_indicator _ h_meas_T],
    simp only [measurable_const, lintegral_const, univ_inter, lintegral_const_mul,
        measurable_set.univ, measure.restrict_apply],
    rw h_ind, { ring }, { apply h_meas_s' }, { simp } },
  { intros f' g h_univ h_meas_f' h_meas_g h_ind_f' h_ind_g,
    have h_measM_f' := h_meas_f'.mono hMf le_rfl,
    have h_measM_g := h_meas_g.mono hMf le_rfl,
    simp_rw [pi.add_apply, right_distrib],
    rw [lintegral_add (h_mul_indicator _ h_measM_f') (h_mul_indicator _ h_measM_g),
        lintegral_add h_measM_f' h_measM_g, right_distrib, h_ind_f', h_ind_g] },
  { intros f h_meas_f h_mono_f h_ind_f,
    have h_measM_f := λ n, (h_meas_f n).mono hMf le_rfl,
    simp_rw [ennreal.supr_mul],
    rw [lintegral_supr h_measM_f h_mono_f, lintegral_supr, ennreal.supr_mul],
    { simp_rw [← h_ind_f] },
    { exact λ n, h_mul_indicator _ (h_measM_f n) },
    { intros m n h_le a, apply ennreal.mul_le_mul _ le_rfl, apply h_mono_f h_le } },
end

/-- This (roughly) proves that if `f` and `g` are independent random variables,
   then `E[f * g] = E[f] * E[g]`. However, instead of directly using the independence
   of the random variables, it uses the independence of measurable spaces for the
   domains of `f` and `g`. This is similar to the sigma-algebra approach to
   independence. See `lintegral_mul_eq_lintegral_mul_lintegral_of_independent_fn` for
   a more common variant of the product of independent variables. -/
lemma lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space
  {Mf : measurable_space α} {Mg : measurable_space α} [M : measurable_space α]
  {μ : measure α} (hMf : Mf ≤ M) (hMg : Mg ≤ M)
  (h_ind : indep Mf Mg μ)
  (f g : α → ℝ≥0∞) (h_meas_f : @measurable α ℝ≥0∞ Mf _ f)
  (h_meas_g : @measurable α ℝ≥0∞ Mg _ g) :
  ∫⁻ a, f a * g a ∂μ = ∫⁻ a, f a ∂μ * ∫⁻ a, g a ∂μ :=
begin
  revert g,
  have h_meas_Mg : ∀ ⦃f : α → ℝ≥0∞⦄, @measurable α ℝ≥0∞ Mg _ f → measurable f,
  { intros f' h_meas_f', apply h_meas_f'.mono hMg le_rfl },
  have h_measM_f := h_meas_f.mono hMf le_rfl,
  apply measurable.ennreal_induction,
  { intros c s h_s,
    apply lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator hMf _ (hMg _ h_s) _ h_meas_f,
    apply probability_theory.indep_sets_of_indep_sets_of_le_right h_ind,
    rw singleton_subset_iff, apply h_s },
  { intros f' g h_univ h_measMg_f' h_measMg_g h_ind_f' h_ind_g',
    have h_measM_f' := h_meas_Mg h_measMg_f',
    have h_measM_g := h_meas_Mg h_measMg_g,
    simp_rw [pi.add_apply, left_distrib],
    rw [lintegral_add h_measM_f' h_measM_g,
        lintegral_add (h_measM_f.mul h_measM_f') (h_measM_f.mul h_measM_g),
        left_distrib, h_ind_f', h_ind_g'] },
  { intros f' h_meas_f' h_mono_f' h_ind_f',
    have h_measM_f' := λ n, h_meas_Mg (h_meas_f' n),
    simp_rw [ennreal.mul_supr],
    rw [lintegral_supr, lintegral_supr h_measM_f' h_mono_f', ennreal.mul_supr],
    { simp_rw [← h_ind_f'] },
    { apply λ (n : ℕ), h_measM_f.mul (h_measM_f' n) },
    { apply λ (n : ℕ) (m : ℕ) (h_le : n ≤ m) a, ennreal.mul_le_mul le_rfl
      (h_mono_f' h_le a) } }
end

/-- This proves that if `f` and `g` are independent random variables,
   then `E[f * g] = E[f] * E[g]`. -/
lemma lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun [M : measurable_space α]
  (μ : measure α) (f g : α → ℝ≥0∞) (h_meas_f : measurable f) (h_meas_g : measurable g)
  (h_indep_fun : indep_fun (borel ennreal) (borel ennreal) f g μ) :
  ∫⁻ (a : α), (f * g) a ∂μ = ∫⁻ (a : α), f a ∂μ * ∫⁻ (a : α), g a ∂μ :=
begin
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space
    (measurable_iff_comap_le.1 h_meas_f) (measurable_iff_comap_le.1 h_meas_g),
  apply h_indep_fun,
  repeat { apply measurable.of_comap_le le_rfl },
end

end probability_theory
