/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich
-/
import measure_theory.integral.lebesgue
import probability_theory.independence

/-!
# Integration in Probability Theory

Integration results for independent random variables. Specifically, for two
independent random variables X and Y over the extended non-negative
reals, `E[X * Y] = E[X] * E[Y]`, and similar results.

## Implementation notes

Many lemmas in this file take two arguments of the same typeclass. It is worth remembering that lean
will always pick the later typeclass in this situation, and does not care whether the arguments are
`[]`, `{}`, or `()`. All of these use the `measurable_space` `M2` to define `μ`:

```lean
example {M1 : measurable_space α} [M2 : measurable_space α] {μ : measure α} : sorry := sorry
example [M1 : measurable_space α] {M2 : measurable_space α} {μ : measure α} : sorry := sorry
```

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
  {Mf : measurable_space α} [M : measurable_space α] {μ : measure α} (hMf : Mf ≤ M)
  (c : ℝ≥0∞) {T : set α} (h_meas_T : measurable_set T)
  (h_ind : indep_sets Mf.measurable_set' {T} μ)
  {f : α → ℝ≥0∞} (h_meas_f : @measurable α ℝ≥0∞ Mf _ f) :
  ∫⁻ a, f a * T.indicator (λ _, c) a ∂μ = ∫⁻ a, f a ∂μ * ∫⁻ a, T.indicator (λ _, c) a ∂μ :=
begin
  revert f,
  have h_mul_indicator : ∀ g, measurable g → measurable (λ a, g a * T.indicator (λ x, c) a),
    from λ g h_mg, h_mg.mul (measurable_const.indicator h_meas_T),
  apply measurable.ennreal_induction,
  { intros c' s' h_meas_s',
    simp_rw [← inter_indicator_mul],
    rw [lintegral_indicator _ (measurable_set.inter (hMf _ h_meas_s') (h_meas_T)),
      lintegral_indicator _ (hMf _ h_meas_s'), lintegral_indicator _ h_meas_T],
    simp only [measurable_const, lintegral_const, univ_inter, lintegral_const_mul,
      measurable_set.univ, measure.restrict_apply],
    ring_nf,
    congr,
    rw [mul_comm, h_ind s' T h_meas_s' (set.mem_singleton _)], },
  { intros f' g h_univ h_meas_f' h_meas_g h_ind_f' h_ind_g,
    have h_measM_f' : measurable f', from h_meas_f'.mono hMf le_rfl,
    have h_measM_g : measurable g, from h_meas_g.mono hMf le_rfl,
    simp_rw [pi.add_apply, right_distrib],
    rw [lintegral_add (h_mul_indicator _ h_measM_f') (h_mul_indicator _ h_measM_g),
      lintegral_add h_measM_f' h_measM_g, right_distrib, h_ind_f', h_ind_g] },
  { intros f h_meas_f h_mono_f h_ind_f,
    have h_measM_f : ∀ n, measurable (f n), from λ n, (h_meas_f n).mono hMf le_rfl,
    simp_rw [ennreal.supr_mul],
    rw [lintegral_supr h_measM_f h_mono_f, lintegral_supr, ennreal.supr_mul],
    { simp_rw [← h_ind_f] },
    { exact λ n, h_mul_indicator _ (h_measM_f n) },
    { exact λ m n h_le a, ennreal.mul_le_mul (h_mono_f h_le a) le_rfl, }, },
end

/-- This (roughly) proves that if `f` and `g` are independent random variables,
   then `E[f * g] = E[f] * E[g]`. However, instead of directly using the independence
   of the random variables, it uses the independence of measurable spaces for the
   domains of `f` and `g`. This is similar to the sigma-algebra approach to
   independence. See `lintegral_mul_eq_lintegral_mul_lintegral_of_independent_fn` for
   a more common variant of the product of independent variables. -/
lemma lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space
  {Mf Mg : measurable_space α} [M : measurable_space α] {μ : measure α}
  (hMf : Mf ≤ M) (hMg : Mg ≤ M) (h_ind : indep Mf Mg μ) {f g : α → ℝ≥0∞}
  (h_meas_f : @measurable α ℝ≥0∞ Mf _ f) (h_meas_g : @measurable α ℝ≥0∞ Mg _ g) :
  ∫⁻ a, f a * g a ∂μ = ∫⁻ a, f a ∂μ * ∫⁻ a, g a ∂μ :=
begin
  revert g,
  have h_measM_f : measurable f, from h_meas_f.mono hMf le_rfl,
  apply measurable.ennreal_induction,
  { intros c s h_s,
    apply lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator hMf _ (hMg _ h_s) _ h_meas_f,
    apply indep_sets_of_indep_sets_of_le_right h_ind,
    rwa singleton_subset_iff, },
  { intros f' g h_univ h_measMg_f' h_measMg_g h_ind_f' h_ind_g',
    have h_measM_f' : measurable f', from h_measMg_f'.mono hMg le_rfl,
    have h_measM_g : measurable g, from h_measMg_g.mono hMg le_rfl,
    simp_rw [pi.add_apply, left_distrib],
    rw [lintegral_add h_measM_f' h_measM_g,
      lintegral_add (h_measM_f.mul h_measM_f') (h_measM_f.mul h_measM_g),
      left_distrib, h_ind_f', h_ind_g'] },
  { intros f' h_meas_f' h_mono_f' h_ind_f',
    have h_measM_f' : ∀ n, measurable (f' n), from λ n, (h_meas_f' n).mono hMg le_rfl,
    simp_rw [ennreal.mul_supr],
    rw [lintegral_supr, lintegral_supr h_measM_f' h_mono_f', ennreal.mul_supr],
    { simp_rw [← h_ind_f'], },
    { exact λ n, h_measM_f.mul (h_measM_f' n), },
    { exact λ n m (h_le : n ≤ m) a, ennreal.mul_le_mul le_rfl (h_mono_f' h_le a), }, }
end

/-- This proves that if `f` and `g` are independent random variables,
   then `E[f * g] = E[f] * E[g]`. -/
lemma lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun [measurable_space α] {μ : measure α}
  {f g : α → ℝ≥0∞} (h_meas_f : measurable f) (h_meas_g : measurable g)
  (h_indep_fun : indep_fun f g μ) :
  ∫⁻ a, (f * g) a ∂μ = ∫⁻ a, f a ∂μ * ∫⁻ a, g a ∂μ :=
lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space
  (measurable_iff_comap_le.1 h_meas_f) (measurable_iff_comap_le.1 h_meas_g) h_indep_fun
  (measurable.of_comap_le le_rfl) (measurable.of_comap_le le_rfl)

end probability_theory
