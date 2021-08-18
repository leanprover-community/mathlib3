/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import measure_theory.integral.set_integral
import analysis.calculus.mean_value

/-!
# Derivatives of integrals depending on parameters

A parametric integral is a function with shape `f = λ x : H, ∫ a : α, F x a ∂μ` for some
`F : H → α → E`, where `H` and `E` are normed spaces and `α` is a measured space with measure `μ`.

We already know from `continuous_of_dominated` in `measure_theory.bochner_integral` how to
guarantee that `f` is continuous using the dominated convergence theorem. In this file,
we want to express the derivative of `f` as the integral of the derivative of `F` with respect
to `x`.


## Main results

As explained above, all results express the derivative of a parametric integral as the integral of
a derivative. The variations come from the assumptions and from the different ways of expressing
derivative, especially Fréchet derivatives vs elementary derivative of function of one real
variable.

* `has_fderiv_at_of_dominated_loc_of_lip`: this version assumes
    `F x` is ae-measurable for x near `x₀`, `F x₀` is integrable,
    `λ x, F x a` has derivative `F' a : H →L[ℝ] E` at `x₀` which is ae-measurable,
    `λ x, F x a` is locally Lipschitz near `x₀` for almost every `a`, with a Lipschitz bound which
    is integrable with respect to `a`. A subtle point is that the "near x₀" in the last condition
    has to be uniform in `a`. This is controlled by a positive number `ε`.

* `has_fderiv_at_of_dominated_of_fderiv_le`: this version assume `λ x, F x a` has derivative
    `F' x a` for `x` near `x₀` and `F' x` is bounded by an integrable function independent from
    `x` near `x₀`.


`has_deriv_at_of_dominated_loc_of_lip` and `has_deriv_at_of_dominated_loc_of_deriv_le ` are versions
of the above two results that assume `H = ℝ` and use the high-school derivative `deriv` instead of
Fréchet derivative `fderiv`.
-/

noncomputable theory

open topological_space measure_theory filter metric
open_locale topological_space filter

variables {α : Type*} [measurable_space α] {μ : measure α}
          {E : Type*} [normed_group E] [normed_space ℝ E]
          [complete_space E] [second_countable_topology E]
          [measurable_space E] [borel_space E]
          {H : Type*} [normed_group H] [normed_space ℝ H]
          [second_countable_topology $ H →L[ℝ] E]

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a ball around `x₀` for ae `a` with
integrable Lipschitz bound (with a ball radius independent of `a`), and `F x` is
ae-measurable for `x` in the same ball. See `has_fderiv_at_of_dominated_loc_of_lip` for a
slightly more general version. -/
lemma has_fderiv_at_of_dominated_loc_of_lip' {F : H → α → E} {F' : α → (H →L[ℝ] E)} {x₀ : H}
  {bound : α → ℝ}
  {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ x ∈ ball x₀ ε, ae_measurable (F x) μ)
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : ae_measurable F' μ)
  (h_lipsch : ∀ᵐ a ∂μ, lipschitz_on_with (real.nnabs $ bound a) (λ x, F x a) (ball x₀ ε))
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐ a ∂μ, has_fderiv_at (λ x, F x a) (F' a) x₀) :
  integrable F' μ ∧ has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ :=
begin
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos,
  have nneg : ∀ x, 0 ≤ ∥x - x₀∥⁻¹ := λ x, inv_nonneg.mpr (norm_nonneg _) ,
  set b : α → ℝ := λ a, abs (bound a),
  have b_int : integrable b μ := bound_integrable.norm,
  have b_nonneg : ∀ a, 0 ≤ b a := λ a, abs_nonneg _,
  have hF_int' : ∀ x ∈ ball x₀ ε, integrable (F x) μ,
  { intros x x_in,
    have : ∀ᵐ a ∂μ, ∥F x₀ a - F x a∥ ≤ ε * ∥(bound a : ℝ)∥,
    { apply h_lipsch.mono,
      intros a ha,
      rw lipschitz_on_with_iff_norm_sub_le at ha,
      apply (ha x₀ x₀_in x x_in).trans,
      rw [mul_comm, nnreal.coe_nnabs, real.norm_eq_abs],
      rw [mem_ball, dist_eq_norm, norm_sub_rev] at x_in,
      exact mul_le_mul_of_nonneg_right (le_of_lt x_in) (abs_nonneg  _) },
    exact integrable_of_norm_sub_le (hF_meas x x_in) hF_int
      (integrable.const_mul bound_integrable.norm ε) this },
  have hF'_int : integrable F' μ,
  { have : ∀ᵐ a ∂μ, ∥F' a∥ ≤ b a,
    { apply (h_diff.and h_lipsch).mono,
      rintros a ⟨ha_diff, ha_lip⟩,
      exact ha_diff.le_of_lip (ball_mem_nhds _ ε_pos) ha_lip },
    exact b_int.mono' hF'_meas this },
  refine ⟨hF'_int, _⟩,
  have h_ball: ball x₀ ε ∈ 𝓝 x₀ := ball_mem_nhds x₀ ε_pos,
  have : ∀ᶠ x in 𝓝 x₀,
      ∥x - x₀∥⁻¹ * ∥∫ a, F x a ∂μ - ∫ a, F x₀ a ∂μ - (∫ a, F' a ∂μ) (x - x₀)∥ =
       ∥∫ a, ∥x - x₀∥⁻¹ • (F x a - F x₀ a  - F' a (x - x₀)) ∂μ∥,
  { apply mem_of_superset (ball_mem_nhds _ ε_pos),
    intros x x_in,
    rw [set.mem_set_of_eq, ← norm_smul_of_nonneg (nneg _), integral_smul,
        integral_sub, integral_sub, ← continuous_linear_map.integral_apply hF'_int],
    exacts [hF_int' x x_in, hF_int, (hF_int' x x_in).sub hF_int,
            hF'_int.apply_continuous_linear_map _] },
  rw [has_fderiv_at_iff_tendsto, tendsto_congr' this, ← tendsto_zero_iff_norm_tendsto_zero,
      ← show ∫ (a : α), ∥x₀ - x₀∥⁻¹ • (F x₀ a - F x₀ a - (F' a) (x₀ - x₀)) ∂μ = 0, by simp],
  apply tendsto_integral_filter_of_dominated_convergence,
  { apply is_countably_generated_nhds },
  { filter_upwards [h_ball],
    intros x x_in,
    apply ae_measurable.const_smul,
    exact ((hF_meas _ x_in).sub (hF_meas _ x₀_in)).sub (hF'_meas.apply_continuous_linear_map _) },
  { simp [measurable_const] },
  { apply mem_of_superset h_ball,
    intros x hx,
    apply (h_diff.and h_lipsch).mono,
    rintros a ⟨ha_deriv, ha_bound⟩,
    show ∥∥x - x₀∥⁻¹ • (F x a - F x₀ a - F' a (x - x₀))∥ ≤ b a + ∥F' a∥,
    replace ha_bound : ∥F x a - F x₀ a∥ ≤ b a * ∥x - x₀∥,
    { rw lipschitz_on_with_iff_norm_sub_le at ha_bound,
      exact ha_bound _ hx _ x₀_in },
    calc ∥∥x - x₀∥⁻¹ • (F x a - F x₀ a - F' a (x - x₀))∥
    = ∥∥x - x₀∥⁻¹ • (F x a - F x₀ a) - ∥x - x₀∥⁻¹ • F' a (x - x₀)∥ : by rw smul_sub
    ... ≤  ∥∥x - x₀∥⁻¹ • (F x a - F x₀ a)∥ + ∥∥x - x₀∥⁻¹ • F' a (x - x₀)∥ : norm_sub_le _ _
    ... =  ∥x - x₀∥⁻¹ * ∥F x a - F x₀ a∥ + ∥x - x₀∥⁻¹ * ∥F' a (x - x₀)∥ :
                                 by { rw [norm_smul_of_nonneg, norm_smul_of_nonneg] ; exact nneg _}
    ... ≤  ∥x - x₀∥⁻¹ * (b a * ∥x - x₀∥) + ∥x - x₀∥⁻¹ * (∥F' a∥ * ∥x - x₀∥) : add_le_add _ _
    ... ≤ b a + ∥F' a∥ : _,
    exact mul_le_mul_of_nonneg_left ha_bound (nneg _),
    apply mul_le_mul_of_nonneg_left ((F' a).le_op_norm _) (nneg _),
    by_cases h : ∥x - x₀∥ = 0,
    { simpa [h] using add_nonneg (b_nonneg a) (norm_nonneg (F' a)) },
    { field_simp [h] } },
  { exact b_int.add hF'_int.norm },
  { apply h_diff.mono,
    intros a ha,
    suffices : tendsto (λ x, ∥x - x₀∥⁻¹ • (F x a - F x₀ a - F' a (x - x₀))) (𝓝 x₀) (𝓝 0),
    by simpa,
    rw tendsto_zero_iff_norm_tendsto_zero,
    have : (λ x, ∥x - x₀∥⁻¹ * ∥F x a - F x₀ a - F' a (x - x₀)∥) =
            λ x, ∥∥x - x₀∥⁻¹ • (F x a - F x₀ a - F' a (x - x₀))∥,
    { ext x,
      rw norm_smul_of_nonneg (nneg _) },
    rwa [has_fderiv_at_iff_tendsto, this] at ha },
end

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a ball around `x₀` for ae `a`
(with a ball radius independent of `a`) with integrable Lipschitz bound, and `F x` is ae-measurable
for `x` in a possibly smaller neighborhood of `x₀`. -/
lemma has_fderiv_at_of_dominated_loc_of_lip {F : H → α → E} {F' : α → (H →L[ℝ] E)} {x₀ : H}
  {bound : α → ℝ}
  {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) μ)
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : ae_measurable F' μ)
  (h_lip : ∀ᵐ a ∂μ, lipschitz_on_with (real.nnabs $ bound a) (λ x, F x a) (ball x₀ ε))
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐ a ∂μ, has_fderiv_at (λ x, F x a) (F' a) x₀) :
  integrable F' μ ∧ has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ :=
begin
  obtain ⟨ε', ε'_pos, h'⟩ : ∃ ε' > 0, ∀ x ∈ ball x₀ ε', ae_measurable (F x) μ,
  by simpa using nhds_basis_ball.eventually_iff.mp hF_meas,
  set δ := min ε ε',
  have δ_pos : 0 < δ := lt_min ε_pos ε'_pos,
  replace h' : ∀ x, x ∈ ball x₀ δ → ae_measurable (F x) μ,
  { intros x x_in,
    exact h' _ (ball_subset_ball (min_le_right ε ε') x_in) },
  replace h_lip : ∀ᵐ (a : α) ∂μ, lipschitz_on_with (real.nnabs $ bound a) (λ x, F x a) (ball x₀ δ),
  { apply h_lip.mono,
    intros a lip,
    exact lip.mono (ball_subset_ball $ min_le_left ε ε') },
  apply has_fderiv_at_of_dominated_loc_of_lip' δ_pos ; assumption
end

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is differentiable on a ball around `x₀` for ae `a` with
derivative norm uniformly bounded by an integrable function (the ball radius is independent of `a`),
and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
lemma has_fderiv_at_of_dominated_of_fderiv_le {F : H → α → E} {F' : H → α → (H →L[ℝ] E)} {x₀ : H}
  {bound : α → ℝ}
  {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) μ)
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : ae_measurable (F' x₀) μ)
  (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ∥F' x a∥ ≤ bound a)
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, has_fderiv_at (λ x, F x a) (F' x a) x) :
  has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ :=
begin
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos,
  have diff_x₀ : ∀ᵐ a ∂μ, has_fderiv_at (λ x, F x a) (F' x₀ a) x₀ :=
    h_diff.mono (λ a ha, ha x₀ x₀_in),
  have : ∀ᵐ a ∂μ, lipschitz_on_with (real.nnabs (bound a)) (λ x, F x a) (ball x₀ ε),
  { apply (h_diff.and h_bound).mono,
    rintros a ⟨ha_deriv, ha_bound⟩,
    refine (convex_ball _ _).lipschitz_on_with_of_nnnorm_has_fderiv_within_le
      (λ x x_in, (ha_deriv x x_in).has_fderiv_within_at) (λ x x_in, _),
    rw [← nnreal.coe_le_coe, coe_nnnorm, nnreal.coe_nnabs],
    exact (ha_bound x x_in).trans (le_abs_self _) },
  exact (has_fderiv_at_of_dominated_loc_of_lip ε_pos hF_meas hF_int
                                               hF'_meas this bound_integrable diff_x₀).2
end

/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : ℝ`, assuming
`F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on an interval around `x₀` for ae `a`
(with interval radius independent of `a`) with integrable Lipschitz bound, and `F x` is
ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
lemma has_deriv_at_of_dominated_loc_of_lip {F : ℝ → α → E} {F' : α → E} {x₀ : ℝ}
  {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) μ)
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : ae_measurable F' μ) {bound : α → ℝ}
  (h_lipsch : ∀ᵐ a ∂μ, lipschitz_on_with (real.nnabs $ bound a) (λ x, F x a) (ball x₀ ε))
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐ a ∂μ, has_deriv_at (λ x, F x a) (F' a) x₀) :
  (integrable F' μ) ∧ has_deriv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ :=
begin
  have hm := (continuous_linear_map.smul_rightL ℝ ℝ E 1).continuous.measurable.comp_ae_measurable
             hF'_meas,
  cases has_fderiv_at_of_dominated_loc_of_lip ε_pos hF_meas hF_int hm h_lipsch bound_integrable
    h_diff with hF'_int key,
  replace hF'_int : integrable F' μ,
  { rw [← integrable_norm_iff hm] at hF'_int,
    simpa only [integrable_norm_iff, hF'_meas, one_mul, norm_one,
                continuous_linear_map.norm_smul_rightL_apply] using hF'_int},
  refine ⟨hF'_int, _⟩,
  simp_rw has_deriv_at_iff_has_fderiv_at at h_diff ⊢,
  rwa continuous_linear_map.integral_comp_comm _ hF'_int at key,
  all_goals { apply_instance, },
end

/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : ℝ`, assuming
`F x₀` is integrable, `x ↦ F x a` is differentiable on an interval around `x₀` for ae `a`
(with interval radius independent of `a`) with derivative uniformly bounded by an integrable
function, and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
lemma has_deriv_at_of_dominated_loc_of_deriv_le {F : ℝ → α → E} {F' : ℝ → α → E} {x₀ : ℝ}
  {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) μ)
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : ae_measurable (F' x₀) μ)
  {bound : α → ℝ}
  (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ∥F' x a∥ ≤ bound a)
  (bound_integrable : integrable bound μ)
  (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, has_deriv_at (λ x, F x a) (F' x a) x) :
  (integrable (F' x₀) μ) ∧ has_deriv_at (λn, ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ :=
begin
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos,
  have diff_x₀ : ∀ᵐ a ∂μ, has_deriv_at (λ x, F x a) (F' x₀ a) x₀ :=
    h_diff.mono (λ a ha, ha x₀ x₀_in),
  have : ∀ᵐ a ∂μ, lipschitz_on_with (real.nnabs (bound a)) (λ (x : ℝ), F x a) (ball x₀ ε),
  { apply (h_diff.and h_bound).mono,
    rintros a ⟨ha_deriv, ha_bound⟩,
    refine (convex_ball _ _).lipschitz_on_with_of_nnnorm_has_deriv_within_le
      (λ x x_in, (ha_deriv x x_in).has_deriv_within_at) (λ x x_in, _),
    rw [← nnreal.coe_le_coe, coe_nnnorm, nnreal.coe_nnabs],
    exact (ha_bound x x_in).trans (le_abs_self _) },
  exact has_deriv_at_of_dominated_loc_of_lip ε_pos hF_meas hF_int hF'_meas this
        bound_integrable diff_x₀
end
