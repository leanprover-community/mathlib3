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

We already know from `continuous_of_dominated` in `measure_theory.integral.bochner` how to
guarantee that `f` is continuous using the dominated convergence theorem. In this file,
we want to express the derivative of `f` as the integral of the derivative of `F` with respect
to `x`.


## Main results

As explained above, all results express the derivative of a parametric integral as the integral of
a derivative. The variations come from the assumptions and from the different ways of expressing
derivative, especially Fréchet derivatives vs elementary derivative of function of one real
variable.

* `has_fderiv_at_integral_of_dominated_loc_of_lip`: this version assumes that
  - `F x` is ae-measurable for x near `x₀`,
  - `F x₀` is integrable,
  - `λ x, F x a` has derivative `F' a : H →L[ℝ] E` at `x₀` which is ae-measurable,
  - `λ x, F x a` is locally Lipschitz near `x₀` for almost every `a`, with a Lipschitz bound which
    is integrable with respect to `a`.

  A subtle point is that the "near x₀" in the last condition has to be uniform in `a`. This is
  controlled by a positive number `ε`.

* `has_fderiv_at_integral_of_dominated_of_fderiv_le`: this version assume `λ x, F x a` has
   derivative `F' x a` for `x` near `x₀` and `F' x` is bounded by an integrable function independent
   from `x` near `x₀`.


`has_deriv_at_integral_of_dominated_loc_of_lip` and
`has_deriv_at_integral_of_dominated_loc_of_deriv_le` are versions of the above two results that
assume `H = ℝ` or `H = ℂ` and use the high-school derivative `deriv` instead of Fréchet derivative
`fderiv`.

We also provide versions of these theorems for set integrals.

## Tags
integral, derivative
-/

noncomputable theory

open topological_space measure_theory filter metric
open_locale topology filter

variables {α : Type*} [measurable_space α] {μ : measure α} {𝕜 : Type*} [is_R_or_C 𝕜]
          {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [normed_space 𝕜 E]
          [complete_space E]
          {H : Type*} [normed_add_comm_group H] [normed_space 𝕜 H]

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming `F x₀` is
integrable, `‖F x a - F x₀ a‖ ≤ bound a * ‖x - x₀‖` for `x` in a ball around `x₀` for ae `a` with
integrable Lipschitz bound `bound` (with a ball radius independent of `a`), and `F x` is
ae-measurable for `x` in the same ball. See `has_fderiv_at_integral_of_dominated_loc_of_lip` for a
slightly less general but usually more useful version. -/
lemma has_fderiv_at_integral_of_dominated_loc_of_lip' {F : H → α → E} {F' : α → (H →L[𝕜] E)}
  {x₀ : H} {bound : α → ℝ}
  {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ x ∈ ball x₀ ε, ae_strongly_measurable (F x) μ)
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : ae_strongly_measurable F' μ)
  (h_lipsch : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ‖F x a - F x₀ a‖ ≤ bound a * ‖x - x₀‖)
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐ a ∂μ, has_fderiv_at (λ x, F x a) (F' a) x₀) :
  integrable F' μ ∧ has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ :=
begin
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos,
  have nneg : ∀ x, 0 ≤ ‖x - x₀‖⁻¹ := λ x, inv_nonneg.mpr (norm_nonneg _) ,
  set b : α → ℝ := λ a, |bound a|,
  have b_int : integrable b μ := bound_integrable.norm,
  have b_nonneg : ∀ a, 0 ≤ b a := λ a, abs_nonneg _,
  replace h_lipsch : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ‖F x a - F x₀ a‖ ≤ b a * ‖x - x₀‖,
    from h_lipsch.mono (λ a ha x hx, (ha x hx).trans $
      mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)),
  have hF_int' : ∀ x ∈ ball x₀ ε, integrable (F x) μ,
  { intros x x_in,
    have : ∀ᵐ a ∂μ, ‖F x₀ a - F x a‖ ≤ ε * b a,
    { simp only [norm_sub_rev (F x₀ _)],
      refine h_lipsch.mono (λ a ha, (ha x x_in).trans _),
      rw mul_comm ε,
      rw [mem_ball, dist_eq_norm] at x_in,
      exact mul_le_mul_of_nonneg_left x_in.le (b_nonneg _) },
    exact integrable_of_norm_sub_le (hF_meas x x_in) hF_int
      (integrable.const_mul bound_integrable.norm ε) this },
  have hF'_int : integrable F' μ,
  { have : ∀ᵐ a ∂μ, ‖F' a‖ ≤ b a,
    { apply (h_diff.and h_lipsch).mono,
      rintros a ⟨ha_diff, ha_lip⟩,
      refine ha_diff.le_of_lip' (b_nonneg a) (mem_of_superset (ball_mem_nhds _ ε_pos) $ ha_lip) },
    exact b_int.mono' hF'_meas this },
  refine ⟨hF'_int, _⟩,
  have h_ball: ball x₀ ε ∈ 𝓝 x₀ := ball_mem_nhds x₀ ε_pos,
  have : ∀ᶠ x in 𝓝 x₀,
      ‖x - x₀‖⁻¹ * ‖∫ a, F x a ∂μ - ∫ a, F x₀ a ∂μ - (∫ a, F' a ∂μ) (x - x₀)‖ =
       ‖∫ a, ‖x - x₀‖⁻¹ • (F x a - F x₀ a  - F' a (x - x₀)) ∂μ‖,
  { apply mem_of_superset (ball_mem_nhds _ ε_pos),
    intros x x_in,
    rw [set.mem_set_of_eq, ← norm_smul_of_nonneg (nneg _), integral_smul,
        integral_sub, integral_sub, ← continuous_linear_map.integral_apply hF'_int],
    exacts [hF_int' x x_in, hF_int, (hF_int' x x_in).sub hF_int,
            hF'_int.apply_continuous_linear_map _] },
  rw [has_fderiv_at_iff_tendsto, tendsto_congr' this, ← tendsto_zero_iff_norm_tendsto_zero,
      ← show ∫ (a : α), ‖x₀ - x₀‖⁻¹ • (F x₀ a - F x₀ a - (F' a) (x₀ - x₀)) ∂μ = 0, by simp],
  apply tendsto_integral_filter_of_dominated_convergence,
  { filter_upwards [h_ball] with _ x_in,
    apply ae_strongly_measurable.const_smul,
    exact ((hF_meas _ x_in).sub (hF_meas _ x₀_in)).sub (hF'_meas.apply_continuous_linear_map _) },
  { apply mem_of_superset h_ball,
    intros x hx,
    apply (h_diff.and h_lipsch).mono,
    rintros a ⟨ha_deriv, ha_bound⟩,
    show ‖‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀))‖ ≤ b a + ‖F' a‖,
    replace ha_bound : ‖F x a - F x₀ a‖ ≤ b a * ‖x - x₀‖ := ha_bound x hx,
    calc ‖‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀))‖
    = ‖‖x - x₀‖⁻¹ • (F x a - F x₀ a) - ‖x - x₀‖⁻¹ • F' a (x - x₀)‖ : by rw smul_sub
    ... ≤  ‖‖x - x₀‖⁻¹ • (F x a - F x₀ a)‖ + ‖‖x - x₀‖⁻¹ • F' a (x - x₀)‖ : norm_sub_le _ _
    ... =  ‖x - x₀‖⁻¹ * ‖F x a - F x₀ a‖ + ‖x - x₀‖⁻¹ * ‖F' a (x - x₀)‖ :
                                 by { rw [norm_smul_of_nonneg, norm_smul_of_nonneg] ; exact nneg _}
    ... ≤  ‖x - x₀‖⁻¹ * (b a * ‖x - x₀‖) + ‖x - x₀‖⁻¹ * (‖F' a‖ * ‖x - x₀‖) : add_le_add _ _
    ... ≤ b a + ‖F' a‖ : _,
    exact mul_le_mul_of_nonneg_left ha_bound (nneg _),
    apply mul_le_mul_of_nonneg_left ((F' a).le_op_norm _) (nneg _),
    by_cases h : ‖x - x₀‖ = 0,
    { simpa [h] using add_nonneg (b_nonneg a) (norm_nonneg (F' a)) },
    { field_simp [h] } },
  { exact b_int.add hF'_int.norm },
  { apply h_diff.mono,
    intros a ha,
    suffices : tendsto (λ x, ‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀))) (𝓝 x₀) (𝓝 0),
    by simpa,
    rw tendsto_zero_iff_norm_tendsto_zero,
    have : (λ x, ‖x - x₀‖⁻¹ * ‖F x a - F x₀ a - F' a (x - x₀)‖) =
            λ x, ‖‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀))‖,
    { ext x,
      rw norm_smul_of_nonneg (nneg _) },
    rwa [has_fderiv_at_iff_tendsto, this] at ha },
end

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a ball around `x₀` for ae `a`
(with a ball radius independent of `a`) with integrable Lipschitz bound, and `F x` is ae-measurable
for `x` in a possibly smaller neighborhood of `x₀`. -/
lemma has_fderiv_at_integral_of_dominated_loc_of_lip {F : H → α → E} {F' : α → (H →L[𝕜] E)} {x₀ : H}
  {bound : α → ℝ}
  {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (F x) μ)
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : ae_strongly_measurable F' μ)
  (h_lip : ∀ᵐ a ∂μ, lipschitz_on_with (real.nnabs $ bound a) (λ x, F x a) (ball x₀ ε))
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐ a ∂μ, has_fderiv_at (λ x, F x a) (F' a) x₀) :
  integrable F' μ ∧ has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ :=
begin
  obtain ⟨δ, δ_pos, hδ⟩ : ∃ δ > 0, ∀ x ∈ ball x₀ δ, ae_strongly_measurable (F x) μ ∧ x ∈ ball x₀ ε,
    from eventually_nhds_iff_ball.mp (hF_meas.and (ball_mem_nhds x₀ ε_pos)),
  choose hδ_meas hδε using hδ,
  replace h_lip : ∀ᵐ (a : α) ∂μ, ∀ x ∈ ball x₀ δ, ‖F x a - F x₀ a‖ ≤ |bound a| * ‖x - x₀‖,
    from h_lip.mono (λ a lip x hx, lip.norm_sub_le (hδε x hx) (mem_ball_self ε_pos)),
  replace bound_integrable := bound_integrable.norm,
  apply has_fderiv_at_integral_of_dominated_loc_of_lip' δ_pos; assumption
end

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is differentiable on a ball around `x₀` for ae `a` with
derivative norm uniformly bounded by an integrable function (the ball radius is independent of `a`),
and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
lemma has_fderiv_at_integral_of_dominated_of_fderiv_le {F : H → α → E} {F' : H → α → (H →L[𝕜] E)}
  {x₀ : H} {bound : α → ℝ}
  {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (F x) μ)
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : ae_strongly_measurable (F' x₀) μ)
  (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ‖F' x a‖ ≤ bound a)
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, has_fderiv_at (λ x, F x a) (F' x a) x) :
  has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ :=
begin
  letI : normed_space ℝ H := normed_space.restrict_scalars ℝ 𝕜 H,
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos,
  have diff_x₀ : ∀ᵐ a ∂μ, has_fderiv_at (λ x, F x a) (F' x₀ a) x₀ :=
    h_diff.mono (λ a ha, ha x₀ x₀_in),
  have : ∀ᵐ a ∂μ, lipschitz_on_with (real.nnabs (bound a)) (λ x, F x a) (ball x₀ ε),
  { apply (h_diff.and h_bound).mono,
    rintros a ⟨ha_deriv, ha_bound⟩,
    refine (convex_ball _ _).lipschitz_on_with_of_nnnorm_has_fderiv_within_le
      (λ x x_in, (ha_deriv x x_in).has_fderiv_within_at) (λ x x_in, _),
    rw [← nnreal.coe_le_coe, coe_nnnorm, real.coe_nnabs],
    exact (ha_bound x x_in).trans (le_abs_self _) },
  exact (has_fderiv_at_integral_of_dominated_loc_of_lip ε_pos hF_meas hF_int
                                               hF'_meas this bound_integrable diff_x₀).2
end

/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : 𝕜`, `𝕜 = ℝ` or `𝕜 = ℂ`,
assuming `F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a ball around `x₀` for ae `a`
(with ball radius independent of `a`) with integrable Lipschitz bound, and `F x` is
ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
lemma has_deriv_at_integral_of_dominated_loc_of_lip {F : 𝕜 → α → E} {F' : α → E} {x₀ : 𝕜}
  {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (F x) μ)
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : ae_strongly_measurable F' μ) {bound : α → ℝ}
  (h_lipsch : ∀ᵐ a ∂μ, lipschitz_on_with (real.nnabs $ bound a) (λ x, F x a) (ball x₀ ε))
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐ a ∂μ, has_deriv_at (λ x, F x a) (F' a) x₀) :
  (integrable F' μ) ∧ has_deriv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ :=
begin
  set L : E →L[𝕜] (𝕜 →L[𝕜] E) := (continuous_linear_map.smul_rightL 𝕜 𝕜 E 1),
  replace h_diff : ∀ᵐ a ∂μ, has_fderiv_at (λ x, F x a) (L (F' a)) x₀ :=
    h_diff.mono (λ x hx, hx.has_fderiv_at),
  have hm : ae_strongly_measurable (L ∘ F') μ := L.continuous.comp_ae_strongly_measurable hF'_meas,
  cases has_fderiv_at_integral_of_dominated_loc_of_lip ε_pos hF_meas hF_int hm h_lipsch
    bound_integrable h_diff with hF'_int key,
  replace hF'_int : integrable F' μ,
  { rw [← integrable_norm_iff hm] at hF'_int,
    simpa only [L, (∘), integrable_norm_iff, hF'_meas, one_mul, norm_one,
      continuous_linear_map.comp_apply, continuous_linear_map.coe_restrict_scalarsL',
      continuous_linear_map.norm_restrict_scalars, continuous_linear_map.norm_smul_rightL_apply]
      using hF'_int },
  refine ⟨hF'_int, _⟩,
  simp_rw has_deriv_at_iff_has_fderiv_at at h_diff ⊢,
  rwa continuous_linear_map.integral_comp_comm _ hF'_int at key,
  all_goals { apply_instance, },
end

/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : ℝ`, assuming
`F x₀` is integrable, `x ↦ F x a` is differentiable on an interval around `x₀` for ae `a`
(with interval radius independent of `a`) with derivative uniformly bounded by an integrable
function, and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
lemma has_deriv_at_integral_of_dominated_loc_of_deriv_le {F : 𝕜 → α → E} {F' : 𝕜 → α → E} {x₀ : 𝕜}
  {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (F x) μ)
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : ae_strongly_measurable (F' x₀) μ)
  {bound : α → ℝ}
  (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ‖F' x a‖ ≤ bound a)
  (bound_integrable : integrable bound μ)
  (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, has_deriv_at (λ x, F x a) (F' x a) x) :
  (integrable (F' x₀) μ) ∧ has_deriv_at (λn, ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ :=
begin
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos,
  have diff_x₀ : ∀ᵐ a ∂μ, has_deriv_at (λ x, F x a) (F' x₀ a) x₀ :=
    h_diff.mono (λ a ha, ha x₀ x₀_in),
  have : ∀ᵐ a ∂μ, lipschitz_on_with (real.nnabs (bound a)) (λ (x : 𝕜), F x a) (ball x₀ ε),
  { apply (h_diff.and h_bound).mono,
    rintros a ⟨ha_deriv, ha_bound⟩,
    refine (convex_ball _ _).lipschitz_on_with_of_nnnorm_has_deriv_within_le
      (λ x x_in, (ha_deriv x x_in).has_deriv_within_at) (λ x x_in, _),
    rw [← nnreal.coe_le_coe, coe_nnnorm, real.coe_nnabs],
    exact (ha_bound x x_in).trans (le_abs_self _) },
  exact has_deriv_at_integral_of_dominated_loc_of_lip ε_pos hF_meas hF_int hF'_meas this
        bound_integrable diff_x₀
end
