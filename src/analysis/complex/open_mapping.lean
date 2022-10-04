/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
import analysis.analytic.isolated_zeros
import analysis.complex.cauchy_integral
import analysis.complex.abs_max
import topology.algebra.field
import topology.locally_constant.basic

/-!
# The open mapping theorem for holomorphic functions

A holomorphic function on a preconnected open set of the complex plane is either constant or open.
-/

open set filter metric complex
open_locale topological_space

variables {U : set ℂ} {f : ℂ → ℂ} {z₀ w : ℂ} {ε r m : ℝ}

lemma diff_cont_on_cl.ball_subset_image_closed_ball (h : diff_cont_on_cl ℂ f (ball z₀ r))
  (hr : 0 < r) (hf : ∀ z ∈ sphere z₀ r, ε ≤ ∥f z - f z₀∥) (hz₀ : ¬ ∀ᶠ z in 𝓝 z₀, f z = f z₀) :
  ball (f z₀) (ε / 2) ⊆ f '' closed_ball z₀ r :=
begin
  rintro v hv,
  have h2 : diff_cont_on_cl ℂ (λ z, f z - v) (ball z₀ r) := h.sub_const v,
  have h3 : continuous_on (λ z, ∥f z - v∥) (closed_ball z₀ r),
    from continuous_norm.comp_continuous_on (closure_ball z₀ hr.ne.symm ▸ h2.continuous_on),
  have h4 : analytic_on ℂ f (ball z₀ r) := h.differentiable_on.analytic_on is_open_ball,
  have h5 : ∀ z ∈ sphere z₀ r, ε / 2 ≤ ∥f z - v∥,
    { rintro z hz,
      have := norm_sub_sub_norm_sub_le_norm_sub (f z) v (f z₀),
      linarith [hf z hz, (show ∥v - f z₀∥ < ε / 2, from mem_ball.mp hv)] },
  obtain ⟨w, hw, hfw⟩ : ∃ z ∈ ball z₀ r, ∥f z - v∥ < ε / 2,
    from ⟨z₀, mem_ball_self hr, by simpa [← dist_eq_norm, dist_comm] using mem_ball.mp hv⟩,
  obtain ⟨z, hz1, hz2⟩ : ∃ z ∈ ball z₀ r, is_local_min (λ z, ∥f z - v∥) z,
    from exists_local_min_mem_ball h3 h5 hw hfw,
  have h7 := h2.differentiable_on.eventually_differentiable_at (is_open_ball.mem_nhds hz1),
  refine ⟨z, ball_subset_closed_ball hz1, sub_eq_zero.mp _⟩,
  refine (complex.eventually_eq_or_eq_zero_of_is_local_min_norm h7 hz2).resolve_left (λ key, _),
  have h8 : ∀ᶠ w in 𝓝 z, f w = f z := by { filter_upwards [key] with h; field_simp },
  have h9 : is_preconnected (ball z₀ r) := (convex_ball z₀ r).is_preconnected,
  have h10 : ∃ᶠ w in 𝓝[≠] z, f w = f z := (h8.filter_mono nhds_within_le_nhds).frequently,
  have h11 := h4.eq_on_of_preconnected_of_frequently_eq analytic_on_const h9 hz1 h10,
  have h12 : f z = f z₀ := (h11 (mem_ball_self hr)).symm,
  exact hz₀ (mem_of_superset (ball_mem_nhds z₀ hr) (h12 ▸ h11))
end

lemma diff_cont_on_cl.continuous_on_closed_ball (hf : diff_cont_on_cl ℂ f (ball z₀ r)) :
  continuous_on f (closed_ball z₀ r) :=
if h : r = 0 then by simp only [h, closed_ball_zero, continuous_on_singleton]
  else closure_ball z₀ h ▸ hf.continuous_on

lemma analytic_at.locally_constant_or_nhds_le_map_nhds (hf : analytic_at ℂ f z₀) :
  (∀ᶠ z in 𝓝 z₀, f z = f z₀) ∨ (𝓝 (f z₀) ≤ filter.map f (𝓝 z₀)) :=
begin
  refine or_iff_not_imp_left.mpr (λ h, _),
  refine (nhds_basis_ball.le_basis_iff (nhds_basis_closed_ball.map f)).mpr (λ R hR, _),
  have h1 := (hf.eventually_eq_or_eventually_ne analytic_at_const).resolve_left h,
  have h2 : ∀ᶠ z in 𝓝 z₀, analytic_at ℂ f z := (is_open_analytic_at ℂ f).eventually_mem hf,
  obtain ⟨ρ, hρ, h3, h4⟩ : ∃ ρ > 0, analytic_on ℂ f (closed_ball z₀ ρ) ∧
      ∀ z ∈ closed_ball z₀ ρ, z ≠ z₀ → f z ≠ f z₀,
    by simpa only [set_of_and, subset_inter_iff] using
      nhds_basis_closed_ball.mem_iff.mp (h2.and (eventually_nhds_within_iff.mp h1)),
  replace h3 : diff_cont_on_cl ℂ f (ball z₀ ρ),
    from ⟨h3.differentiable_on.mono ball_subset_closed_ball,
      (closure_ball z₀ hρ.lt.ne.symm).symm ▸ h3.continuous_on⟩,
  let r := ρ ⊓ R,
  have hr : 0 < r := lt_inf_iff.mpr ⟨hρ, hR⟩,
  have h5 : closed_ball z₀ r ⊆ closed_ball z₀ ρ := closed_ball_subset_closed_ball inf_le_left,
  have h6 : diff_cont_on_cl ℂ f (ball z₀ r) := h3.mono (ball_subset_ball inf_le_left),
  have h7 : ∀ z ∈ sphere z₀ r, f z ≠ f z₀,
    from λ z hz, h4 z (h5 (sphere_subset_closed_ball hz)) (ne_of_mem_sphere hz hr.ne.symm),
  have h8 : (sphere z₀ r).nonempty := normed_space.sphere_nonempty.mpr hr.le,
  have h9 : continuous_on (λ x, ∥f x - f z₀∥) (sphere z₀ r),
    from continuous_norm.comp_continuous_on
      ((h6.sub_const (f z₀)).continuous_on_closed_ball.mono sphere_subset_closed_ball),
  obtain ⟨x, hx, hfx⟩ := (is_compact_sphere z₀ r).exists_forall_le h8 h9,
  refine ⟨∥f x - f z₀∥ / 2, half_pos (norm_sub_pos_iff.mpr (h7 x hx)), _⟩,
  exact (h6.ball_subset_image_closed_ball hr (λ z hz, hfx z hz) h).trans
    (image_subset f (closed_ball_subset_closed_ball inf_le_right))
end

theorem analytic_on.is_constant_or_is_open (hf : analytic_on ℂ f U) (hU : is_preconnected U) :
  (∃ w, ∀ z ∈ U, f z = w) ∨ (∀ s ⊆ U, is_open s → is_open (f '' s)) :=
begin
  by_cases ∃ z₀ ∈ U, ∀ᶠ z in 𝓝 z₀, f z = f z₀,
  { obtain ⟨z₀, hz₀, h⟩ := h,
    have h3 : ∃ᶠ z in 𝓝[≠] z₀, f z = f z₀ := (h.filter_mono nhds_within_le_nhds).frequently,
    exact or.inl ⟨f z₀, hf.eq_on_of_preconnected_of_frequently_eq analytic_on_const hU hz₀ h3⟩ },
  { push_neg at h,
    refine or.inr (λ s hs1 hs2, is_open_iff_mem_nhds.mpr _),
    rintro z ⟨w, hw1, rfl⟩,
    have := (hf w (hs1 hw1)).locally_constant_or_nhds_le_map_nhds.resolve_left (h w (hs1 hw1)),
    exact this (image_mem_map (hs2.mem_nhds hw1)) }
end
