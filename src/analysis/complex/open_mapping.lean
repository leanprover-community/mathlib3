/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
import analysis.analytic.isolated_zeros
import analysis.complex.cauchy_integral
import analysis.complex.abs_max

/-!
# The open mapping theorem for holomorphic functions

This file proves the open mapping theorem for holomorphic functions, namely that an analytic
function on a preconnected set of the complex plane is either constant or open. The main step is to
show a local version of the theorem that states that if `f` is analytic at a point `z₀`, then either
it is constant in a neighborhood of `z₀` or it maps any neighborhood of `z₀` to a neighborhood of
its image `f z₀`. The results extend in higher dimension to `g : E → ℂ`.

The proof of the local version on `ℂ` goes through two main steps: first, assuming that the function
is not constant around `z₀`, use the isolated zero principle to show that `‖f z‖` is bounded below
on a small `sphere z₀ r` around `z₀`, and then use the maximum principle applied to the auxiliary
function `(λ z, ‖f z - v‖)` to show that any `v` close enough to `f z₀` is in `f '' ball z₀ r`. That
second step is implemented in `diff_cont_on_cl.ball_subset_image_closed_ball`.

## Main results

* `analytic_at.eventually_constant_or_nhds_le_map_nhds` is the local version of the open mapping
  theorem around a point;
* `analytic_on.is_constant_or_is_open` is the open mapping theorem on a connected open set.
-/

open set filter metric complex
open_locale topology

variables {E : Type*} [normed_add_comm_group E] [normed_space ℂ E] {U : set E}
  {f : ℂ → ℂ} {g : E → ℂ} {z₀ w : ℂ} {ε r m : ℝ}

/-- If the modulus of a holomorphic function `f` is bounded below by `ε` on a circle, then its range
contains a disk of radius `ε / 2`. -/
lemma diff_cont_on_cl.ball_subset_image_closed_ball (h : diff_cont_on_cl ℂ f (ball z₀ r))
  (hr : 0 < r) (hf : ∀ z ∈ sphere z₀ r, ε ≤ ‖f z - f z₀‖) (hz₀ : ∃ᶠ z in 𝓝 z₀, f z ≠ f z₀) :
  ball (f z₀) (ε / 2) ⊆ f '' closed_ball z₀ r :=
begin
  /- This is a direct application of the maximum principle. Pick `v` close to `f z₀`, and look at
  the function `λ z, ‖f z - v‖`: it is bounded below on the circle, and takes a small value at `z₀`
  so it is not constant on the disk, which implies that its infimum is equal to `0` and hence that
  `v` is in the range of `f`. -/
  rintro v hv,
  have h1 : diff_cont_on_cl ℂ (λ z, f z - v) (ball z₀ r) := h.sub_const v,
  have h2 : continuous_on (λ z, ‖f z - v‖) (closed_ball z₀ r),
    from continuous_norm.comp_continuous_on (closure_ball z₀ hr.ne.symm ▸ h1.continuous_on),
  have h3 : analytic_on ℂ f (ball z₀ r) := h.differentiable_on.analytic_on is_open_ball,
  have h4 : ∀ z ∈ sphere z₀ r, ε / 2 ≤ ‖f z - v‖,
    from λ z hz, by linarith [hf z hz, (show ‖v - f z₀‖ < ε / 2, from mem_ball.mp hv),
      norm_sub_sub_norm_sub_le_norm_sub (f z) v (f z₀)],
  have h5 : ‖f z₀ - v‖ < ε / 2 := by simpa [← dist_eq_norm, dist_comm] using mem_ball.mp hv,
  obtain ⟨z, hz1, hz2⟩ : ∃ z ∈ ball z₀ r, is_local_min (λ z, ‖f z - v‖) z,
    from exists_local_min_mem_ball h2 (mem_closed_ball_self hr.le) (λ z hz, h5.trans_le (h4 z hz)),
  refine ⟨z, ball_subset_closed_ball hz1, sub_eq_zero.mp _⟩,
  have h6 := h1.differentiable_on.eventually_differentiable_at (is_open_ball.mem_nhds hz1),
  refine (eventually_eq_or_eq_zero_of_is_local_min_norm h6 hz2).resolve_left (λ key, _),
  have h7 : ∀ᶠ w in 𝓝 z, f w = f z := by { filter_upwards [key] with h; field_simp },
  replace h7 : ∃ᶠ w in 𝓝[≠] z, f w = f z := (h7.filter_mono nhds_within_le_nhds).frequently,
  have h8 : is_preconnected (ball z₀ r) := (convex_ball z₀ r).is_preconnected,
  have h9 := h3.eq_on_of_preconnected_of_frequently_eq analytic_on_const h8 hz1 h7,
  have h10 : f z = f z₀ := (h9 (mem_ball_self hr)).symm,
  exact not_eventually.mpr hz₀ (mem_of_superset (ball_mem_nhds z₀ hr) (h10 ▸ h9))
end

/-- A function `f : ℂ → ℂ` which is analytic at a point `z₀` is either constant in a neighborhood
of `z₀`, or behaves locally like an open function (in the sense that the image of every neighborhood
of `z₀` is a neighborhood of `f z₀`, as in `is_open_map_iff_nhds_le`). For a function `f : E → ℂ`
the same result holds, see `analytic_at.eventually_constant_or_nhds_le_map_nhds`. -/
lemma analytic_at.eventually_constant_or_nhds_le_map_nhds_aux (hf : analytic_at ℂ f z₀) :
  (∀ᶠ z in 𝓝 z₀, f z = f z₀) ∨ (𝓝 (f z₀) ≤ map f (𝓝 z₀)) :=
begin
  /- The function `f` is analytic in a neighborhood of `z₀`; by the isolated zeros principle, if `f`
  is not constant in a neighborhood of `z₀`, then it is nonzero, and therefore bounded below, on
  every small enough circle around `z₀` and then `diff_cont_on_cl.ball_subset_image_closed_ball`
  provides an explicit ball centered at `f z₀` contained in the range of `f`. -/
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
  have h9 : continuous_on (λ x, ‖f x - f z₀‖) (sphere z₀ r),
    from continuous_norm.comp_continuous_on
      ((h6.sub_const (f z₀)).continuous_on_ball.mono sphere_subset_closed_ball),
  obtain ⟨x, hx, hfx⟩ := (is_compact_sphere z₀ r).exists_forall_le h8 h9,
  refine ⟨‖f x - f z₀‖ / 2, half_pos (norm_sub_pos_iff.mpr (h7 x hx)), _⟩,
  exact (h6.ball_subset_image_closed_ball hr (λ z hz, hfx z hz) (not_eventually.mp h)).trans
    (image_subset f (closed_ball_subset_closed_ball inf_le_right))
end

/-- The *open mapping theorem* for holomorphic functions, local version: is a function `g : E → ℂ`
is analytic at a point `z₀`, then either it is constant in a neighborhood of `z₀`, or it maps every
neighborhood of `z₀` to a neighborhood of `z₀`. For the particular case of a holomorphic function on
`ℂ`, see `analytic_at.eventually_constant_or_nhds_le_map_nhds_aux`. -/
lemma analytic_at.eventually_constant_or_nhds_le_map_nhds {z₀ : E} (hg : analytic_at ℂ g z₀) :
  (∀ᶠ z in 𝓝 z₀, g z = g z₀) ∨ (𝓝 (g z₀) ≤ map g (𝓝 z₀)) :=
begin
  /- The idea of the proof is to use the one-dimensional version applied to the restriction of `g`
  to lines going through `z₀` (indexed by `sphere (0 : E) 1`). If the restriction is eventually
  constant along each of these lines, then the identity theorem implies that `g` is constant on any
  ball centered at `z₀` on which it is analytic, and in particular `g` is eventually constant. If on
  the other hand there is one line along which `g` is not eventually constant, then the
  one-dimensional version of the open mapping theorem can be used to conclude. -/
  let ray : E → ℂ → E := λ z t, z₀ + t • z,
  let gray : E → ℂ → ℂ := λ z, (g ∘ ray z),
  obtain ⟨r, hr, hgr⟩ := is_open_iff.mp (is_open_analytic_at ℂ g) z₀ hg,
  have h1 : ∀ z ∈ sphere (0 : E) 1, analytic_on ℂ (gray z) (ball 0 r),
  { refine λ z hz t ht, analytic_at.comp _ _,
    { exact hgr (by simpa [ray, norm_smul, mem_sphere_zero_iff_norm.mp hz] using ht) },
    { exact analytic_at_const.add
      ((continuous_linear_map.smul_right (continuous_linear_map.id ℂ ℂ) z).analytic_at t) } },
  by_cases (∀ z ∈ sphere (0 : E) 1, ∀ᶠ t in 𝓝 0, gray z t = gray z 0),
  { left, -- If g is eventually constant along every direction, then it is eventually constant
    refine eventually_of_mem (ball_mem_nhds z₀ hr) (λ z hz, _),
    refine (eq_or_ne z z₀).cases_on (congr_arg g) (λ h', _),
    replace h' : ‖z - z₀‖ ≠ 0 := by simpa only [ne.def, norm_eq_zero, sub_eq_zero],
    let w : E := ‖z - z₀‖⁻¹ • (z - z₀),
    have h3 : ∀ t ∈ ball (0 : ℂ) r, gray w t = g z₀,
    { have e1 : is_preconnected (ball (0 : ℂ) r) := (convex_ball 0 r).is_preconnected,
      have e2 : w ∈ sphere (0 : E) 1 := by simp [w, norm_smul, h'],
      specialize h1 w e2,
      apply h1.eq_on_of_preconnected_of_eventually_eq analytic_on_const e1 (mem_ball_self hr),
      simpa [gray, ray] using h w e2 },
    have h4 : ‖z - z₀‖ < r := by simpa [dist_eq_norm] using mem_ball.mp hz,
    replace h4 : ↑‖z - z₀‖ ∈ ball (0 : ℂ) r := by simpa only [mem_ball_zero_iff, norm_eq_abs,
      abs_of_real, abs_norm_eq_norm],
    simpa only [gray, ray, smul_smul, mul_inv_cancel h', one_smul, add_sub_cancel'_right,
      function.comp_app, coe_smul] using h3 ↑‖z - z₀‖ h4 },
  { right, -- Otherwise, it is open along at least one direction and that implies the result
    push_neg at h,
    obtain ⟨z, hz, hrz⟩ := h,
    specialize h1 z hz 0 (mem_ball_self hr),
    have h7 := h1.eventually_constant_or_nhds_le_map_nhds_aux.resolve_left hrz,
    rw [show gray z 0 = g z₀, by simp [gray, ray], ← map_compose] at h7,
    refine h7.trans (map_mono _),
    have h10 : continuous (λ (t : ℂ), z₀ + t • z),
      from continuous_const.add (continuous_id'.smul continuous_const),
    simpa using h10.tendsto 0 }
end

/-- The *open mapping theorem* for holomorphic functions, global version: if a function `g : E → ℂ`
is analytic on a connected set `U`, then either it is constant on `U`, or it is open on `U` (in the
sense that it maps any open set contained in `U` to an open set in `ℂ`). -/
theorem analytic_on.is_constant_or_is_open (hg : analytic_on ℂ g U) (hU : is_preconnected U) :
  (∃ w, ∀ z ∈ U, g z = w) ∨ (∀ s ⊆ U, is_open s → is_open (g '' s)) :=
begin
  by_cases ∃ z₀ ∈ U, ∀ᶠ z in 𝓝 z₀, g z = g z₀,
  { obtain ⟨z₀, hz₀, h⟩ := h,
    exact or.inl ⟨g z₀, hg.eq_on_of_preconnected_of_eventually_eq analytic_on_const hU hz₀ h⟩ },
  { push_neg at h,
    refine or.inr (λ s hs1 hs2, is_open_iff_mem_nhds.mpr _),
    rintro z ⟨w, hw1, rfl⟩,
    exact (hg w (hs1 hw1)).eventually_constant_or_nhds_le_map_nhds.resolve_left (h w (hs1 hw1))
      (image_mem_map (hs2.mem_nhds hw1)) }
end
