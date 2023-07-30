/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
import analysis.complex.removable_singularity
import analysis.calculus.series

/-!
# Locally uniform limits of holomorphic functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file gathers some results about locally uniform limits of holomorphic functions on an open
subset of the complex plane.

## Main results

* `tendsto_locally_uniformly_on.differentiable_on`: A locally uniform limit of holomorphic functions
  is holomorphic.
* `tendsto_locally_uniformly_on.deriv`: Locally uniform convergence implies locally uniform
  convergence of the derivatives to the derivative of the limit.
-/

open set metric measure_theory filter complex interval_integral
open_locale real topology

variables {E ι : Type*} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
  {U K : set ℂ} {z : ℂ} {M r δ : ℝ} {φ : filter ι} {F : ι → ℂ → E} {f g : ℂ → E}

namespace complex

section cderiv

/-- A circle integral which coincides with `deriv f z` whenever one can apply the Cauchy formula for
the derivative. It is useful in the proof that locally uniform limits of holomorphic functions are
holomorphic, because it depends continuously on `f` for the uniform topology. -/
noncomputable def cderiv (r : ℝ) (f : ℂ → E) (z : ℂ) : E :=
(2 * π * I : ℂ)⁻¹ • ∮ w in C(z, r), ((w - z) ^ 2)⁻¹ • f w

lemma cderiv_eq_deriv (hU : is_open U) (hf : differentiable_on ℂ f U) (hr : 0 < r)
  (hzr : closed_ball z r ⊆ U) :
  cderiv r f z = deriv f z :=
two_pi_I_inv_smul_circle_integral_sub_sq_inv_smul_of_differentiable hU hzr hf (mem_ball_self hr)

lemma norm_cderiv_le (hr : 0 < r) (hf : ∀ w ∈ sphere z r, ‖f w‖ ≤ M) :
  ‖cderiv r f z‖ ≤ M / r :=
begin
  have hM : 0 ≤ M,
  { obtain ⟨w, hw⟩ : (sphere z r).nonempty := normed_space.sphere_nonempty.mpr hr.le,
    exact (norm_nonneg _).trans (hf w hw) },
  have h1 : ∀ w ∈ sphere z r, ‖((w - z) ^ 2)⁻¹ • f w‖ ≤ M / r ^ 2,
  { intros w hw,
    simp only [mem_sphere_iff_norm, norm_eq_abs] at hw,
    simp only [norm_smul, inv_mul_eq_div, hw, norm_eq_abs, map_inv₀, complex.abs_pow],
    exact div_le_div hM (hf w hw) (sq_pos_of_pos hr) le_rfl },
  have h2 := circle_integral.norm_integral_le_of_norm_le_const hr.le h1,
  simp only [cderiv, norm_smul],
  refine (mul_le_mul le_rfl h2 (norm_nonneg _) (norm_nonneg _)).trans (le_of_eq _),
  field_simp [_root_.abs_of_nonneg real.pi_pos.le, real.pi_pos.ne.symm, hr.ne.symm],
  ring
end

lemma cderiv_sub (hr : 0 < r) (hf : continuous_on f (sphere z r))
  (hg : continuous_on g (sphere z r)) :
  cderiv r (f - g) z = cderiv r f z - cderiv r g z :=
begin
  have h1 : continuous_on (λ (w : ℂ), ((w - z) ^ 2)⁻¹) (sphere z r),
  { refine ((continuous_id'.sub continuous_const).pow 2).continuous_on.inv₀ (λ w hw h, hr.ne _),
    rwa [mem_sphere_iff_norm, sq_eq_zero_iff.mp h, norm_zero] at hw },
  simp_rw [cderiv, ← smul_sub],
  congr' 1,
  simpa only [pi.sub_apply, smul_sub] using circle_integral.integral_sub
    ((h1.smul hf).circle_integrable hr.le) ((h1.smul hg).circle_integrable hr.le)
end

lemma norm_cderiv_lt (hr : 0 < r) (hfM : ∀ w ∈ sphere z r, ‖f w‖ < M)
  (hf : continuous_on f (sphere z r)) :
  ‖cderiv r f z‖ < M / r :=
begin
  obtain ⟨L, hL1, hL2⟩ : ∃ L < M, ∀ w ∈ sphere z r, ‖f w‖ ≤ L,
  { have e1 : (sphere z r).nonempty := normed_space.sphere_nonempty.mpr hr.le,
    have e2 : continuous_on (λ w, ‖f w‖) (sphere z r),
      from continuous_norm.comp_continuous_on hf,
    obtain ⟨x, hx, hx'⟩ := (is_compact_sphere z r).exists_forall_ge e1 e2,
    exact ⟨‖f x‖, hfM x hx, hx'⟩ },
  exact (norm_cderiv_le hr hL2).trans_lt ((div_lt_div_right hr).mpr hL1)
end

lemma norm_cderiv_sub_lt (hr : 0 < r) (hfg : ∀ w ∈ sphere z r, ‖f w - g w‖ < M)
  (hf : continuous_on f (sphere z r)) (hg : continuous_on g (sphere z r)) :
  ‖cderiv r f z - cderiv r g z‖ < M / r :=
cderiv_sub hr hf hg ▸ norm_cderiv_lt hr hfg (hf.sub hg)

lemma tendsto_uniformly_on.cderiv (hF : tendsto_uniformly_on F f φ (cthickening δ K)) (hδ : 0 < δ)
  (hFn : ∀ᶠ n in φ, continuous_on (F n) (cthickening δ K)) :
  tendsto_uniformly_on (cderiv δ ∘ F) (cderiv δ f) φ K :=
begin
  by_cases φ = ⊥,
  { simp only [h, tendsto_uniformly_on, eventually_bot, implies_true_iff]},
  haveI : φ.ne_bot := ne_bot_iff.2 h,
  have e1 : continuous_on f (cthickening δ K) := tendsto_uniformly_on.continuous_on hF hFn,
  rw [tendsto_uniformly_on_iff] at hF ⊢,
  rintro ε hε,
  filter_upwards [hF (ε * δ) (mul_pos hε hδ), hFn] with n h h' z hz,
  simp_rw [dist_eq_norm] at h ⊢,
  have e2 : ∀ w ∈ sphere z δ, ‖f w - F n w‖ < ε * δ,
    from λ w hw1, h w (closed_ball_subset_cthickening hz δ (sphere_subset_closed_ball hw1)),
  have e3 := sphere_subset_closed_ball.trans (closed_ball_subset_cthickening hz δ),
  have hf : continuous_on f (sphere z δ),
    from e1.mono (sphere_subset_closed_ball.trans (closed_ball_subset_cthickening hz δ)),
  simpa only [mul_div_cancel _ hδ.ne.symm] using norm_cderiv_sub_lt hδ e2 hf (h'.mono e3)
end

end cderiv

section weierstrass

lemma tendsto_uniformly_on_deriv_of_cthickening_subset (hf : tendsto_locally_uniformly_on F f φ U)
  (hF : ∀ᶠ n in φ, differentiable_on ℂ (F n) U) {δ : ℝ} (hδ: 0 < δ) (hK : is_compact K)
  (hU : is_open U) (hKU : cthickening δ K ⊆ U) :
  tendsto_uniformly_on (deriv ∘ F) (cderiv δ f) φ K :=
begin
  have h1 : ∀ᶠ n in φ, continuous_on (F n) (cthickening δ K),
    by filter_upwards [hF] with n h using h.continuous_on.mono hKU,
  have h2 : is_compact (cthickening δ K),
    from is_compact_of_is_closed_bounded is_closed_cthickening hK.bounded.cthickening,
  have h3 : tendsto_uniformly_on F f φ (cthickening δ K),
    from (tendsto_locally_uniformly_on_iff_forall_is_compact hU).mp hf (cthickening δ K) hKU h2,
  apply (h3.cderiv hδ h1).congr,
  filter_upwards [hF] with n h z hz,
  exact cderiv_eq_deriv hU h hδ ((closed_ball_subset_cthickening hz δ).trans hKU)
end

lemma exists_cthickening_tendsto_uniformly_on (hf : tendsto_locally_uniformly_on F f φ U)
  (hF : ∀ᶠ n in φ, differentiable_on ℂ (F n) U) (hK : is_compact K) (hU : is_open U) (hKU : K ⊆ U) :
  ∃ δ > 0, cthickening δ K ⊆ U ∧ tendsto_uniformly_on (deriv ∘ F) (cderiv δ f) φ K :=
begin
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open hU hKU,
  exact ⟨δ, hδ, hKδ, tendsto_uniformly_on_deriv_of_cthickening_subset hf hF hδ hK hU hKδ⟩
end

/-- A locally uniform limit of holomorphic functions on an open domain of the complex plane is
holomorphic (the derivatives converge locally uniformly to that of the limit, which is proved
as `tendsto_locally_uniformly_on.deriv`). -/
theorem _root_.tendsto_locally_uniformly_on.differentiable_on [φ.ne_bot]
  (hf : tendsto_locally_uniformly_on F f φ U) (hF : ∀ᶠ n in φ, differentiable_on ℂ (F n) U)
  (hU : is_open U) :
  differentiable_on ℂ f U :=
begin
  rintro x hx,
  obtain ⟨K, ⟨hKx, hK⟩, hKU⟩ := (compact_basis_nhds x).mem_iff.mp (hU.mem_nhds hx),
  obtain ⟨δ, hδ, -, h1⟩ := exists_cthickening_tendsto_uniformly_on hf hF hK hU hKU,
  have h2 : interior K ⊆ U := interior_subset.trans hKU,
  have h3 : ∀ᶠ n in φ, differentiable_on ℂ (F n) (interior K),
    filter_upwards [hF] with n h using h.mono h2,
  have h4 : tendsto_locally_uniformly_on F f φ (interior K) := hf.mono h2,
  have h5 : tendsto_locally_uniformly_on (deriv ∘ F) (cderiv δ f) φ (interior K),
    from h1.tendsto_locally_uniformly_on.mono interior_subset,
  have h6 : ∀ x ∈ interior K, has_deriv_at f (cderiv δ f x) x,
    from λ x h, has_deriv_at_of_tendsto_locally_uniformly_on'
      is_open_interior h5 h3 (λ _, h4.tendsto_at) h,
  have h7 : differentiable_on ℂ f (interior K),
    from λ x hx, (h6 x hx).differentiable_at.differentiable_within_at,
  exact (h7.differentiable_at (interior_mem_nhds.mpr hKx)).differentiable_within_at
end

lemma _root_.tendsto_locally_uniformly_on.deriv (hf : tendsto_locally_uniformly_on F f φ U)
  (hF : ∀ᶠ n in φ, differentiable_on ℂ (F n) U) (hU : is_open U) :
  tendsto_locally_uniformly_on (deriv ∘ F) (deriv f) φ U :=
begin
  rw [tendsto_locally_uniformly_on_iff_forall_is_compact hU],
  by_cases φ = ⊥,
  { simp only [h, tendsto_uniformly_on, eventually_bot, implies_true_iff] },
  haveI : φ.ne_bot := ne_bot_iff.2 h,
  rintro K hKU hK,
  obtain ⟨δ, hδ, hK4, h⟩ := exists_cthickening_tendsto_uniformly_on hf hF hK hU hKU,
  refine h.congr_right (λ z hz, cderiv_eq_deriv hU (hf.differentiable_on hF hU) hδ _),
  exact (closed_ball_subset_cthickening hz δ).trans hK4,
end

end weierstrass

section tsums

/-- If the terms in the sum `∑' (i : ι), F i` are uniformly bounded on `U` by a
summable function, and each term in the sum is differentiable on `U`, then so is the sum. -/
lemma differentiable_on_tsum_of_summable_norm {u : ι → ℝ}
  (hu : summable u) (hf : ∀ (i : ι), differentiable_on ℂ (F i) U) (hU : is_open U)
  (hF_le : ∀ (i : ι) (w : ℂ), w ∈ U → ‖F i w‖ ≤ u i) :
  differentiable_on ℂ (λ w : ℂ, ∑' (i : ι), F i w) U :=
begin
  classical,
  have hc := (tendsto_uniformly_on_tsum hu hF_le).tendsto_locally_uniformly_on,
  refine hc.differentiable_on (eventually_of_forall $ λ s, _) hU,
  exact differentiable_on.sum (λ i hi, hf i),
end

/-- If the terms in the sum `∑' (i : ι), F i` are uniformly bounded on `U` by a
summable function, then the sum of `deriv F i` at a point in `U` is the derivative of the
sum. -/
lemma has_sum_deriv_of_summable_norm {u : ι → ℝ}
  (hu : summable u) (hf : ∀ (i : ι), differentiable_on ℂ (F i) U) (hU : is_open U)
  (hF_le : ∀ (i : ι) (w : ℂ), w ∈ U → ‖F i w‖ ≤ u i) (hz : z ∈ U) :
  has_sum (λ (i : ι), deriv (F i) z) (deriv (λ w : ℂ, ∑' (i : ι), F i w) z) :=
begin
  rw has_sum,
  have hc := (tendsto_uniformly_on_tsum hu hF_le).tendsto_locally_uniformly_on,
  convert (hc.deriv (eventually_of_forall $ λ s, differentiable_on.sum
    (λ i hi, hf i)) hU).tendsto_at hz using 1,
  ext1 s,
  exact (deriv_sum (λ i hi, (hf i).differentiable_at (hU.mem_nhds hz))).symm,
end

end tsums

end complex
