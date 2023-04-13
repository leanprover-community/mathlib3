/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import measure_theory.function.continuous_map_dense
import measure_theory.integral.integral_eq_improper
import measure_theory.group.integration
import topology.continuous_function.zero_at_infty
import analysis.fourier.fourier_transform
import analysis.inner_product_space.dual

/-!
# The Riemann-Lebesgue Lemma

In this file we prove the Riemann-Lebesgue lemma for functions on finite-dimensional real vector
spaces: for any `L¹` function `f` on `V` (valued in some complete normed space `E`), the function

`λ w : V →L[ℝ] ℝ, ∫ (v : V), exp (↑(w v) * I) • f x`

tends to zero as `w → ∞`. This is proved first for continuous compactly-supported functions on
inner-product spaces; then we pass to general `L¹` functions using the density of continuous
compactly-supported functions in `L¹` space. Finally we generalise from inner-product spaces to
arbitrary spaces, by choosing a continuous linear equivalence to an inner-product space.

## Main results

- `tendsto_integral_exp_inner_smul_cocompact` : for `V` a finite-dimensional real inner product
  space and `f : V → E` integrable, the function `λ w : V, ∫ v : V, exp (⟪w, v⟫ * I) • f v` tends
  to 0 wrt `cocompact V`.
- `tendsto_integral_exp_smul_cocompact` : for `V` a finite-dimensional real vector space (endowed
  with its unique Hausdorff topological vector space structure), and `W` the dual of `V`, the
  function `λ w : W, ∫ v : V, exp (w v * I) • f v` tends to wrt `cocompact W`.
- `real.tendsto_integral_exp_smul_cocompact`: special case of functions on `ℝ`.
-/

open measure_theory filter complex set finite_dimensional
open_locale filter topology real ennreal fourier_transform real_inner_product_space

variables {E V : Type*} [normed_add_comm_group E] [normed_space ℂ E] {f : V → E}

section inner_product_space

variables [normed_add_comm_group V]

local attribute [instance, priority 500] borel

lemma borel_space_of_normed_add_comm_group : borel_space V := borel_space.mk (by refl)
local attribute [instance, priority 500] borel_space_of_normed_add_comm_group

variables [inner_product_space ℝ V] [finite_dimensional ℝ V]

/-- The integrand in the Riemann-Lebesgue lemma is integrable. -/
lemma fourier_integrand_integrable (hf : integrable f) (w : V) :
  integrable (λ v : V, exp (⟪w, v⟫ * I) • f v) :=
begin
  rw ←integrable_norm_iff,
  { simpa only [norm_smul, norm_exp_of_real_mul_I, one_mul] using hf.norm },
  { refine (continuous.ae_strongly_measurable _).smul hf.1,
    refine complex.continuous_exp.comp ((continuous_of_real.comp _).mul continuous_const),
    exact continuous_inner.comp
      (continuous_const.prod_mk continuous_id : continuous (_ : V → V × V)), }
end

variables [complete_space E]

/-- Shifting `f` by `(π / ‖w‖ ^ 2) • w` negates the integral in the Riemann-Lebesgue lemma. -/
lemma fourier_integral_half_period_translate {w : V} (hw : w ≠ 0) :
  ∫ (v : V), exp (⟪w, v⟫ * I) • f (v + (π / ‖w‖ ^ 2) • w) = -∫ (v : V), exp (⟪w, v⟫ * I) • f v :=
begin
  let w' := (π / ‖w‖ ^ 2) • w,
  have hw' : ⟪w, w'⟫ = π,
  { rw [inner_smul_right, inner_self_eq_norm_sq_to_K, is_R_or_C.coe_real_eq_id, id.def,
      div_mul_cancel],
    rwa [ne.def, sq_eq_zero_iff, norm_eq_zero] },
  have : (λ v : V, exp (⟪w, v⟫ * I) • f (v + w')) =
    (λ v : V, (λ x : V, -exp (⟪w, x⟫ * I) • f x) (v + w')), by simp only [inner_add_right, hw',
    of_real_add, add_mul, exp_add, exp_pi_mul_I, mul_neg_one, neg_neg],
  rw [this, integral_add_right_eq_self],
  simp_rw [neg_smul, integral_neg],
end

/-- Rewrite the Riemann-Lebesgue integral in a form that allows us to use uniform continuity. -/
lemma fourier_integral_eq_half_sub_half_period_translate {w : V} (hw : w ≠ 0) (hf : integrable f) :
  ∫ v : V, exp (⟪w, v⟫ * I) • f v =
  (1 / (2 : ℂ)) • ∫ v : V, exp (⟪w, v⟫ * I) • (f v - f (v + (π / ‖w‖ ^ 2) • w)) :=
begin
  simp_rw [smul_sub],
  rw [integral_sub, fourier_integral_half_period_translate hw, sub_eq_add_neg, neg_neg,
    ←two_smul ℂ _, ←@smul_assoc _ _ _ _ _ _ (is_scalar_tower.left ℂ), smul_eq_mul],
  norm_num,
  exacts [fourier_integrand_integrable hf w,
    fourier_integrand_integrable (hf.comp_add_right _) w],
end

/-- Riemann-Lebesgue Lemma for continuous and compactly-supported functions: the integral
`∫ v, exp (⟪w, v⟫ * I) • f v` tends to 0 as `‖w‖ → ∞`.  -/
lemma tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support
  (hf1 : continuous f) (hf2 : has_compact_support f) :
  tendsto (λ w : V, ∫ v : V, exp (⟪w, v⟫ * I) • f v) (cocompact V) (𝓝 0) :=
begin
  refine normed_add_comm_group.tendsto_nhds_zero.mpr (λ ε hε, _),
  suffices : ∃ (T : ℝ), ∀ (w : V), T ≤ ‖w‖ → ‖∫ (v : V), exp (⟪w, v⟫ * I) • f v‖ < ε,
  { simp_rw [←comap_dist_left_at_top_eq_cocompact (0 : V), eventually_comap, eventually_at_top,
      dist_eq_norm', sub_zero],
    exact let ⟨T, hT⟩ := this in ⟨T, (λ b hb v hv, hT v (hv.symm ▸ hb))⟩ },
  obtain ⟨R, hR_pos, hR_bd⟩ : ∃ (R : ℝ), 0 < R ∧ ∀ (x : V), R ≤ ‖x‖ → f x = 0,
    from hf2.exists_pos_le_norm,
  let A := {v : V | ‖v‖ ≤ R + 1},
  have mA : measurable_set A,
  { suffices : A = metric.closed_ball (0 : V) (R + 1),
    by { rw this, exact metric.is_closed_ball.measurable_set },
    simp_rw [A, metric.closed_ball, dist_eq_norm, sub_zero] },
  obtain ⟨B, hB_pos, hB_vol⟩ : ∃ (B : nnreal), 0 < B ∧ volume A ≤ B,
  { have hc : is_compact A, by simpa only [metric.closed_ball, dist_eq_norm, sub_zero]
      using is_compact_closed_ball (0 : V) _,
    let B₀ := volume A,
    replace hc : B₀ < ⊤ := hc.measure_lt_top,
    refine ⟨B₀.to_nnreal + 1, add_pos_of_nonneg_of_pos B₀.to_nnreal.coe_nonneg one_pos, _⟩,
    rw [ennreal.coe_add, ennreal.coe_one, ennreal.coe_to_nnreal hc.ne],
    exact le_self_add },
  --* Use uniform continuity to choose δ such that `‖x - y‖ < δ` implies `‖f x - f y‖ < ε / B`.
  obtain ⟨δ, hδ1, hδ2⟩ := metric.uniform_continuous_iff.mp
    (hf2.uniform_continuous_of_continuous hf1) (ε / B) (div_pos hε hB_pos),
  refine ⟨max π (1 + π / δ), λ w hw_bd, _⟩,
  let w' := (π / ‖w‖ ^ 2) • w,
  have hw_ne : w ≠ 0,
  { contrapose! hw_bd, rw [hw_bd, norm_zero], exact lt_max_of_lt_left real.pi_pos },
  have hw'_nm : ‖w'‖ = π / ‖w‖,
  { rw [norm_smul, norm_div, real.norm_of_nonneg real.pi_pos.le, norm_pow, norm_norm,
      sq, ←div_div, div_mul_cancel _ (norm_eq_zero.not.mpr hw_ne)] },
  --* Rewrite integral in terms of `f v - f (v + w')`.
  rw [fourier_integral_eq_half_sub_half_period_translate hw_ne
    (hf1.integrable_of_has_compact_support hf2), norm_smul, norm_eq_abs, ←complex.of_real_one,
    ←of_real_bit0, ←of_real_div, complex.abs_of_nonneg one_half_pos.le],
  have : ε = (1 / 2) * (2 * ε), by { field_simp, rw mul_comm },
  rw [this, mul_lt_mul_left (one_half_pos : (0:ℝ) < 1/2)],
  refine lt_of_le_of_lt (norm_integral_le_integral_norm _) _,
  simp_rw [norm_smul, norm_exp_of_real_mul_I, one_mul],
  --* Show integral can be taken over A only.
  have int_A : ∫ (v : V), ‖f v - f (v + w')‖ = ∫ v in A, ‖f v - f (v + w')‖,
  { refine (set_integral_eq_integral_of_forall_compl_eq_zero (λ v hv, _)).symm,
    dsimp only [A] at hv,
    simp only [A, mem_set_of_eq, not_le] at hv,
    rw [hR_bd v _, hR_bd (v + w') _, sub_zero, norm_zero],
    { rw ←sub_neg_eq_add,
      refine le_trans _ (norm_sub_norm_le _ _),
      rw [le_sub_iff_add_le, norm_neg],
      refine le_trans _ hv.le,
      rw [add_le_add_iff_left, hw'_nm],
      exact (div_le_one $ norm_pos_iff.mpr hw_ne).mpr ((le_max_left _ _).trans hw_bd) },
    { exact ((le_add_iff_nonneg_right _).mpr zero_le_one).trans hv.le } },
  rw int_A,
  --* Bound integral using fact that ‖f v - f (v + w')‖ is small.
  have bdA : ∀ v : V, (v ∈ A) → ‖ ‖f v - f (v + w') ‖ ‖ ≤ ε / B,
  { simp_rw norm_norm,
    refine (λ x _, le_of_lt _),
    simp_rw dist_eq_norm at hδ2,
    apply hδ2,
    rw [sub_add_cancel', norm_neg, hw'_nm, div_lt_iff (norm_pos_iff.mpr hw_ne), ←div_lt_iff' hδ1],
    refine (lt_add_of_pos_left _ zero_lt_one).trans_le ((le_max_right π (1 + π / δ)).trans hw_bd) },
  have bdA2 := norm_set_integral_le_of_norm_le_const (hB_vol.trans_lt ennreal.coe_lt_top) bdA _,
  swap, { apply continuous.ae_strongly_measurable,
    exact (continuous_norm.comp $ continuous.sub hf1 $ continuous.comp hf1 $
    continuous_id'.add continuous_const) },
  have : ‖ _ ‖ = ∫ (v : V) in A, ‖f v - f (v + w')‖ :=
    real.norm_of_nonneg (set_integral_nonneg mA (λ x hx, norm_nonneg _)),
  rw this at bdA2,
  refine bdA2.trans_lt _,
  rw [div_mul_eq_mul_div, div_lt_iff (nnreal.coe_pos.mpr hB_pos), mul_comm (2 : ℝ), mul_assoc,
    mul_lt_mul_left hε],
  rw ← ennreal.to_real_le_to_real at hB_vol,
  { refine hB_vol.trans_lt _,
    rw [(by refl : (↑B : ennreal).to_real = ↑B), two_mul],
    exact lt_add_of_pos_left _ hB_pos },
  exacts [(hB_vol.trans_lt ennreal.coe_lt_top).ne, ennreal.coe_lt_top.ne],
end

/- If `f` and `g` are close in `L¹` norm, then their Fourier transforms are close in sup norm. -/
lemma fourier_L1_cts {f g : V → E} (hf : integrable f) (hg : integrable g) {ε : ℝ}
  (hfg : ∫ v, ‖f v - g v‖ ≤ ε) (w : V) :
  ‖(∫ v, exp (⟪w, v⟫ * I) • f v) - (∫ v, exp (⟪w, v⟫ * I) • g v)‖ ≤ ε :=
begin
  rw ←integral_sub (fourier_integrand_integrable hf _) (fourier_integrand_integrable hg _),
  refine (norm_integral_le_integral_norm _).trans ((integral_mono _ (hf.sub hg).norm _).trans hfg),
  { exact ((fourier_integrand_integrable hf _).sub (fourier_integrand_integrable hg _)).norm },
  intro x,
  simpa only [←smul_sub, norm_smul, norm_eq_abs, abs_exp_of_real_mul_I, one_mul]
end

/-- Riemann-Lebesgue lemma for integrable functions on a real inner-product space. -/
theorem tendsto_integral_exp_inner_smul_cocompact (hfi : integrable f) :
  tendsto (λ w : V, ∫ v, exp (⟪w, v⟫ * I) • f v) (cocompact V) (𝓝 0) :=
metric.tendsto_nhds.mpr $ λ ε hε, begin
  haveI : normal_space V := normal_space_of_t3_second_countable V,
  obtain ⟨g, hg3, hg1, -, hg2⟩ :=
    hfi.exists_has_compact_support_integral_sub_le (div_pos hε two_pos),
  refine ((metric.tendsto_nhds.mp
    (tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support hg1 hg2)) _
    (div_pos hε two_pos)).mp (eventually_of_forall (λ t hI, _)),
  rw dist_eq_norm at hI ⊢,
  have := add_lt_add_of_le_of_lt
    (fourier_L1_cts hfi (hg1.integrable_of_has_compact_support hg2) hg3 t) hI,
  rw add_halves at this,
  refine ((le_of_eq _).trans (norm_add_le _ _)).trans_lt this,
  simp only [sub_zero, sub_add_cancel],
end

theorem real.tendsto_integral_exp_smul_cocompact {f : ℝ → E} (hfi : integrable f) :
  tendsto (λ w : ℝ, ∫ v : ℝ, exp (↑(v * w) * I) • f v) (cocompact ℝ) (𝓝 0) :=
begin
  convert tendsto_integral_exp_inner_smul_cocompact hfi,
  ext1 w,
  congr' 1 with v : 1,
  congr' 3,
  rw [mul_comm, of_real_inj, is_R_or_C.inner_apply, is_R_or_C.conj_to_real],
end

/-- Riemann-Lebesgue lemma for integrable functions, formulated via dual space.
  **Do not use** -- it is only a stepping stone to `tendsto_integral_exp_smul_cocompact`. -/
theorem tendsto_integral_exp_smul_cocompact_of_inner_product
  (μ : measure V) [μ.is_add_haar_measure] (hfi : integrable f μ) :
  tendsto (λ w : V →L[ℝ] ℝ, ∫ v, exp (w v * I) • f v ∂μ) (cocompact (V →L[ℝ] ℝ)) (𝓝 0) :=
begin
  obtain ⟨C, C_ne_zero, C_ne_top, hC⟩ := μ.is_add_haar_measure_eq_smul_is_add_haar_measure volume,
  rw hC at hfi ⊢,
  rw integrable_smul_measure C_ne_zero C_ne_top at hfi,
  simp_rw integral_smul_measure,
  rw ←(smul_zero _ : C.to_real • (0 : E) = 0),
  apply tendsto.const_smul,
  let A := (inner_product_space.to_dual ℝ V).symm,
  have : (λ w : V →L[ℝ] ℝ, ∫ v, exp (w v * I) • f v) = (λ w : V, ∫ v, exp (⟪w, v⟫ * I) • f v) ∘ A,
  { ext1 w,
    congr' 1 with v : 1,
    rw inner_product_space.to_dual_symm_apply },
  rw this,
  exact (tendsto_integral_exp_inner_smul_cocompact hfi).comp
    A.to_homeomorph.to_cocompact_map.cocompact_tendsto',
end

end inner_product_space

section no_inner_product

variables
  [add_comm_group V] [topological_space V] [topological_add_group V] [t2_space V]
  [measurable_space V] [borel_space V]
  [module ℝ V] [has_continuous_smul ℝ V] [finite_dimensional ℝ V]
  [complete_space E]

/-- Riemann-Lebesgue lemma for integrable functions on a finite-dimensional real vector space,
formulated via dual space. -/
theorem tendsto_integral_exp_smul_cocompact
  (μ : measure V) [μ.is_add_haar_measure] (hfi : integrable f μ) :
  tendsto (λ w : V →L[ℝ] ℝ, ∫ v, exp (w v * I) • f v ∂μ) (cocompact (V →L[ℝ] ℝ)) (𝓝 0) :=
begin
  -- We have already proved the result for inner-product spaces, formulated in a way which doesn't
  -- refer to the inner product. So we choose an arbitrary inner-product space isomorphic to V
  -- and port the result over from there.
  let V' := euclidean_space ℝ (fin (finrank ℝ V)),
  have : finrank ℝ V = finrank ℝ V',
    by rw finrank_euclidean_space_fin,
  -- note `nonempty_continuous_linear_equiv_of_finrank_eq` requires a normed-space structure
  let A₀ := (nonempty_linear_equiv_of_finrank_eq this).some,
  let A : V ≃L[ℝ] V' :=
  { continuous_to_fun := A₀.to_linear_map.continuous_of_finite_dimensional,
    continuous_inv_fun := A₀.symm.to_linear_map.continuous_of_finite_dimensional,
    .. A₀ },
  letI : measurable_space V' := borel V',
  haveI : borel_space V' := borel_space.mk (by refl),
  -- various equivs derived from A
  let Aₘ : measurable_equiv V V' := A.to_homeomorph.to_measurable_equiv,
  -- isomorphism between duals derived from A -- need to do continuity as a separate step in order
  -- to apply `linear_map.continuous_of_finite_dimensional`.
  let Adualₗ : (V →L[ℝ] ℝ) ≃ₗ[ℝ] (V' →L[ℝ] ℝ) :=
  { to_fun := λ e, e.comp A.symm.to_continuous_linear_map,
    inv_fun := λ e, e.comp A.to_continuous_linear_map,
    map_add' := by
    { intros e f, ext1 v, simp only [continuous_linear_map.coe_comp', function.comp_app,
      continuous_linear_map.add_apply] },
    map_smul' := by
    { intros x f, ext1 v, simp only [ring_hom.id_apply, continuous_linear_map.coe_comp',
        function.comp_app, continuous_linear_map.smul_apply] },
    left_inv := by
    { intro w, ext1 v, simp only [continuous_linear_equiv.coe_def_rev,
      continuous_linear_map.coe_comp', continuous_linear_equiv.coe_coe,
      function.comp_app, continuous_linear_equiv.symm_apply_apply] },
    right_inv := by
    { intro w, ext1 v, simp only [continuous_linear_equiv.coe_def_rev,
        continuous_linear_map.coe_comp', continuous_linear_equiv.coe_coe,
        function.comp_app, continuous_linear_equiv.apply_symm_apply] }, },
  let Adual : (V →L[ℝ] ℝ) ≃L[ℝ] (V' →L[ℝ] ℝ) :=
  { continuous_to_fun := Adualₗ.to_linear_map.continuous_of_finite_dimensional,
    continuous_inv_fun := Adualₗ.symm.to_linear_map.continuous_of_finite_dimensional,
    .. Adualₗ },
  have hfi' : integrable (f ∘ A.symm) (μ.map Aₘ),
  { rwa [integrable_map_equiv Aₘ, homeomorph.to_measurable_equiv_coe,
      continuous_linear_equiv.coe_to_homeomorph, function.comp.assoc,
      continuous_linear_equiv.symm_comp_self] },
  haveI : (μ.map Aₘ).is_add_haar_measure,
    from measure.map_continuous_linear_equiv.is_add_haar_measure _ A,
  convert (tendsto_integral_exp_smul_cocompact_of_inner_product (μ.map Aₘ) hfi').comp
    Adual.to_homeomorph.to_cocompact_map.cocompact_tendsto',
  ext1 w,
  rw [function.comp_app, integral_map_equiv],
  congr' 1 with v : 1,
  congr;
  exact (continuous_linear_equiv.symm_apply_apply A v).symm,
end

end no_inner_product
