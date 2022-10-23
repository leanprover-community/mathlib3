/-
Copyright (c) 2022 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import analysis.ODE.picard_lindelof
import geometry.manifold.cont_mdiff
import geometry.manifold.mfderiv

open_locale manifold

/-- Express cont_mdiff_at in a fixed chosen local chart. -/
lemma cont_mdiff_at_fix_ext_chart
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
  {n : ℕ∞} {f : M → M'} (x₀ : M) {x : M}
  (hx : x ∈ (ext_chart_at I x₀).source) (hfx : f x ∈ (ext_chart_at I' (f x₀)).source) :
  cont_mdiff_at I I' n f x ↔ continuous_at f x ∧
    cont_diff_within_at 𝕜 n (written_in_ext_chart_at I I' x₀ f)
      (set.range I) ((ext_chart_at I x₀) x) :=
begin
  rw [cont_mdiff_at, cont_mdiff_within_at],
  rw ext_chart_at_source at hx hfx,
  rw (cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_indep_chart
    (smooth_manifold_with_corners.chart_mem_maximal_atlas I x₀) hx
    (smooth_manifold_with_corners.chart_mem_maximal_atlas I' (f x₀)) hfx,
  apply and_congr (continuous_within_at_iff_continuous_at
    (is_open.mem_nhds is_open_univ (set.mem_univ x))),
  rw [cont_diff_within_at_prop, written_in_ext_chart_at, ext_chart_at_coe, ext_chart_at_coe,
    ext_chart_at_coe_symm, function.comp_apply, set.inter_comm _ (set.range I)],
  refine cont_diff_within_at_inter ((I.continuous_at_symm).preimage_mem_nhds _),
  rw I.left_inv,
  apply (local_homeomorph.continuous_at_symm _
    (local_homeomorph.map_source _ hx)).preimage_mem_nhds,
  exact is_open.mem_nhds is_open_univ (set.mem_univ _)
end

-- variables
--   {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [proper_space E]
--   {H : Type*} [topological_space H] (I : model_with_corners ℝ E H)
--   (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

-- lemma step1
--   (v : M → tangent_bundle I M) (h₁ : ∀ x, (v x).1 = x) (h₂ : cont_mdiff I I.tangent 1 v)
--   (x₀ : M) (hx : (ext_chart_at I x₀) x₀ ∈ interior (ext_chart_at I x₀).target) :
--   ∃ (ε : ℝ) (hε : 0 < ε) (γ : ℝ → M), γ 0 = x₀ ∧ ∀ (t : ℝ), t ∈ metric.ball (0 : ℝ) ε →
--     (γ t) ∈ (ext_chart_at I x₀).source ∧
--     (ext_chart_at I x₀) (γ t) ∈ interior (ext_chart_at I x₀).target ∧
--     continuous_at γ t ∧
--     has_deriv_at ((ext_chart_at I x₀) ∘ γ) ((ext_chart_at I.tangent (v x₀)) (v (γ t))).2 t :=
-- begin
--   obtain ⟨ε, hε, f, hf1, hf2⟩ := ODE_solution_exists.at_ball_of_cont_diff_on_nhds
--     (λ y, (written_in_ext_chart_at I I.tangent x₀ v y).2)
--     ((ext_chart_at I x₀) x₀) (ext_chart_at I x₀).target _ _ 0,
--   { have h1 : (f ⁻¹' interior (ext_chart_at I x₀).target) ∈ nhds (0 : ℝ),
--     { apply continuous_at.preimage_mem_nhds,
--       { exact (hf2 0 (metric.mem_ball_self hε)).continuous_at },
--       { apply is_open.mem_nhds is_open_interior,
--         rw hf1,
--         exact hx } },
--     rw metric.mem_nhds_iff at h1,
--     obtain ⟨r, hr1, hr2⟩ := h1,
--     refine ⟨min r ε, lt_min hr1 hε, (ext_chart_at I x₀).symm ∘ f, _, _⟩,
--     { rw function.comp_apply,
--       rw hf1,
--       exact ext_chart_at_to_inv I x₀ },
--     { intros t ht,
--       have hf2' := hf2 t
--         (set.mem_of_mem_of_subset ht (metric.ball_subset_ball (min_le_right r ε))),
--       refine ⟨_, _, _, _⟩,
--       { rw function.comp_apply,
--         rw ←set.mem_preimage,
--         apply set.mem_of_mem_of_subset _ (local_equiv.target_subset_preimage_source _),
--         apply set.mem_of_mem_of_subset _ (interior_subset : interior (ext_chart_at I x₀).target ⊆ (ext_chart_at I x₀).target),
--         rw ←set.mem_preimage,
--         apply set.mem_of_mem_of_subset _ hr2,
--         apply set.mem_of_mem_of_subset ht,
--         apply metric.ball_subset_ball,
--         exact min_le_left _ _ },
--       { rw function.comp_apply,
--         rw ←set.mem_preimage,
--         rw ←set.mem_preimage,
--         apply set.mem_of_mem_of_subset _ (set.inter_subset_right (ext_chart_at I x₀).target _),
--         rw local_equiv.target_inter_inv_preimage_preimage,
--         rw set.inter_eq_self_of_subset_right interior_subset,
--         rw ←set.mem_preimage,
--         apply set.mem_of_mem_of_subset ht,
--         apply set.subset.trans _ hr2,
--         apply metric.ball_subset_ball,
--         exact min_le_left _ _ },
--       { apply continuous_at.comp,
--         { have hft : f t ∈ (ext_chart_at I x₀).target,
--           { rw ←set.mem_preimage,
--             apply set.mem_of_mem_of_subset ht,
--             have : f ⁻¹' interior (ext_chart_at I x₀).target ⊆
--               f ⁻¹' (ext_chart_at I x₀).target,
--             { apply set.preimage_mono,
--               exact interior_subset },
--             apply set.subset.trans _ this,
--             apply set.subset.trans _ hr2,
--             apply metric.ball_subset_ball,
--             exact min_le_left r ε },
--           have : (ext_chart_at I x₀) ((ext_chart_at I x₀).symm (f t)) = f t,
--           { rw local_equiv.right_inv,
--             exact hft },
--           rw ←this,
--           apply ext_chart_continuous_at_symm',
--           rw ←set.mem_preimage,
--           apply set.mem_of_mem_of_subset hft,
--           exact local_equiv.target_subset_preimage_source _ },
--         { exact hf2'.continuous_at } },
--       rw function.comp_apply,
--       rw ←function.comp_apply v,
--       rw ←function.comp_apply (ext_chart_at I.tangent (v x₀)),
--       rw ←written_in_ext_chart_at,
--       apply has_deriv_at.congr_of_eventually_eq hf2',
--       rw filter.eventually_eq_iff_exists_mem,
--       use metric.ball 0 (min r ε),
--       split,
--       { rw is_open.mem_nhds_iff metric.is_open_ball,
--         exact ht },
--       { intros t' ht',
--         rw function.comp_apply,
--         rw function.comp_apply,
--         apply local_equiv.right_inv,
--         rw ←set.mem_preimage,
--         apply set.mem_of_mem_of_subset ht',
--         have : f ⁻¹' interior (ext_chart_at I x₀).target ⊆
--           f ⁻¹' (ext_chart_at I x₀).target,
--         { apply set.preimage_mono,
--           exact interior_subset },
--         apply set.subset.trans _ this,
--         apply set.subset.trans _ hr2,
--         apply metric.ball_subset_ball,
--         exact min_le_left r ε } } },
--   { rw mem_nhds_iff,
--     use interior (ext_chart_at I x₀).target,
--     use interior_subset,
--     use is_open_interior,
--     exact hx },
--   { intros y hy,
--     have h₂' : ∀ (x : M) (h : x ∈ (ext_chart_at I x₀).source), continuous_at v x ∧
--     cont_diff_within_at ℝ 1 ((ext_chart_at I.tangent (v x₀)) ∘ v ∘ (ext_chart_at I x₀).symm)
--       (set.range I) ((ext_chart_at I x₀) x),
--     { intros x h,
--       apply (cont_mdiff_at_fix_ext_chart x₀ h _).mp (h₂ x),
--       rw ext_chart_at_source,
--       rw basic_smooth_vector_bundle_core.mem_chart_source_iff,
--       rw h₁,
--       rw h₁,
--       rw ←ext_chart_at_source I,
--       exact h },
--     obtain ⟨h1, h2⟩ := h₂' ((ext_chart_at I x₀).symm y) (local_equiv.map_target _ hy),
--     rw local_equiv.right_inv _ hy at h2,
--     rw ←written_in_ext_chart_at at h2,
--     rw ext_chart_at_target,
--     apply cont_diff_within_at.mono _ (set.inter_subset_right _ _),
--     exact cont_diff_at.comp_cont_diff_within_at _ cont_diff_at_snd h2 }
-- end

-- lemma step2
--   (v : M → tangent_bundle I M) (h₁ : ∀ x, (v x).1 = x) (h₂ : cont_mdiff I I.tangent 1 v)
--   (x₀ : M) (hx : (ext_chart_at I x₀) x₀ ∈ interior (ext_chart_at I x₀).target) :
--   ∃ (ε : ℝ) (hε : 0 < ε) (γ : ℝ → M), γ 0 = x₀ ∧ ∀ (t : ℝ), t ∈ metric.ball (0 : ℝ) ε →
--     has_mfderiv_at 𝓘(ℝ, ℝ) I γ t
--       ((1 : ℝ →L[ℝ] ℝ).smul_right ((ext_chart_at I.tangent (v (γ t))) (v (γ t))).2) :=
-- begin
--   obtain ⟨ε, hε, γ, hf1, hf2⟩ := step1 I M v h₁ h₂ x₀ hx,
--   refine ⟨ε, hε, γ, hf1, _⟩,
--   intros t ht,
--   rw has_mfderiv_at,
--   obtain ⟨hf4, hf3, hfcon, hf2'⟩ := hf2 t ht,
--   use hfcon,
--   have : differentiable_at ℝ ((ext_chart_at I (γ t)) ∘ (ext_chart_at I (x₀)).symm)
--     (((ext_chart_at I x₀) ∘ γ) t),
--   { rw function.comp_apply,
--     have : differentiable_within_at ℝ ((ext_chart_at I (γ t)) ∘ (ext_chart_at I x₀).symm)
--       (set.range I) ((ext_chart_at I x₀) (γ t)) :=
--     ((cont_diff_within_at_ext_coord_change I (γ t) x₀) _).differentiable_within_at le_top,
--     { apply differentiable_within_at.differentiable_at this,
--       rw mem_nhds_iff,
--       use interior (ext_chart_at I x₀).target,
--       exact ⟨set.subset.trans interior_subset (ext_chart_at_target_subset_range _ _),
--         is_open_interior, hf3⟩ },
--     { rw local_equiv.trans_source,
--       rw local_equiv.symm_source,
--       use set.mem_of_mem_of_subset hf3 interior_subset,
--       rw set.mem_preimage,
--       rw local_equiv.left_inv _ hf4,
--       exact mem_ext_chart_source _ _ } },
--   have h := has_fderiv_at.comp_has_deriv_at t this.has_fderiv_at hf2',
--   have : (fderiv ℝ ((ext_chart_at I (γ t)) ∘ (ext_chart_at I (x₀)).symm)
--     (((ext_chart_at I x₀) ∘ γ) t)) ((ext_chart_at I.tangent (v x₀)) (v (γ t))).snd =
--     ((ext_chart_at I.tangent (v (γ t))) (v (γ t))).snd,
--   { rw ext_chart_at_coe,
--     rw ext_chart_at_coe_symm,
--     have hat : ∀ x : M, chart_at H x =
--       (⟨chart_at H x, charted_space.chart_mem_atlas _ _⟩ : atlas H M).val := λ x, rfl,
--     have hat' : ∀ x : M, (chart_at H x).symm =
--       (⟨chart_at H x, charted_space.chart_mem_atlas _ _⟩ : atlas H M).val.symm := λ x, rfl,
--     rw hat,
--     rw hat',
--     rw ←fderiv_within_of_mem_nhds,
--     rw ext_chart_at_coe,
--     rw function.comp_apply,
--     rw function.comp_apply,
--     rw ←tangent_bundle_core_coord_change,
--     { rw ext_chart_at_coe,
--       rw function.comp_apply,
--       rw model_with_corners.prod_apply,
--       have h : ∀ (α β : Type*) (a : α) (b : β), (a, b).snd = b := λ _ _ _ _, rfl,
--       rw h,
--       rw model_with_corners_self_coe,
--       rw id,
--       rw basic_smooth_vector_bundle_core.to_charted_space_chart_at,
--       have : ∀ (x : M) (z : (tangent_bundle_core I M).to_topological_vector_bundle_core.total_space),
--         (tangent_bundle_core I M).chart (chart_mem_atlas H x) z = (chart_at H x z.proj,
--         (tangent_bundle_core I M).coord_change (achart H z.proj) (achart H x) (achart H z.proj z.proj) z.2) := λ x z, rfl,
--       rw this (v x₀).fst,
--       have h : ∀ (a : H) (b : E), (a, b).snd = b := λ _ _, rfl,
--       rw h,
--       rw ←achart_def,
--       rw ←achart_def,
--       rw bundle.total_space.proj,
--       rw h₁,
--       rw h₁,
--       rw hat,
--       rw ←achart_def,
--       have : ∀ x, (achart H x₀).val x = (achart H x₀) x := λ x, rfl,
--       rw this,
--       have h1 : γ t ∈ (achart H (γ t)).val.source := by simp,
--       have h2 : γ t ∈ (achart H x₀).val.source,
--       { rw achart_val,
--         rw ←ext_chart_at_source I,
--         exact hf4 },
--       rw basic_smooth_vector_bundle_core.coord_change_comp_eq_self' _ h1 h2,
--       simp only [local_homeomorph.coe_coe,
--         basic_smooth_vector_bundle_core.coe_chart_at_fst,
--         model_with_corners_self_local_equiv,
--         ext_chart_at.equations._eqn_1,
--         function.comp_app,
--         local_equiv.prod_coe,
--         local_equiv.coe_trans,
--         model_with_corners_prod_to_local_equiv],
--       rw local_equiv.refl_coe,
--       rw id,
--       rw basic_smooth_vector_bundle_core.to_charted_space_chart_at,
--       rw basic_smooth_vector_bundle_core.chart_apply,
--       rw basic_smooth_vector_bundle_core.coord_change_self',
--       simp },
--     { rw ←filter.exists_mem_subset_iff,
--       use (ext_chart_at I x₀).target,
--       split,
--       { rw mem_nhds_iff,
--         use interior (ext_chart_at I x₀).target,
--         use interior_subset,
--         use is_open_interior,
--         exact hf3 },
--       { rw ext_chart_at_target,
--         exact set.inter_subset_right _ _ } } },
--   { rw this at h,
--     have h1 : written_in_ext_chart_at 𝓘(ℝ, ℝ) I t γ = ((ext_chart_at I (γ t)) ∘ γ) := rfl,
--     have h2 : (ext_chart_at 𝓘(ℝ, ℝ) t) t = t := rfl,
--     rw [h1, h2],
--     apply has_deriv_within_at.has_fderiv_within_at,
--     apply has_deriv_at.has_deriv_within_at,
--     apply has_deriv_at.congr_of_eventually_eq h,
--     rw filter.eventually_eq_iff_exists_mem,
--     use metric.ball (0 : ℝ) ε,
--     split,
--     { rw is_open.mem_nhds_iff (metric.is_open_ball),
--       exact ht },
--     { intros t' ht',
--       rw function.comp_apply,
--       rw function.comp_apply,
--       rw function.comp_apply,
--       rw local_equiv.left_inv,
--       exact (hf2 t' ht').1 } }
-- end

-- lemma curve_exists_boundaryless
--   [hI : I.boundaryless]
--   (v : M → tangent_bundle I M) (h₁ : ∀ x, (v x).1 = x) (h₂ : cont_mdiff I I.tangent 1 v) (x₀ : M) :
--   ∃ (ε : ℝ) (hε : 0 < ε) (γ : ℝ → M), γ 0 = x₀ ∧ ∀ (t : ℝ), t ∈ metric.ball (0 : ℝ) ε →
--     has_mfderiv_at 𝓘(ℝ, ℝ) I γ t
--       ((1 : ℝ →L[ℝ] ℝ).smul_right ((ext_chart_at I.tangent (v (γ t))) (v (γ t))).2) :=
-- begin
--   apply step2 I M v h₁ h₂,
--   rw ext_chart_at_target,
--   rw model_with_corners.boundaryless.range_eq_univ,
--   rw set.inter_univ,
--   rw is_open.interior_eq,
--   { rw ←local_equiv.image_source_eq_target,
--     rw ←set.univ_inter ((I.symm) ⁻¹' (((chart_at H x₀).to_local_equiv) '' (chart_at H x₀).to_local_equiv.source)),
--     have : I.target = set.univ,
--     { apply set.eq_univ_of_subset _ hI.range_eq_univ,
--       rw set.range_subset_iff,
--       intro y,
--       apply local_equiv.map_source,
--       rw model_with_corners.source_eq,
--       exact set.mem_univ _ },
--     rw ←this,
--     rw ←model_with_corners.to_local_equiv_coe_symm,
--     rw ←local_equiv.image_eq_target_inter_inv_preimage,
--     { rw ←set.image_comp,
--       rw model_with_corners.to_local_equiv_coe,
--       rw local_homeomorph.coe_coe,
--       rw ←ext_chart_at_coe,
--       rw set.mem_image,
--       use x₀,
--       refine ⟨_, rfl⟩,
--       exact charted_space.mem_chart_source _ _ },
--     { rw model_with_corners.source_eq,
--       exact set.subset_univ _ } },
--   { apply (model_with_corners.continuous_symm _).is_open_preimage,
--     exact local_homeomorph.open_target _ }
-- end
