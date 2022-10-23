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

lemma vector_field_cont_mdiff_at_fix_ext_chart
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {n : ℕ∞} {v : M → tangent_bundle I M} (hv : ∀ x, (v x).1 = x) (x₀ : M) {x : M}
  (hx : x ∈ (ext_chart_at I x₀).source) :
  cont_mdiff_at I I.tangent n v x ↔ continuous_at v x ∧
    cont_diff_within_at 𝕜 n (written_in_ext_chart_at I I.tangent x₀ v)
      (set.range I) ((ext_chart_at I x₀) x) :=
begin
  refine cont_mdiff_at_fix_ext_chart x₀ hx _,
  rw [ext_chart_at_source, basic_smooth_vector_bundle_core.mem_chart_source_iff, hv, hv,
  ←ext_chart_at_source I],
  exact hx
end

lemma vector_field_cont_diff_on_snd_of_cont_mdiff
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {n : ℕ∞} {v : M → tangent_bundle I M} (h₁ : ∀ x, (v x).1 = x)
  (h₂ : cont_mdiff I I.tangent n v) (x₀ : M) :
  cont_diff_on 𝕜 n (λ (y : E), (written_in_ext_chart_at I I.tangent x₀ v y).snd)
    (ext_chart_at I x₀).target :=
begin
  intros y hy,
  rw ext_chart_at_target,
  apply cont_diff_within_at.mono _ (set.inter_subset_right _ _),
  rw ←local_equiv.right_inv _ hy,
  refine cont_diff_at.comp_cont_diff_within_at _ cont_diff_at_snd _,
  apply ((vector_field_cont_mdiff_at_fix_ext_chart h₁ _ _).mp h₂.cont_mdiff_at).2,
  exact local_equiv.map_target _ hy
end

variables
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [proper_space E]
  {H : Type*} [topological_space H] (I : model_with_corners ℝ E H)
  (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

/-- We apply the ODE existence theorem to a continuously differentiable vector field written in the
  preferred chart around the base point. We require that the base point not be on the boundary.
  Several useful properties of the solution are proven here, to be used in
  `exists_integral_curve_of_cont_mdiff_tangent_vector_field`. -/
lemma exists_integral_curve_of_cont_mdiff_tangent_vector_field_aux
  (v : M → tangent_bundle I M) (h₁ : ∀ x, (v x).1 = x) (h₂ : cont_mdiff I I.tangent 1 v)
  (x₀ : M) (hx : (ext_chart_at I x₀) x₀ ∈ interior (ext_chart_at I x₀).target) :
  ∃ (ε : ℝ) (hε : 0 < ε) (γ : ℝ → M), γ 0 = x₀ ∧ ∀ (t : ℝ), t ∈ metric.ball (0 : ℝ) ε →
    (γ t) ∈ (ext_chart_at I x₀).source ∧
    (ext_chart_at I x₀) (γ t) ∈ interior (ext_chart_at I x₀).target ∧
    continuous_at γ t ∧
    has_deriv_at ((ext_chart_at I x₀) ∘ γ) ((ext_chart_at I.tangent (v x₀)) (v (γ t))).2 t :=
begin
  have hx1 := is_open.mem_nhds (is_open_interior) hx,
  have hx2 := (vector_field_cont_diff_on_snd_of_cont_mdiff h₁ h₂ x₀).mono interior_subset,
  obtain ⟨ε, hε, f, hf1, hf2⟩ := ODE_solution_exists.at_ball_of_cont_diff_on_nhds_mem_set
    (λ y, (written_in_ext_chart_at I I.tangent x₀ v y).2)
    ((ext_chart_at I x₀) x₀) (interior (ext_chart_at I x₀).target) hx1 hx2 0,
  have hf1' : ((ext_chart_at I x₀).symm ∘ f) 0 = x₀,
  { rw function.comp_apply,
    rw hf1,
    exact ext_chart_at_to_inv I x₀ },
  refine ⟨ε, hε, (ext_chart_at I x₀).symm ∘ f, hf1', _⟩,
  intros t ht,
  obtain ⟨hf3, hf4⟩ := hf2 t ht,
  refine ⟨_, _, _, _⟩,
  { rw [function.comp_apply, ←set.mem_preimage],
    apply set.mem_of_mem_of_subset _ (local_equiv.target_subset_preimage_source _),
    apply set.mem_of_mem_of_subset _
      (interior_subset : interior (ext_chart_at I x₀).target ⊆ (ext_chart_at I x₀).target),
    rw ←set.mem_preimage,
    exact hf3 },
  { rw [function.comp_apply, ←set.mem_preimage, ←set.mem_preimage],
    apply set.mem_of_mem_of_subset _ (set.inter_subset_right (ext_chart_at I x₀).target _),
    rw [local_equiv.target_inter_inv_preimage_preimage,
      set.inter_eq_self_of_subset_right interior_subset],
    exact hf3 },
  { refine continuous_at.comp _ hf4.continuous_at,
    apply ext_chart_continuous_at_symm'',
    exact set.mem_of_mem_of_subset hf3 interior_subset },
  { rw [function.comp_apply, ←function.comp_apply v,
    ←function.comp_apply (ext_chart_at I.tangent (v x₀)), ←written_in_ext_chart_at],
    apply has_deriv_at.congr_of_eventually_eq hf4,
    rw filter.eventually_eq_iff_exists_mem,
    refine ⟨metric.ball 0 ε, is_open.mem_nhds metric.is_open_ball ht, _⟩,
    intros t' ht',
    rw [function.comp_apply, function.comp_apply],
    apply local_equiv.right_inv,
    exact set.mem_of_mem_of_subset (hf2 t' ht').1 interior_subset }
end

-- how to generalise / simplify?
lemma curve_change_chart
  (v : M → tangent_bundle I M) (h₁ : ∀ x, (v x).1 = x) (x₀ : M) (γ : ℝ → M) (t : ℝ)
  (hγ₁ : (γ t) ∈ (ext_chart_at I x₀).source)
  (hγ₂ : (ext_chart_at I x₀) (γ t) ∈ interior (ext_chart_at I x₀).target)
  (hd : has_deriv_at ((ext_chart_at I x₀) ∘ γ) ((ext_chart_at I.tangent (v x₀)) (v (γ t))).snd t) :
  has_deriv_at (((ext_chart_at I (γ t)) ∘ (ext_chart_at I x₀).symm) ∘ ((ext_chart_at I x₀) ∘ γ))
    ((ext_chart_at I.tangent (v (γ t))) (v (γ t))).snd t :=
begin
  have hI : set.range I ∈ nhds ((ext_chart_at I x₀) (γ t)) :=
    (mem_nhds_iff.mpr
      ⟨interior (ext_chart_at I x₀).target,
        set.subset.trans interior_subset (ext_chart_at_target_subset_range _ _),
        is_open_interior, hγ₂⟩),
  have : differentiable_at ℝ ((ext_chart_at I (γ t)) ∘ (ext_chart_at I (x₀)).symm)
    (((ext_chart_at I x₀) ∘ γ) t),
  { rw function.comp_apply,
    refine (((cont_diff_within_at_ext_coord_change I (γ t) x₀) _).differentiable_within_at
      le_top).differentiable_at hI,
    rw [local_equiv.trans_source, local_equiv.symm_source],
    use set.mem_of_mem_of_subset hγ₂ interior_subset,
    rw [set.mem_preimage, local_equiv.left_inv _ hγ₁],
    exact mem_ext_chart_source _ _ },
  have h := has_fderiv_at.comp_has_deriv_at t this.has_fderiv_at hd,
  have : (fderiv ℝ ((ext_chart_at I (γ t)) ∘ (ext_chart_at I (x₀)).symm)
    (((ext_chart_at I x₀) ∘ γ) t)) ((ext_chart_at I.tangent (v x₀)) (v (γ t))).snd =
    ((ext_chart_at I.tangent (v (γ t))) (v (γ t))).snd,
  { rw [ext_chart_at_coe, ext_chart_at_coe_symm],
    have hat : ∀ x : M, chart_at H x =
      (⟨chart_at H x, charted_space.chart_mem_atlas _ _⟩ : atlas H M).val := λ x, rfl,
    have hat' : ∀ x : M, (chart_at H x).symm =
      (⟨chart_at H x, charted_space.chart_mem_atlas _ _⟩ : atlas H M).val.symm := λ x, rfl,
    rw hat,
    rw hat',
    rw ←fderiv_within_of_mem_nhds hI,
    rw ext_chart_at_coe,
    rw function.comp_apply,
    rw ←tangent_bundle_core_coord_change,
    rw ext_chart_at_coe,
    rw function.comp_apply,
    rw model_with_corners.prod_apply,
    have h : ∀ (α β : Type*) (a : α) (b : β), (a, b).snd = b := λ _ _ _ _, rfl,
    rw h,
    rw model_with_corners_self_coe,
    rw id,
    rw basic_smooth_vector_bundle_core.to_charted_space_chart_at,
    have : ∀ (x : M) (z : (tangent_bundle_core I M).to_topological_vector_bundle_core.total_space),
      (tangent_bundle_core I M).chart (chart_mem_atlas H x) z = (chart_at H x z.proj,
      (tangent_bundle_core I M).coord_change (achart H z.proj) (achart H x) (achart H z.proj z.proj) z.2) := λ x z, rfl,
    rw this (v x₀).fst,
    have h : ∀ (a : H) (b : E), (a, b).snd = b := λ _ _, rfl,
    rw h,
    rw ←achart_def,
    rw ←achart_def,
    rw bundle.total_space.proj,
    rw h₁,
    rw h₁,
    rw hat,
    rw ←achart_def,
    have : ∀ x, (achart H x₀).val x = (achart H x₀) x := λ x, rfl,
    rw this,
    have h1 : γ t ∈ (achart H (γ t)).val.source := by simp,
    have h2 : γ t ∈ (achart H x₀).val.source,
    { rw achart_val,
      rw ←ext_chart_at_source I,
      exact hγ₁ },
    rw basic_smooth_vector_bundle_core.coord_change_comp_eq_self' _ h1 h2,
    simp only [local_homeomorph.coe_coe,
      basic_smooth_vector_bundle_core.coe_chart_at_fst,
      model_with_corners_self_local_equiv,
      ext_chart_at.equations._eqn_1,
      function.comp_app,
      local_equiv.prod_coe,
      local_equiv.coe_trans,
      model_with_corners_prod_to_local_equiv],
    rw local_equiv.refl_coe,
    rw id,
    rw basic_smooth_vector_bundle_core.to_charted_space_chart_at,
    rw basic_smooth_vector_bundle_core.chart_apply,
    rw basic_smooth_vector_bundle_core.coord_change_self',
    simp },
  rw this at h,
  exact h
end

lemma exists_integral_curve_of_cont_mdiff_tangent_vector_field
  (v : M → tangent_bundle I M) (h₁ : ∀ x, (v x).1 = x) (h₂ : cont_mdiff I I.tangent 1 v)
  (x₀ : M) (hx : (ext_chart_at I x₀) x₀ ∈ interior (ext_chart_at I x₀).target) :
  ∃ (ε : ℝ) (hε : 0 < ε) (γ : ℝ → M), γ 0 = x₀ ∧ ∀ (t : ℝ), t ∈ metric.ball (0 : ℝ) ε →
    has_mfderiv_at 𝓘(ℝ, ℝ) I γ t
      ((1 : ℝ →L[ℝ] ℝ).smul_right ((ext_chart_at I.tangent (v (γ t))) (v (γ t))).2) :=
begin
  obtain ⟨ε, hε, γ, hf1, hf2⟩ :=
    exists_integral_curve_of_cont_mdiff_tangent_vector_field_aux I M v h₁ h₂ x₀ hx,
  refine ⟨ε, hε, γ, hf1, _⟩,
  intros t ht,
  rw has_mfderiv_at,
  obtain ⟨hf3, hf4, hf5, hf6⟩ := hf2 t ht,
  use hf5,
  rw [ext_chart_model_space_apply, written_in_ext_chart_at, ext_chart_model_space_eq_id,
    local_equiv.refl_symm, local_equiv.refl_coe, function.comp.right_id],
  apply has_deriv_within_at.has_fderiv_within_at,
  apply has_deriv_at.has_deriv_within_at,
  have hd := curve_change_chart I M v h₁ x₀ γ t hf3 hf4 hf6,
  apply has_deriv_at.congr_of_eventually_eq hd,
  rw filter.eventually_eq_iff_exists_mem,
  refine ⟨metric.ball 0 ε, is_open.mem_nhds (metric.is_open_ball) ht, _⟩,
  intros t' ht',
  rw [function.comp_apply, function.comp_apply, function.comp_apply, local_equiv.left_inv],
  exact (hf2 t' ht').1
end

lemma curve_exists_boundaryless
  [hI : I.boundaryless]
  (v : M → tangent_bundle I M) (h₁ : ∀ x, (v x).1 = x) (h₂ : cont_mdiff I I.tangent 1 v) (x₀ : M) :
  ∃ (ε : ℝ) (hε : 0 < ε) (γ : ℝ → M), γ 0 = x₀ ∧ ∀ (t : ℝ), t ∈ metric.ball (0 : ℝ) ε →
    has_mfderiv_at 𝓘(ℝ, ℝ) I γ t
      ((1 : ℝ →L[ℝ] ℝ).smul_right ((ext_chart_at I.tangent (v (γ t))) (v (γ t))).2) :=
begin
  apply step2 I M v h₁ h₂,
  rw ext_chart_at_target,
  rw model_with_corners.boundaryless.range_eq_univ,
  rw set.inter_univ,
  rw is_open.interior_eq,
  { rw ←local_equiv.image_source_eq_target,
    rw ←set.univ_inter ((I.symm) ⁻¹' (((chart_at H x₀).to_local_equiv) '' (chart_at H x₀).to_local_equiv.source)),
    have : I.target = set.univ,
    { apply set.eq_univ_of_subset _ hI.range_eq_univ,
      rw set.range_subset_iff,
      intro y,
      apply local_equiv.map_source,
      rw model_with_corners.source_eq,
      exact set.mem_univ _ },
    rw ←this,
    rw ←model_with_corners.to_local_equiv_coe_symm,
    rw ←local_equiv.image_eq_target_inter_inv_preimage,
    { rw ←set.image_comp,
      rw model_with_corners.to_local_equiv_coe,
      rw local_homeomorph.coe_coe,
      rw ←ext_chart_at_coe,
      rw set.mem_image,
      use x₀,
      refine ⟨_, rfl⟩,
      exact charted_space.mem_chart_source _ _ },
    { rw model_with_corners.source_eq,
      exact set.subset_univ _ } },
  { apply (model_with_corners.continuous_symm _).is_open_preimage,
    exact local_homeomorph.open_target _ }
end
