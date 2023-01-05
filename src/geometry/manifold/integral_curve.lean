/-
Copyright (c) 2022 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import analysis.ODE.picard_lindelof
import geometry.manifold.cont_mdiff
import geometry.manifold.mfderiv

/-!
# Integral curves of vector fields on a manifold

For any continuously differentiable vector field on a manifold `M` and any chosen non-boundary point
`x₀ : M`, an integral curve `γ : ℝ → M` exists such that `γ t₀ = x₀` and the tangent vector of `γ`
at `t` coincides with the vector field at `γ t` for all `t` within an open interval around `t₀`.

As a corollary, such an integral curve exists for any starting point `x₀` if `M` is a manifold
without boundary.

## Implementation details

Since there is already an ODE solution existence theorem
`ODE_solution_exists.at_ball_of_cont_diff_on_nhds`, the bulk of this file is to convert statements
about manifolds to statements about the model space. This comes in a few steps:
1. Express the smoothness of the vector field `v` in a single fixed chart around the starting point
`x₀`.
2. Use the ODE solution existence theorem to obtain a curve `γ : ℝ → M` whose derivative coincides
with the vector field (stated in the local chart around `x₀`).
3. Same as 2 but now stated in the local chart around `γ t`, which is how `cont_mdiff` is defined.

## Tags

integral curve, vector field
-/

localized "notation (name := ext_chart_at) `𝓔(` I `, ` x `)` :=
  ext_chart_at I x" in manifold

open_locale manifold

section

variables
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

/-- Express cont_mdiff_at in a fixed chosen local chart.

TODO: cont_mdiff_within_at, cont_mdiff_on versions -/
lemma cont_mdiff_at_indep_ext_chart
  {n : ℕ∞} {f : M → M'} (x₀ : M) {x : M}
  (hx : x ∈ 𝓔(I, x₀).source) (hfx : f x ∈ 𝓔(I', f x₀).source) :
  cont_mdiff_at I I' n f x ↔ continuous_at f x ∧
    cont_diff_within_at 𝕜 n (written_in_ext_chart_at I I' x₀ f) (set.range I) (𝓔(I, x₀) x) :=
begin
  rw [cont_mdiff_at, cont_mdiff_within_at],
  rw ext_chart_at_source at hx hfx,
  rw (cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_indep_chart
    (smooth_manifold_with_corners.chart_mem_maximal_atlas I x₀) hx
    (smooth_manifold_with_corners.chart_mem_maximal_atlas I' (f x₀)) hfx,
  apply and_congr (continuous_within_at_iff_continuous_at
    (is_open.mem_nhds is_open_univ (set.mem_univ x))),
  rw [cont_diff_within_at_prop, written_in_ext_chart_at, ext_chart_at_coe, ext_chart_at_coe,
    ext_chart_at_coe_symm, set.inter_comm _ (set.range I)],
  refine cont_diff_within_at_inter ((I.continuous_at_symm).preimage_mem_nhds _),
  rw I.left_inv,
  apply (local_homeomorph.continuous_at_symm _
    (local_homeomorph.map_source _ hx)).preimage_mem_nhds,
  exact is_open.mem_nhds is_open_univ (set.mem_univ _)
end

lemma vector_field_cont_mdiff_at_indep_ext_chart
  {n : ℕ∞} {v : M → tangent_bundle I M} (hv : ∀ x, (v x).1 = x) (x₀ : M) {x : M}
  (hx : x ∈ 𝓔(I, x₀).source) :
  cont_mdiff_at I I.tangent n v x ↔ continuous_at v x ∧
    cont_diff_within_at 𝕜 n (written_in_ext_chart_at I I.tangent x₀ v) (set.range I) (𝓔(I, x₀) x) :=
begin
  refine cont_mdiff_at_indep_ext_chart x₀ hx _,
  rw [ext_chart_at_source, basic_smooth_vector_bundle_core.mem_chart_source_iff, hv, hv,
    ←ext_chart_at_source I],
  exact hx
end

/-- If `v` is a smooth vector field, then the partial function `E → E` defined by its trivialisation
on a chosen local chart is smooth. -/
lemma vector_field_cont_diff_on_snd_of_cont_mdiff
  {n : ℕ∞} {v : M → tangent_bundle I M} (h₁ : ∀ x, (v x).1 = x)
  (h₂ : cont_mdiff I I.tangent n v) (x₀ : M) :
  cont_diff_on 𝕜 n (λ (y : E), (written_in_ext_chart_at I I.tangent x₀ v y).2) 𝓔(I, x₀).target :=
begin
  intros y hy,
  apply cont_diff_within_at.mono _ (ext_chart_at_target_subset_range _ _),
  rw ←local_equiv.right_inv _ hy,
  refine cont_diff_at.comp_cont_diff_within_at _ cont_diff_at_snd _,
  apply ((vector_field_cont_mdiff_at_indep_ext_chart h₁ _ _).mp h₂.cont_mdiff_at).2,
  exact local_equiv.map_target _ hy
end

/-- Express the change of coordinates in the tangent bundle in terms of the change of
  coordinates in the base space. -/
lemma tangent_bundle_core_coord_change_triv
  (v v' : tangent_bundle I M) :
  (𝓔(I.tangent, v') v).2 =
    (fderiv_within 𝕜 (𝓔(I, v'.1) ∘ 𝓔(I, v.1).symm) (set.range I) (𝓔(I, v.1) v.1)) v.2 := rfl

lemma tangent_bundle_core_coord_change_triv'
  (v v' : tangent_bundle I M) (hv : v.1 ∈ 𝓔(I, v'.1).source) :
  (𝓔(I.tangent, v) v).2 =
    (fderiv_within 𝕜 (𝓔(I, v.1) ∘ 𝓔(I, v'.1).symm) (set.range I) (𝓔(I, v'.1) v.1))
      (𝓔(I.tangent, v') v).2 :=
begin
  rw [ext_chart_at_coe, function.comp_apply, model_with_corners.prod_apply,
    basic_smooth_vector_bundle_core.to_charted_space_chart_at,
    basic_smooth_vector_bundle_core.chart_apply],
  have hi := mem_achart_source H v.1,
  have hj : v.1 ∈ (achart H v'.1).val.to_local_equiv.source,
  { rw ext_chart_at_source at hv,
    exact hv },
  rw ←basic_smooth_vector_bundle_core.coord_change_comp' _ hi hj hi,
  refl
end

end

variables
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {H : Type*} [topological_space H] (I : model_with_corners ℝ E H)
  (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  (v : M → tangent_bundle I M)

/-- We apply the ODE existence theorem to a continuously differentiable vector field written in the
  preferred chart around the base point. We require that the base point not be on the boundary.
  Several useful properties of the solution are proven here, to be used in
  `exists_integral_curve_of_cont_mdiff_tangent_vector_field`. -/
lemma exists_integral_curve_of_cont_mdiff_tangent_vector_field_aux [proper_space E]
  (hv : ∀ x, (v x).1 = x) (hcd : cont_mdiff I I.tangent 1 v) (t₀ : ℝ) (x₀ : M)
  (hx : I.is_interior_point x₀) :
  ∃ (ε > (0 : ℝ)) (γ : ℝ → M), γ t₀ = x₀ ∧ ∀ (t : ℝ), t ∈ set.Ioo (t₀ - ε) (t₀ + ε) →
    (γ t) ∈ 𝓔(I, x₀).source ∧
    𝓔(I, x₀) (γ t) ∈ interior 𝓔(I, x₀).target ∧
    continuous_at γ t ∧
    has_deriv_at (𝓔(I, x₀) ∘ γ) (𝓔(I.tangent, v x₀) (v (γ t))).2 t :=
begin
  have hx1 := (vector_field_cont_diff_on_snd_of_cont_mdiff hv hcd x₀).mono interior_subset,
  have hx2 := is_open.mem_nhds (is_open_interior) hx,
  obtain ⟨ε, hε, f, hf1, hf2⟩ :=
    exists_forall_deriv_at_Ioo_eq_of_cont_diff_on_nhds t₀ (𝓔(I, x₀) x₀) hx1 hx2,
  have hf1' : (𝓔(I, x₀).symm ∘ f) t₀ = x₀,
  { rw function.comp_apply,
    rw hf1,
    exact ext_chart_at_to_inv I x₀ },
  refine ⟨ε, hε, 𝓔(I, x₀).symm ∘ f, hf1', _⟩,
  intros t ht,
  obtain ⟨hf3, hf4⟩ := hf2 t ht,
  refine ⟨_, _, _, _⟩,
  { rw [function.comp_apply, ←set.mem_preimage],
    apply set.mem_of_mem_of_subset _ (local_equiv.target_subset_preimage_source _),
    apply set.mem_of_mem_of_subset _
      (interior_subset : interior 𝓔(I, x₀).target ⊆ 𝓔(I, x₀).target),
    rw ←set.mem_preimage,
    exact hf3 },
  { rw [function.comp_apply, ←set.mem_preimage, ←set.mem_preimage],
    apply set.mem_of_mem_of_subset _ (set.inter_subset_right 𝓔(I, x₀).target _),
    rw [local_equiv.target_inter_inv_preimage_preimage,
      set.inter_eq_self_of_subset_right interior_subset],
    exact hf3 },
  { refine continuous_at.comp _ hf4.continuous_at,
    apply ext_chart_continuous_at_symm'',
    exact set.mem_of_mem_of_subset hf3 interior_subset },
  { rw [function.comp_apply, ←function.comp_apply v,
    ←function.comp_apply 𝓔(I.tangent, v x₀), ←written_in_ext_chart_at],
    apply has_deriv_at.congr_of_eventually_eq hf4,
    rw filter.eventually_eq_iff_exists_mem,
    refine ⟨set.Ioo (t₀ - ε) (t₀ + ε), is_open.mem_nhds is_open_Ioo ht, _⟩,
    intros t' ht',
    rw [function.comp_apply, function.comp_apply],
    apply local_equiv.right_inv,
    exact set.mem_of_mem_of_subset (hf2 t' ht').1 interior_subset }
end

-- how to generalise / simplify?
/-- The derivative of a curve on a manifold is independent of the chosen extended chart.

Note: The hypothesis `hγ₂` is equivalent to `I.is_boundary_point (γ t)`, but the equivalence has
not been implemented in mathlib yet. -/
lemma curve_has_deriv_at_coord_change
  (hv : ∀ x, (v x).1 = x) (x₀ : M) (γ : ℝ → M) (t : ℝ)
  (hγ₁ : (γ t) ∈ 𝓔(I, x₀).source) (hγ₂ : 𝓔(I, x₀) (γ t) ∈ interior 𝓔(I, x₀).target)
  (hd : has_deriv_at (𝓔(I, x₀) ∘ γ) (𝓔(I.tangent, v x₀) (v (γ t))).2 t) :
  has_deriv_at ((𝓔(I, γ t) ∘ 𝓔(I, x₀).symm) ∘ (𝓔(I, x₀) ∘ γ))
    (𝓔(I.tangent, v (γ t)) (v (γ t))).2 t :=
begin
  have : (v (γ t)).fst ∈ 𝓔(I, (v x₀).1).source,
  { rw [hv, hv],
    exact hγ₁ },
  rw tangent_bundle_core_coord_change_triv' (v (γ t)) (v x₀) this,
  apply has_fderiv_at.comp_has_deriv_at _ _ hd,
  rw [hv, hv, function.comp_apply],
  have : set.range I ∈ nhds (𝓔(I, x₀) (γ t)),
  { rw mem_nhds_iff,
    refine ⟨interior 𝓔(I, x₀).target, _, is_open_interior, hγ₂⟩,
    refine set.subset.trans interior_subset _,
    rw ext_chart_at_target,
    exact set.inter_subset_right _ _ },
  apply has_fderiv_within_at.has_fderiv_at _ this,
  apply differentiable_within_at.has_fderiv_within_at,
  apply cont_diff_within_at.differentiable_within_at _ le_top,
  apply cont_diff_within_at_ext_coord_change,
  apply local_equiv.mem_symm_trans_source _ hγ₁,
  exact mem_ext_chart_source _ _
end

/-- For any continuously differentiable vector field and any chosen non-boundary point `x₀` on the
  manifold, an integral curve `γ : ℝ → M` exists such that `γ t₀ = x₀` and the tangent vector of `γ`
  at `t` coincides with the vector field at `γ t` for all `t` within an open interval around `t₀`.-/
theorem exists_integral_curve_of_cont_mdiff_tangent_vector_field [proper_space E]
  (hv : ∀ x, (v x).1 = x) (hcd : cont_mdiff I I.tangent 1 v)
  (t₀ : ℝ) (x₀ : M) (hx : I.is_interior_point x₀) :
  ∃ (ε > (0 : ℝ)) (γ : ℝ → M), γ t₀ = x₀ ∧ ∀ (t : ℝ), t ∈ set.Ioo (t₀ - ε) (t₀ + ε) →
    has_mfderiv_at 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smul_right (𝓔(I.tangent, v(γ t)) (v (γ t))).2) :=
begin
  obtain ⟨ε, hε, γ, hf1, hf2⟩ :=
    exists_integral_curve_of_cont_mdiff_tangent_vector_field_aux I M v hv hcd t₀ x₀ hx,
  refine ⟨ε, hε, γ, hf1, _⟩,
  intros t ht,
  rw has_mfderiv_at,
  obtain ⟨hf3, hf4, hf5, hf6⟩ := hf2 t ht,
  use hf5,
  rw [ext_chart_model_space_apply, written_in_ext_chart_at, ext_chart_model_space_eq_id,
    local_equiv.refl_symm, local_equiv.refl_coe, function.comp.right_id],
  apply has_deriv_within_at.has_fderiv_within_at,
  apply has_deriv_at.has_deriv_within_at,
  have hd := curve_has_deriv_at_coord_change I M v hv x₀ γ t hf3 hf4 hf6,
  apply has_deriv_at.congr_of_eventually_eq hd,
  rw filter.eventually_eq_iff_exists_mem,
  refine ⟨set.Ioo (t₀ - ε) (t₀ + ε), is_open.mem_nhds is_open_Ioo ht, _⟩,
  intros t' ht',
  rw [function.comp_apply, function.comp_apply, function.comp_apply, local_equiv.left_inv],
  exact (hf2 t' ht').1
end

/-- For any continuously differentiable vector field defined on a manifold without boundary and any
  chosen starting point `x₀ : M`, an integral curve `γ : ℝ → M` exists such that `γ t₀ = x₀` and the
  tangent vector of `γ` at `t` coincides with the vector field at `γ t` for all `t` within an open
  interval around `t₀`. -/
lemma exists_integral_curve_of_cont_mdiff_tangent_vector_field_of_boundaryless
  [proper_space E] [I.boundaryless]
  (h₁ : ∀ x, (v x).1 = x) (h₂ : cont_mdiff I I.tangent 1 v) (t₀ : ℝ) (x₀ : M) :
  ∃ (ε > (0 : ℝ)) (γ : ℝ → M), γ t₀ = x₀ ∧ ∀ (t : ℝ), t ∈ set.Ioo (t₀ - ε) (t₀ + ε) →
    has_mfderiv_at 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smul_right (𝓔(I.tangent, v(γ t)) (v (γ t))).2) :=
exists_integral_curve_of_cont_mdiff_tangent_vector_field I M v h₁ h₂ t₀ x₀
    (model_with_corners.boundaryless.is_interior_point I)
