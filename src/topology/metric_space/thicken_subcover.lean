/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.metric_space.hausdorff_distance
import topology.metric_space.emetric_paracompact
import analysis.convex.partition_of_unity

/-!
-/

open_locale topological_space ennreal big_operators nnreal
open set function filter topological_space emetric

variables {ι X : Type*}

/-- An auxiliary lemma for `emetric.exists_continuous_forall_closed_ball_subset`. -/
lemma emetric.exists_nhds_nnreal_pos_forall_closed_ball_subset [emetric_space X] {K : ι → set X}
  {U : ι → set X} (hK : ∀ i, is_closed (K i)) (hU : ∀ i, is_open (U i)) (hKU : ∀ i, K i ⊆ U i)
  (hfin : locally_finite K) (x : X) :
  ∃ (V ∈ 𝓝 x) (r : ℝ≥0), ∀ y ∈ V,
    (r : ℝ) ∈ Ioi 0 ∩ ennreal.of_real ⁻¹' ⋂ i (hi : y ∈ K i), Iio (inf_edist y (U i)ᶜ) :=
begin
  suffices : ∃ r : ℝ≥0, 0 < r ∧ ∀ i (y ∈ closed_ball x r ∩ K i),
    x ∈ K i ∧ (r + r : ℝ≥0∞) < inf_edist x (U i)ᶜ,
  { rcases this with ⟨r, hr0, hr⟩,
    have hr0' : (0 : ℝ≥0∞) < r, from ennreal.coe_pos.2 hr0,
    refine ⟨closed_ball x r, closed_ball_mem_nhds _ hr0', r, λ y hy, ⟨nnreal.coe_pos.2 hr0, _⟩⟩,
    simp only [mem_preimage, ennreal.of_real_coe_nnreal, mem_Inter₂, mem_Iio],
    intros i hi,
    refine lt_of_add_lt_add_left _, exact r,
    calc (r + r : ℝ≥0∞) < inf_edist x (U i)ᶜ : (hr i y ⟨hy, hi⟩).2
    ... ≤ edist x y + inf_edist y (U i)ᶜ : inf_edist_le_edist_add_inf_edist
    ... ≤ r + inf_edist y (U i)ᶜ : add_le_add_right _ _,
    rwa edist_comm },
  have H₁ : (𝓝 x).has_basis (λ r : ℝ≥0, 0 < r) (λ r, closed_ball x r),
    from nhds_basis_uniformity uniformity_basis_edist_nnreal_le,
  rcases H₁.mem_iff.1 (hfin.Inter_compl_mem_nhds hK x) with ⟨r, hr₀, hr⟩,
  simp only [subset_Inter_iff] at hr,
  have H₂ : (⋂ i (hi : x ∈ K i), U i) ∈ 𝓝 x,
    from (bInter_mem (hfin.point_finite x)).2 (λ i hi, (hU i).mem_nhds (hKU i hi)),
  have H₃ : 0 < inf_edist x (⋂ i (hi : x ∈ K i), U i)ᶜ,
    by rwa [pos_iff_ne_zero, ne.def, ← mem_closure_iff_inf_edist_zero, ← mem_compl_iff,
      ← interior_compl, compl_compl, mem_interior_iff_mem_nhds],
  rcases ennreal.lt_iff_exists_nnreal_btwn.mp H₃ with ⟨r', hr₀', hr'⟩,
  rw ennreal.coe_pos at hr₀',
  refine ⟨min r (r' / 2), lt_min hr₀ (nnreal.half_pos hr₀'), _⟩,
  rintro i y ⟨hyx, hyK⟩,
  have hxK : x ∈ K i,
  { contrapose hyK with hxK,
    exact hr i hxK (closed_ball_subset_closed_ball (ennreal.coe_le_coe.2 (min_le_left _ _)) hyx) },
  refine ⟨hxK, _⟩,
  have : (↑(min r (r' / 2)) : ℝ≥0∞) ≤ ↑(r' / 2), from ennreal.coe_le_coe.2 (min_le_right _ _),
  calc (↑(min r (r' / 2)) + ↑(min r (r' / 2)) : ℝ≥0∞) ≤ ↑(r' / 2) + ↑(r' / 2) :
    add_le_add this this
  ... = r' : by rw [← ennreal.coe_add, nnreal.add_halves]
  ... < inf_edist x (⋂ i (hi : x ∈ K i), U i)ᶜ : hr'
  ... ≤ inf_edist x (U i)ᶜ : inf_edist_anti (compl_subset_compl.2 $ Inter₂_subset _ hxK)
end

/-- Let `X` be an extended metric space. Let `K : ι → set X` be a locally finite family of closed
sets, let `U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there
exists a positive continuous function `δ : X → ℝ≥0` such that for any `i` and `x ∈ K i`,
we have `emetric.closed_ball x (δ x) ⊆ U i`. -/
lemma emetric.exists_continuous_forall_closed_ball_subset [emetric_space X] {K : ι → set X}
  {U : ι → set X} (hK : ∀ i, is_closed (K i)) (hU : ∀ i, is_open (U i)) (hKU : ∀ i, K i ⊆ U i)
  (hfin : locally_finite K) :
  ∃ δ : C(X, ℝ≥0), (∀ x, 0 < δ x) ∧ ∀ i (x ∈ K i), closed_ball x (δ x) ⊆ U i :=
begin
  suffices : ∃ δ : C(X, ℝ), ∀ x,
    δ x ∈ Ioi 0 ∩ ennreal.of_real ⁻¹' (⋂ i (hi : x ∈ K i), Iio (inf_edist x (U i)ᶜ)),
  { choose δ hδ0 hδ_lt,
    lift δ to C(X, ℝ≥0) using λ x, le_of_lt (hδ0 x),
    replace hδ_lt : ∀ x i, x ∈ K i → ↑(δ x) < inf_edist x (U i)ᶜ, by simpa using hδ_lt,
    exact ⟨δ, hδ0, λ i x hx, disjoint_compl_right_iff_subset.mp
      (disjoint_closed_ball_of_lt_inf_edist $ hδ_lt _ _ hx)⟩ },
  refine exists_continuous_forall_mem_convex_of_local (λ x, _) (λ x, _),
  { refine (convex_Ioi _).inter (ord_connected.preimage_ennreal_of_real _).convex,
    exact ord_connected_Inter (λ i, ord_connected_Inter $ λ _, ord_connected_Iio) },
  { rcases emetric.exists_nhds_nnreal_pos_forall_closed_ball_subset hK hU hKU hfin x
      with ⟨V, hV, r, hr⟩,
    exact ⟨V, hV, λ _, r, continuous_on_const, hr⟩ }
end

/-- Let `X` be a metric space. Let `K : ι → set X` be a locally finite family of closed sets, let
`U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there exists a
positive continuous function `δ : X → ℝ≥0` such that for any `i` and `x ∈ K i`, we have
`metric.closed_ball x (δ x) ⊆ U i`. -/
lemma metric.exists_continuous_forall_closed_ball_subset [metric_space X] {K : ι → set X}
  {U : ι → set X} (hK : ∀ i, is_closed (K i)) (hU : ∀ i, is_open (U i)) (hKU : ∀ i, K i ⊆ U i)
  (hfin : locally_finite K) :
  ∃ δ : C(X, ℝ≥0), (∀ x, 0 < δ x) ∧ ∀ i (x ∈ K i), metric.closed_ball x (δ x) ⊆ U i :=
begin
  rcases emetric.exists_continuous_forall_closed_ball_subset hK hU hKU hfin with ⟨δ, hδ0, hδ⟩,
  refine ⟨δ, hδ0, λ i x hx, _⟩,
  rw [← metric.emetric_closed_ball_nnreal],
  exact hδ i x hx
end
