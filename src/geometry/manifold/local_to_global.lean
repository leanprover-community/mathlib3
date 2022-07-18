import geometry.manifold.partition_of_unity
import analysis.convex.partition_of_unity
import topology.metric_space.thicken_subcover

/-!
-/

open_locale topological_space ennreal manifold big_operators nnreal
open set

variables
  {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {H : Type*} [topological_space H] (I : model_with_corners ℝ E H)
  {F : Type*} [normed_group F] [normed_space ℝ F]
  {ι M : Type*}

lemma exists_smooth_forall_mem_convex_of_local [topological_space M] [charted_space H M]
  [smooth_manifold_with_corners I M] [sigma_compact_space M] [t2_space M] {t : M → set F}
  (ht : ∀ x, convex ℝ (t x))
  (Hloc : ∀ x : M, ∃ (U ∈ 𝓝 x) (g : M → F), smooth_on I 𝓘(ℝ, F) g U ∧ ∀ y ∈ U, g y ∈ t y) :
  ∃ g : C^∞⟮I, M; 𝓘(ℝ, F), F⟯, ∀ x, g x ∈ t x :=
begin
  choose U hU g hgs hgt using Hloc,
  obtain ⟨f, hf⟩ := smooth_partition_of_unity.exists_is_subordinate I is_closed_univ
    (λ x, interior (U x)) (λ x, is_open_interior)
    (λ x hx, mem_Union.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩),
  refine ⟨⟨λ x, ∑ᶠ i, f i x • g i x, f.smooth_finsum_smul $ λ i x hx, _⟩, λ x, _⟩,
  { exact (hgs _).smooth_at (mem_interior_iff_mem_nhds.1 $ hf _ hx) },
  { refine f.to_partition_of_unity.finsum_smul_mem_convex (mem_univ x) (λ i hi, hgt _ _ _) (ht _),
    exact interior_subset (hf _ $ subset_closure hi) }
end

/-- Let `X` be an extended metric space. Let `K : ι → set X` be a locally finite family of closed
sets, let `U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there
exists a positive continuous function `δ : X → ℝ≥0` such that for any `i` and `x ∈ K i`,
we have `emetric.closed_ball x (δ x) ⊆ U i`. -/
lemma emetric.exists_smooth_forall_closed_ball_subset [emetric_space M] [charted_space H M]
  [smooth_manifold_with_corners I M] [sigma_compact_space M] [t2_space M] {K : ι → set M}
  {U : ι → set M} (hK : ∀ i, is_closed (K i)) (hU : ∀ i, is_open (U i)) (hKU : ∀ i, K i ⊆ U i)
  (hfin : locally_finite K) :
  ∃ δ : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯, (∀ x, 0 < δ x) ∧
    ∀ i (x ∈ K i), emetric.closed_ball x (ennreal.of_real (δ x)) ⊆ U i :=
begin
  suffices : ∃ δ : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯, ∀ x,
    δ x ∈ Ioi 0 ∩ ennreal.of_real ⁻¹' (⋂ i (hi : x ∈ K i), Iio (emetric.inf_edist x (U i)ᶜ)),
  { choose δ hδ0 hδ_lt,
    replace hδ_lt : ∀ x i, x ∈ K i → ennreal.of_real (δ x) < emetric.inf_edist x (U i)ᶜ,
      by simpa using hδ_lt,
    exact ⟨δ, hδ0, λ i x hx, disjoint_compl_right_iff_subset.mp
      (emetric.disjoint_closed_ball_of_lt_inf_edist $ hδ_lt _ _ hx)⟩ },
  refine exists_smooth_forall_mem_convex_of_local I (λ x, _) (λ x, _),
  { refine (convex_Ioi _).inter (ord_connected.preimage_ennreal_of_real _).convex,
    exact ord_connected_Inter (λ i, ord_connected_Inter $ λ _, ord_connected_Iio) },
  { rcases emetric.exists_nhds_nnreal_pos_forall_closed_ball_subset hK hU hKU hfin x
      with ⟨V, hV, r, hr⟩,
    exact ⟨V, hV, λ _, r, smooth_on_const, hr⟩ }
end

/-- Let `X` be a metric space. Let `K : ι → set X` be a locally finite family of closed sets, let
`U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there exists a
positive continuous function `δ : X → ℝ≥0` such that for any `i` and `x ∈ K i`, we have
`metric.closed_ball x (δ x) ⊆ U i`. -/
lemma metric.exists_smooth_forall_closed_ball_subset [metric_space M] [charted_space H M]
  [smooth_manifold_with_corners I M] [sigma_compact_space M] [t2_space M] {K : ι → set M}
  {U : ι → set M} (hK : ∀ i, is_closed (K i)) (hU : ∀ i, is_open (U i)) (hKU : ∀ i, K i ⊆ U i)
  (hfin : locally_finite K) :
  ∃ δ : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯, (∀ x, 0 < δ x) ∧ ∀ i (x ∈ K i), metric.closed_ball x (δ x) ⊆ U i :=
begin
  rcases emetric.exists_smooth_forall_closed_ball_subset I hK hU hKU hfin with ⟨δ, hδ0, hδ⟩,
  refine ⟨δ, hδ0, λ i x hx, _⟩,
  rw [← metric.emetric_closed_ball (hδ0 _).le],
  exact hδ i x hx
end
