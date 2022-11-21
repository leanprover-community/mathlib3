/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/

import geometry.manifold.vector_bundle.basic

open bundle set smooth_manifold_with_corners
open_locale manifold topological_space

noncomputable theory

section -- todo: move

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]

lemma fderiv_within_fderiv_within {g : F → G} {f : E → F} {x : E} {y : F} {s : set E} {t : set F}
  (hg : differentiable_within_at 𝕜 g t y) (hf : differentiable_within_at 𝕜 f s x)
  (h : maps_to f s t) (hxs : unique_diff_within_at 𝕜 s x) (hy : f x = y) (v : E) :
  fderiv_within 𝕜 g t y (fderiv_within 𝕜 f s x v) = fderiv_within 𝕜 (g ∘ f) s x v :=
by { subst y, rw [fderiv_within.comp x hg hf h hxs], refl }

end


section -- todo: move

variables {𝕜 E M H E' M' H' H'' : Type*} [nontrivially_normed_field 𝕜]
  [normed_add_comm_group E] [normed_space 𝕜 E] [topological_space H] [topological_space M]
  (f f' : local_homeomorph M H) (I : model_with_corners 𝕜 E H)
  [normed_add_comm_group E'] [normed_space 𝕜 E'] [topological_space H'] [topological_space M']
  (I' : model_with_corners 𝕜 E' H')
  {x : M} {s t : set M}
  [topological_space H'']

namespace local_homeomorph

lemma extend_left_inv {x : M} (hxf : x ∈ f.source) : (f.extend I).symm (f.extend I x) = x :=
(f.extend I).left_inv $ by rwa f.extend_source

lemma extend_coord_change_source_mem_nhds_within {x : E}
  (hx : x ∈ ((f.extend I).symm ≫ f'.extend I).source) :
  ((f.extend I).symm ≫ f'.extend I).source ∈ 𝓝[range I] x :=
begin
  rw [f.extend_coord_change_source] at hx ⊢,
  obtain ⟨x, hx, rfl⟩ := hx,
  refine I.image_mem_nhds_within _,
  refine (local_homeomorph.open_source _).mem_nhds hx
end

lemma extend_coord_change_source_mem_nhds_within' {x : M}
  (hxf : x ∈ f.source) (hxf' : x ∈ f'.source) :
  ((f.extend I).symm ≫ f'.extend I).source ∈ 𝓝[range I] f.extend I x :=
begin
  apply extend_coord_change_source_mem_nhds_within,
  rw [← extend_image_source_inter],
  exact mem_image_of_mem _ ⟨hxf, hxf'⟩,
end

lemma cont_diff_within_at_extend_coord_change'
  [charted_space H M] [smooth_manifold_with_corners I M]
  (hf : f ∈ maximal_atlas I M) (hf' : f' ∈ maximal_atlas I M) {x : M}
  (hxf : x ∈ f.source) (hxf' : x ∈ f'.source) :
  cont_diff_within_at 𝕜 ⊤ (f.extend I ∘ (f'.extend I).symm) (range I) (f'.extend I x) :=
begin
  refine (local_homeomorph.cont_diff_on_extend_coord_change I hf hf' _ _).mono_of_mem _,
  { rw [← f'.extend_image_source_inter], exact mem_image_of_mem _ ⟨hxf', hxf⟩ },
  exact f'.extend_coord_change_source_mem_nhds_within' f I hxf' hxf
end

lemma symm_trans_source' (e : local_homeomorph H' H) (e' : local_homeomorph H' H'') :
  (e.symm ≫ₕ e').source = e.target ∩ e.symm ⁻¹' (e.source ∩ e'.source) :=
trans_source' _ _

end local_homeomorph
end
open local_homeomorph

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
variables (I)

lemma cont_diff_on_fderiv_coord_change (i j : atlas H M) :
  cont_diff_on 𝕜 ∞ (fderiv_within 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I))
    ((i.1.extend I).symm ≫ j.1.extend I).source :=
begin
  have h : ((i.1.extend I).symm ≫ j.1.extend I).source ⊆ range I,
  { rw [i.1.extend_coord_change_source], apply image_subset_range },
  intros x hx,
  refine (cont_diff_within_at.fderiv_within_right _ I.unique_diff le_top $ h hx).mono h,
  refine (local_homeomorph.cont_diff_on_extend_coord_change I (subset_maximal_atlas I j.2)
    (subset_maximal_atlas I i.2) x hx).mono_of_mem _,
  exact i.1.extend_coord_change_source_mem_nhds_within j.1 I hx
end

variables (M)
open smooth_manifold_with_corners
@[simps] def tangent_bundle_core : vector_bundle_core 𝕜 M E (atlas H M) :=
{ base_set := λ i, i.1.source,
  is_open_base_set := λ i, i.1.open_source,
  index_at := achart H,
  mem_base_set_at := mem_chart_source H,
  coord_change := λ i j x, fderiv_within 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I)
    (i.1.extend I x),
  coord_change_self := λ i x hx v, begin
    rw [filter.eventually_eq.fderiv_within_eq, fderiv_within_id', continuous_linear_map.id_apply],
    { exact I.unique_diff_at_image },
    { exact I.unique_diff_at_image },
    { filter_upwards [i.1.extend_target_mem_nhds_within I hx] with y hy,
      exact (i.1.extend I).right_inv hy },
    { simp_rw [function.comp_apply, i.1.extend_left_inv I hx] }
  end,
  continuous_on_coord_change := λ i j, begin
      refine (cont_diff_on_fderiv_coord_change I i j).continuous_on.comp
        ((i.1.extend_continuous_on I).mono _) _,
      { rw [i.1.extend_source], exact inter_subset_left _ _ },
      simp_rw [← i.1.extend_image_source_inter, maps_to_image]
    end,
  coord_change_comp := begin
    rintro i j k x ⟨⟨hxi, hxj⟩, hxk⟩ v,
    rw [fderiv_within_fderiv_within, filter.eventually_eq.fderiv_within_eq],
    { exact I.unique_diff_at_image },
    { have := i.1.extend_preimage_mem_nhds I hxi (j.1.extend_source_mem_nhds I hxj),
      filter_upwards [nhds_within_le_nhds this] with y hy,
      simp_rw [function.comp_apply, (j.1.extend I).left_inv hy] },
    { simp_rw [function.comp_apply, i.1.extend_left_inv I hxi, j.1.extend_left_inv I hxj] },
    { exact (k.1.cont_diff_within_at_extend_coord_change' j.1 I (subset_maximal_atlas I k.2)
        (subset_maximal_atlas I j.2) hxk hxj).differentiable_within_at le_top },
    { exact (j.1.cont_diff_within_at_extend_coord_change' i.1 I (subset_maximal_atlas I j.2)
        (subset_maximal_atlas I i.2) hxj hxi).differentiable_within_at le_top },
    { intros x hx, exact mem_range_self _ },
    { exact I.unique_diff_at_image },
    { rw [function.comp_apply, i.1.extend_left_inv I hxi] }
  end }

variables {M}
include I

/-- The tangent space at a point of the manifold `M`. It is just `E`. We could use instead
`(tangent_bundle_core I M).to_topological_vector_bundle_core.fiber x`, but we use `E` to help the
kernel.
-/
@[nolint unused_arguments]
def tangent_space (x : M) : Type* := E

omit I
variable (M)

/-- The tangent bundle to a smooth manifold, as a Sigma type. Defined in terms of
`bundle.total_space` to be able to put a suitable topology on it. -/
@[nolint has_nonempty_instance, reducible] -- is empty if the base manifold is empty
def tangent_bundle := bundle.total_space (tangent_space I : M → Type*)

local notation `TM` := tangent_bundle I M

/-- The projection from the tangent bundle of a smooth manifold to the manifold. As the tangent
bundle is represented internally as a sigma type, the notation `p.1` also works for the projection
of the point `p`. -/
def tangent_bundle.proj : TM → M :=
λ p, p.1

variable {M}

@[simp, mfld_simps] lemma tangent_bundle.proj_apply (x : M) (v : tangent_space I x) :
  tangent_bundle.proj I M ⟨x, v⟩ = x :=
rfl

section tangent_bundle_instances

/- In general, the definition of tangent_bundle and tangent_space are not reducible, so that type
class inference does not pick wrong instances. In this section, we record the right instances for
them, noting in particular that the tangent bundle is a smooth manifold. -/

section
local attribute [reducible] tangent_space

variables {M} (x : M)

instance : topological_space (tangent_space I x) := by apply_instance
instance : add_comm_group (tangent_space I x) := by apply_instance
instance : topological_add_group (tangent_space I x) := by apply_instance
instance : module 𝕜 (tangent_space I x) := by apply_instance
instance : inhabited (tangent_space I x) := ⟨0⟩

end

variable (M)

instance : topological_space TM :=
(tangent_bundle_core I M).to_fiber_bundle_core.to_topological_space

instance : fiber_bundle E (tangent_space I : M → Type*) :=
(tangent_bundle_core I M).to_fiber_bundle_core.fiber_bundle

instance : vector_bundle 𝕜 E (tangent_space I : M → Type*) :=
(tangent_bundle_core I M).vector_bundle

lemma tangent_space_chart_at (p : tangent_bundle I M) :
  chart_at (model_prod H E) p =
    ((tangent_bundle_core I M).to_fiber_bundle_core.local_triv (achart H p.1))
      .to_local_homeomorph ≫ₕ (chart_at H p.1).prod (local_homeomorph.refl E) :=
rfl

lemma tangent_space_chart_at_to_local_equiv (p : tangent_bundle I M) :
  (chart_at (model_prod H E) p).to_local_equiv =
    (tangent_bundle_core I M).to_fiber_bundle_core.local_triv_as_local_equiv (achart H p.1) ≫
    (chart_at H p.1).to_local_equiv.prod (local_equiv.refl E) :=
rfl

instance tangent_bundle_core.is_smooth : (tangent_bundle_core I M).is_smooth I :=
begin
  refine ⟨λ i j, _⟩,
  rw [smooth_on, cont_mdiff_on_iff_source_of_mem_maximal_atlas
    (subset_maximal_atlas I i.2), cont_mdiff_on_iff_cont_diff_on],
  refine ((cont_diff_on_fderiv_coord_change I i j).congr $ λ x hx, _).mono _,
  { rw [local_equiv.trans_source'] at hx,
    simp_rw [function.comp_apply, tangent_bundle_core_coord_change,
      (i.1.extend I).right_inv hx.1] },
  { exact (i.1.extend_image_source_inter j.1 I).subset },
  { apply inter_subset_left }
end

instance tangent_bundle.smooth_vector_bundle :
  smooth_vector_bundle E (tangent_space I : M → Type*) I :=
(tangent_bundle_core I M).smooth_vector_bundle _

end tangent_bundle_instances

variable (M)

/-- The tangent bundle projection on the basis is a continuous map. -/
lemma tangent_bundle_proj_continuous : continuous (tangent_bundle.proj I M) :=
continuous_proj E (tangent_space I : M → Type*)

/-- The tangent bundle projection on the basis is an open map. -/
lemma tangent_bundle_proj_open : is_open_map (tangent_bundle.proj I M) :=
is_open_map_proj E (tangent_space I : M → Type*)

/-- In the tangent bundle to the model space, the charts are just the canonical identification
between a product type and a sigma type, a.k.a. `equiv.sigma_equiv_prod`. -/
@[simp, mfld_simps] lemma tangent_bundle_model_space_chart_at (p : tangent_bundle I H) :
  (chart_at (model_prod H E) p).to_local_equiv = (equiv.sigma_equiv_prod H E).to_local_equiv :=
begin
  ext x : 1,
  { ext, { refl },
    exact (tangent_bundle_core I H).coord_change_self (achart _ x.1) x.1
      (mem_achart_source H x.1) x.2 },
  { intros x, ext, { refl }, apply heq_of_eq,
    exact (tangent_bundle_core I H).coord_change_self (achart _ x.1) x.1
      (mem_achart_source H x.1) x.2 },
  simp_rw [tangent_space_chart_at],
  simp only [-fiber_bundle_core.local_triv_as_local_equiv_source] with mfld_simps,
  simp_rw [fiber_bundle_core.local_triv_as_local_equiv,
    vector_bundle_core.to_fiber_bundle_core_base_set, tangent_bundle_core_base_set],
  simp only with mfld_simps,
end

@[simp, mfld_simps] lemma tangent_bundle_model_space_coe_chart_at (p : tangent_bundle I H) :
  ⇑(chart_at (model_prod H E) p) = equiv.sigma_equiv_prod H E :=
by { unfold_coes, simp_rw [tangent_bundle_model_space_chart_at], refl }

@[simp, mfld_simps] lemma tangent_bundle_model_space_coe_chart_at_symm (p : tangent_bundle I H) :
  ((chart_at (model_prod H E) p).symm : model_prod H E → tangent_bundle I H) =
  (equiv.sigma_equiv_prod H E).symm :=
by { unfold_coes,
  simp_rw [local_homeomorph.symm_to_local_equiv, tangent_bundle_model_space_chart_at], refl }

variable (H)
/-- The canonical identification between the tangent bundle to the model space and the product,
as a homeomorphism -/
def tangent_bundle_model_space_homeomorph : tangent_bundle I H ≃ₜ model_prod H E :=
{ continuous_to_fun :=
  begin
    let p : tangent_bundle I H := ⟨I.symm (0 : E), (0 : E)⟩,
    have : continuous (chart_at (model_prod H E) p),
    { rw continuous_iff_continuous_on_univ,
      convert local_homeomorph.continuous_on _,
      simp only [tangent_space.fiber_bundle] with mfld_simps },
    simpa only with mfld_simps using this,
  end,
  continuous_inv_fun :=
  begin
    let p : tangent_bundle I H := ⟨I.symm (0 : E), (0 : E)⟩,
    have : continuous (chart_at (model_prod H E) p).symm,
    { rw continuous_iff_continuous_on_univ,
      convert local_homeomorph.continuous_on _,
      simp only with mfld_simps },
    simpa only with mfld_simps using this,
  end,
  .. equiv.sigma_equiv_prod H E }

@[simp, mfld_simps] lemma tangent_bundle_model_space_homeomorph_coe :
  (tangent_bundle_model_space_homeomorph H I : tangent_bundle I H → model_prod H E)
  = equiv.sigma_equiv_prod H E :=
rfl

@[simp, mfld_simps] lemma tangent_bundle_model_space_homeomorph_coe_symm :
  ((tangent_bundle_model_space_homeomorph H I).symm : model_prod H E → tangent_bundle I H)
  = (equiv.sigma_equiv_prod H E).symm :=
rfl
