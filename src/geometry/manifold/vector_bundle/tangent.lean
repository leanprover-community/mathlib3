/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/

import geometry.manifold.vector_bundle.basic

/-! # Tangent bundles

This file defines the tangent bundle as a smooth vector bundle.

Let `M` be a smooth manifold with corners with model `I` on `(E, H)`. We define the tangent bundle
of `M` using the `vector_bundle_core` construction indexed by the charts of `M` with fibers `E`.
Given two charts `i, j : local_homeomorph M H`, the coordinate change between `i` and `j` at a point
`x : M` is the derivative of the composite
```
  I.symm   i.symm    j     I
E -----> H -----> M --> H --> E
```
within the set `range I ⊆ E` at `I (i x) : E`.
This defines a smooth vector bundle `tangent_bundle` with fibers `tangent_space`.

## Main definitions

* `tangent_space I M x` is the fiber of the tangent bundle at `x : M`, which is defined to be `E`.

* `tangent_bundle I M` is the total space of `tangent_space I M`, proven to be a smooth vector
  bundle.
-/

open bundle set smooth_manifold_with_corners local_homeomorph continuous_linear_map
open_locale manifold topology bundle

noncomputable theory

section general

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]

variables (I)

/-- Auxiliary lemma for tangent spaces: the derivative of a coordinate change between two charts is
  smooth on its source. -/
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

/--
Let `M` be a smooth manifold with corners with model `I` on `(E, H)`.
Then `vector_bundle_core I M` is the vector bundle core for the tangent bundle over `M`.
It is indexed by the atlas of `M`, with fiber `E` and its change of coordinates from the chart `i`
to the chart `j` at point `x : M` is the derivative of the composite
```
  I.symm   i.symm    j     I
E -----> H -----> M --> H --> E
```
within the set `range I ⊆ E` at `I (i x) : E`. -/
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
        ((i.1.continuous_on_extend I).mono _) _,
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
    { exact (cont_diff_within_at_extend_coord_change' I (subset_maximal_atlas I k.2)
        (subset_maximal_atlas I j.2) hxk hxj).differentiable_within_at le_top },
    { exact (cont_diff_within_at_extend_coord_change' I (subset_maximal_atlas I j.2)
        (subset_maximal_atlas I i.2) hxj hxi).differentiable_within_at le_top },
    { intros x hx, exact mem_range_self _ },
    { exact I.unique_diff_at_image },
    { rw [function.comp_apply, i.1.extend_left_inv I hxi] }
  end }

variables {M}

lemma tangent_bundle_core_coord_change_achart (x x' z : M) :
  (tangent_bundle_core I M).coord_change (achart H x) (achart H x') z =
  fderiv_within 𝕜 (ext_chart_at I x' ∘ (ext_chart_at I x).symm) (range I) (ext_chart_at I x z) :=
rfl

include I

/-- The tangent space at a point of the manifold `M`. It is just `E`. We could use instead
`(tangent_bundle_core I M).to_topological_vector_bundle_core.fiber x`, but we use `E` to help the
kernel.
-/
@[nolint unused_arguments, derive [topological_space, add_comm_group, topological_add_group]]
def tangent_space (x : M) : Type* := E

omit I
variable (M)

/-- The tangent bundle to a smooth manifold, as a Sigma type. Defined in terms of
`bundle.total_space` to be able to put a suitable topology on it. -/
@[nolint has_nonempty_instance, reducible] -- is empty if the base manifold is empty
def tangent_bundle := bundle.total_space (tangent_space I : M → Type*)

local notation `TM` := tangent_bundle I M


section tangent_bundle_instances

/- In general, the definition of tangent_space is not reducible, so that type class inference
does not pick wrong instances. In this section, we record the right instances for
them, noting in particular that the tangent bundle is a smooth manifold. -/

section

variables {M} (x : M)

instance : module 𝕜 (tangent_space I x) := by delta_instance tangent_space
instance : inhabited (tangent_space I x) := ⟨0⟩
instance {x : M} : has_continuous_add (tangent_space I x) := by delta_instance tangent_space

end

instance : topological_space TM :=
(tangent_bundle_core I M).to_topological_space

instance : fiber_bundle E (tangent_space I : M → Type*) :=
(tangent_bundle_core I M).fiber_bundle

instance : vector_bundle 𝕜 E (tangent_space I : M → Type*) :=
(tangent_bundle_core I M).vector_bundle

namespace tangent_bundle

protected lemma chart_at (p : TM) :
  chart_at (model_prod H E) p =
    ((tangent_bundle_core I M).to_fiber_bundle_core.local_triv (achart H p.1))
      .to_local_homeomorph ≫ₕ (chart_at H p.1).prod (local_homeomorph.refl E) :=
rfl

lemma chart_at_to_local_equiv (p : TM) :
  (chart_at (model_prod H E) p).to_local_equiv =
    (tangent_bundle_core I M).to_fiber_bundle_core.local_triv_as_local_equiv (achart H p.1) ≫
    (chart_at H p.1).to_local_equiv.prod (local_equiv.refl E) :=
rfl

lemma trivialization_at_eq_local_triv (x : M) :
  trivialization_at E (tangent_space I) x =
  (tangent_bundle_core I M).to_fiber_bundle_core.local_triv (achart H x) :=
rfl

@[simp, mfld_simps]
lemma trivialization_at_source (x : M) :
  (trivialization_at E (tangent_space I) x).source = π _ ⁻¹' (chart_at H x).source :=
rfl

@[simp, mfld_simps]
lemma trivialization_at_target (x : M) :
  (trivialization_at E (tangent_space I) x).target = (chart_at H x).source ×ˢ univ :=
rfl

@[simp, mfld_simps]
lemma trivialization_at_base_set (x : M) :
  (trivialization_at E (tangent_space I) x).base_set = (chart_at H x).source :=
rfl

lemma trivialization_at_apply (x : M) (z : TM) :
  trivialization_at E (tangent_space I) x z =
  (z.1, fderiv_within 𝕜 ((chart_at H x).extend I ∘ ((chart_at H z.1).extend I).symm) (range I)
    ((chart_at H z.1).extend I z.1) z.2) :=
rfl

@[simp, mfld_simps]
lemma trivialization_at_fst (x : M) (z : TM) :
  (trivialization_at E (tangent_space I) x z).1 = z.1 :=
rfl

@[simp, mfld_simps] lemma mem_chart_source_iff (p q : TM) :
  p ∈ (chart_at (model_prod H E) q).source ↔ p.1 ∈ (chart_at H q.1).source :=
by simp only [fiber_bundle.charted_space_chart_at] with mfld_simps

@[simp, mfld_simps] lemma mem_chart_target_iff (p : H × E) (q : TM) :
  p ∈ (chart_at (model_prod H E) q).target ↔ p.1 ∈ (chart_at H q.1).target :=
by simp only [fiber_bundle.charted_space_chart_at, and_iff_left_iff_imp] with mfld_simps
  {contextual := tt}

@[simp, mfld_simps] lemma coe_chart_at_fst (p q : TM) :
  ((chart_at (model_prod H E) q) p).1 = chart_at H q.1 p.1 := rfl

@[simp, mfld_simps] lemma coe_chart_at_symm_fst (p : H × E) (q : TM) :
  ((chart_at (model_prod H E) q).symm p).1 = ((chart_at H q.1).symm : H → M) p.1 := rfl

@[simp, mfld_simps] lemma trivialization_at_continuous_linear_map_at {b₀ b : M}
  (hb : b ∈ (trivialization_at E (tangent_space I) b₀).base_set) :
  (trivialization_at E (tangent_space I) b₀).continuous_linear_map_at 𝕜 b =
  (tangent_bundle_core I M).coord_change (achart H b) (achart H b₀) b :=
(tangent_bundle_core I M).local_triv_continuous_linear_map_at hb

@[simp, mfld_simps] lemma trivialization_at_symmL {b₀ b : M}
  (hb : b ∈ (trivialization_at E (tangent_space I) b₀).base_set) :
  (trivialization_at E (tangent_space I) b₀).symmL 𝕜 b =
    (tangent_bundle_core I M).coord_change (achart H b₀) (achart H b) b :=
(tangent_bundle_core I M).local_triv_symmL hb

@[simp, mfld_simps]
lemma coord_change_model_space (b b' x : F) :
  (tangent_bundle_core 𝓘(𝕜, F) F).coord_change (achart F b) (achart F b') x = 1 :=
by simpa only [tangent_bundle_core_coord_change] with mfld_simps using
    fderiv_within_id unique_diff_within_at_univ

@[simp, mfld_simps]
lemma symmL_model_space (b b' : F) :
  (trivialization_at F (tangent_space 𝓘(𝕜, F)) b).symmL 𝕜 b' = (1 : F →L[𝕜] F) :=
begin
  rw [tangent_bundle.trivialization_at_symmL, coord_change_model_space],
  apply mem_univ
end

@[simp, mfld_simps]
lemma continuous_linear_map_at_model_space (b b' : F) :
  (trivialization_at F (tangent_space 𝓘(𝕜, F)) b).continuous_linear_map_at 𝕜 b' =
  (1 : F →L[𝕜] F) :=
begin
  rw [tangent_bundle.trivialization_at_continuous_linear_map_at, coord_change_model_space],
  apply mem_univ
end

end tangent_bundle

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

/-! ## The tangent bundle to the model space -/

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
  simp_rw [tangent_bundle.chart_at, fiber_bundle_core.local_triv,
    fiber_bundle_core.local_triv_as_local_equiv, vector_bundle_core.to_fiber_bundle_core_base_set,
    tangent_bundle_core_base_set],
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

lemma tangent_bundle_core_coord_change_model_space (x x' z : H) :
  (tangent_bundle_core I H).coord_change (achart H x) (achart H x') z =
  continuous_linear_map.id 𝕜 E :=
by { ext v, exact (tangent_bundle_core I H).coord_change_self (achart _ z) z (mem_univ _) v }

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

section in_tangent_coordinates

variables (I I') {M M' H H'} {N : Type*}

/-- The map `in_coordinates` for the tangent bundle is trivial on the model spaces -/
lemma in_coordinates_tangent_bundle_core_model_space
  (x₀ x : H) (y₀ y : H') (ϕ : E →L[𝕜] E') :
    in_coordinates E (tangent_space I) E' (tangent_space I') x₀ x y₀ y ϕ = ϕ :=
begin
  refine (vector_bundle_core.in_coordinates_eq _ _ _ _ _).trans _,
  { exact mem_univ x },
  { exact mem_univ y },
  simp_rw [tangent_bundle_core_index_at, tangent_bundle_core_coord_change_model_space,
    continuous_linear_map.id_comp, continuous_linear_map.comp_id]
end

/-- When `ϕ x` is a continuous linear map that changes vectors in charts around `f x` to vectors
in charts around `g x`, `in_tangent_coordinates I I' f g ϕ x₀ x` is a coordinate change of
this continuous linear map that makes sense from charts around `f x₀` to charts around `g x₀`
by composing it with appropriate coordinate changes.
Note that in the type of `ϕ` is more accurately
`Π x : N, tangent_space I (f x) →L[𝕜] tangent_space I' (g x)`.
We are unfolding `tangent_space` in this type so that Lean recognizes that the type of `ϕ` doesn't
actually depend on `f` or `g`.

This is the underlying function of the trivializations of the hom of (pullbacks of) tangent spaces.
-/
def in_tangent_coordinates (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') : N → N → E →L[𝕜] E' :=
λ x₀ x, in_coordinates E (tangent_space I) E' (tangent_space I') (f x₀) (f x) (g x₀) (g x) (ϕ x)

lemma in_tangent_coordinates_model_space (f : N → H) (g : N → H') (ϕ : N → E →L[𝕜] E') (x₀ : N) :
    in_tangent_coordinates I I' f g ϕ x₀ = ϕ :=
by simp_rw [in_tangent_coordinates, in_coordinates_tangent_bundle_core_model_space]

lemma in_tangent_coordinates_eq (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') {x₀ x : N}
  (hx : f x ∈ (chart_at H (f x₀)).source) (hy : g x ∈ (chart_at H' (g x₀)).source) :
  in_tangent_coordinates I I' f g ϕ x₀ x =
  (tangent_bundle_core I' M').coord_change (achart H' (g x)) (achart H' (g x₀)) (g x) ∘L ϕ x ∘L
  (tangent_bundle_core I M).coord_change (achart H (f x₀)) (achart H (f x)) (f x) :=
(tangent_bundle_core I M).in_coordinates_eq (tangent_bundle_core I' M') (ϕ x) hx hy

end in_tangent_coordinates

end general

section real

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
{H : Type*} [topological_space H] {I : model_with_corners ℝ E H}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

instance {x : M} : path_connected_space (tangent_space I x) := by delta_instance tangent_space

end real
