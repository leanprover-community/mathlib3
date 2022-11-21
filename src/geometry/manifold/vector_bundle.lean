/-
Copyright (c) 2022 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import geometry.manifold.cont_mdiff
import topology.new_vector_bundle

noncomputable theory

open bundle vector_bundle set smooth_manifold_with_corners
open_locale manifold topological_space bundle

section

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]

lemma fderiv_within_comp {g : F → G} {f : E → F} {x : E} {y : F} {s : set E} {t : set F}
  (hg : differentiable_within_at 𝕜 g t y) (hf : differentiable_within_at 𝕜 f s x)
  (h : maps_to f s t) (hxs : unique_diff_within_at 𝕜 s x) (hy : f x = y) :
  fderiv_within 𝕜 (g ∘ f) s x = (fderiv_within 𝕜 g t y).comp (fderiv_within 𝕜 f s x) :=
by { subst y, exact fderiv_within.comp x hg hf h hxs }

lemma fderiv_within_fderiv_within {g : F → G} {f : E → F} {x : E} {y : F} {s : set E} {t : set F}
  (hg : differentiable_within_at 𝕜 g t y) (hf : differentiable_within_at 𝕜 f s x)
  (h : maps_to f s t) (hxs : unique_diff_within_at 𝕜 s x) (hy : f x = y) (v : E) :
  fderiv_within 𝕜 g t y (fderiv_within 𝕜 f s x v) = fderiv_within 𝕜 (g ∘ f) s x v :=
by { rw [fderiv_within_comp hg hf h hxs hy], refl }

end

section

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
open local_homeomorph

end

section
variables {𝕜 B B' F M : Type*} {E : B → Type*}

/-! ### Charted space structure on a fiber bundle -/
section
variables [topological_space F] [topological_space (total_space E)] [∀ x, topological_space (E x)]
  {HB : Type*} [topological_space HB]
  [topological_space B] [charted_space HB B]

@[simps (mfld_cfg)] instance fiber_bundle.charted_space [fiber_bundle F E] :
  charted_space (B × F) (total_space E) :=
{ atlas := (λ e : trivialization F (π E), e.to_local_homeomorph) '' trivialization_atlas F E,
  chart_at := λ x, (trivialization_at F E x.proj).to_local_homeomorph,
  mem_chart_source := λ x, (trivialization_at F E x.proj).mem_source.mpr
    (mem_base_set_trivialization_at F E x.proj),
  chart_mem_atlas := λ x, mem_image_of_mem _ (trivialization_mem_atlas F E _) }

local attribute [reducible] model_prod

instance fiber_bundle.charted_space' [fiber_bundle F E] :
  charted_space (model_prod HB F) (total_space E) :=
charted_space.comp _ (model_prod B F) _

end

/-! ### The groupoid of smooth, fibrewise-linear maps -/

variables [nontrivially_normed_field 𝕜] [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)]
  [normed_add_comm_group F] [normed_space 𝕜 F]
  [topological_space (total_space E)] [∀ x, topological_space (E x)]

  {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
  {HB : Type*} [topological_space HB] (IB : model_with_corners 𝕜 EB HB)
  [topological_space B] [charted_space HB B] [smooth_manifold_with_corners IB B]
  [topological_space B'] [charted_space HB B'] [smooth_manifold_with_corners IB B']
  {EM : Type*} [normed_add_comm_group EM] [normed_space 𝕜 EM]
  {HM : Type*} [topological_space HM] (IM : model_with_corners 𝕜 EM HM)
  [topological_space M] [charted_space HM M] [smooth_manifold_with_corners IM M]


/-- For `B` a topological space and `F` a `𝕜`-normed space, a map from `U : set B` to `F ≃L[𝕜] F`
determines a local homeomorphism from `B × F` to itself by its action fibrewise. -/
def smooth_fiberwise_linear.local_homeomorph (φ : B → F ≃L[𝕜] F) {U : set B} (hU : is_open U)
  (hφ : continuous_on (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : continuous_on (λ x, (φ x).symm : B → F →L[𝕜] F) U) :
  local_homeomorph (B × F) (B × F) :=
{ to_fun := λ x, (x.1, φ x.1 x.2),
  inv_fun := λ x, (x.1, (φ x.1).symm x.2),
  source := U ×ˢ univ,
  target := U ×ˢ univ,
  map_source' := λ x hx, mk_mem_prod hx.1 (mem_univ _),
  map_target' := λ x hx, mk_mem_prod hx.1 (mem_univ _),
  left_inv' := sorry,
  right_inv' := sorry,
  open_source := hU.prod is_open_univ,
  open_target := hU.prod is_open_univ,
  continuous_to_fun := sorry,
  continuous_inv_fun := sorry }

lemma smooth_fiberwise_linear.source_trans_local_homeomorph {φ : B → (F ≃L[𝕜] F)}
  {U : set B}
  (hU : is_open U)
  (hφ : continuous_on (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : continuous_on (λ x, (φ x).symm : B → F →L[𝕜] F) U)
  {φ' : B → (F ≃L[𝕜] F)}
  {U' : set B}
  (hU' : is_open U')
  (hφ' : continuous_on (λ x, φ' x : B → F →L[𝕜] F) U')
  (h2φ' : continuous_on (λ x, (φ' x).symm : B → F →L[𝕜] F) U') :
  (smooth_fiberwise_linear.local_homeomorph φ hU hφ h2φ ≫ₕ
      smooth_fiberwise_linear.local_homeomorph φ' hU' hφ' h2φ').source = (U ∩ U') ×ˢ univ :=
begin
  sorry,
end

lemma smooth_fiberwise_linear.trans_local_homeomorph_apply {φ : B → (F ≃L[𝕜] F)}
  {U : set B}
  (hU : is_open U)
  (hφ : continuous_on (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : continuous_on (λ x, (φ x).symm : B → F →L[𝕜] F) U)
  {φ' : B → (F ≃L[𝕜] F)}
  {U' : set B}
  (hU' : is_open U')
  (hφ' : continuous_on (λ x, φ' x : B → F →L[𝕜] F) U')
  (h2φ' : continuous_on (λ x, (φ' x).symm : B → F →L[𝕜] F) U')
  {b : B}
  (hb : b ∈ U ∩ U')
  (v : F) :
  (smooth_fiberwise_linear.local_homeomorph φ hU hφ h2φ ≫ₕ
      smooth_fiberwise_linear.local_homeomorph φ' hU' hφ' h2φ') ⟨b, v⟩ = ⟨b, φ' b (φ b v)⟩ :=
begin
  sorry,
end

variables (F B)
/-- For `B` a manifold and `F` a normed space, the groupoid on `B × F` consisting of local
homeomorphisms which are bi-smooth and fibrewise linear. -/
def smooth_fiberwise_linear : structure_groupoid (B × F) :=
{ members := ⋃ (φ : B → F ≃L[𝕜] F) (U : set B) (hU : is_open U)
  (hφ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, φ x : B → F →L[𝕜] F) U)
  (h2φ : smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ x, (φ x).symm : B → F →L[𝕜] F) U),
  {e | e.eq_on_source (smooth_fiberwise_linear.local_homeomorph φ hU hφ.continuous_on h2φ.continuous_on)},
  trans' := by sorry begin
    rintros e e' ⟨-, ⟨φ, rfl⟩, -, ⟨U, rfl⟩, -, ⟨hU, rfl⟩, -, ⟨hφ, rfl⟩, -, ⟨h2φ, rfl⟩, heφ⟩
      ⟨-, ⟨φ', rfl⟩, -, ⟨U', rfl⟩, -, ⟨hU', rfl⟩, -, ⟨hφ', rfl⟩, -, ⟨h2φ', rfl⟩, heφ'⟩,
    dsimp at heφ heφ',
    apply mem_Union.mpr,
    use λ b, (φ b).trans (φ' b),
    simp_rw mem_Union,
    refine ⟨U ∩ U', hU.inter hU', _, _, setoid.trans (heφ.trans' heφ') ⟨_, _⟩⟩,
    { sorry },
    { sorry }, -- two smoothness checks
    { apply smooth_fiberwise_linear.source_trans_local_homeomorph },
    { rintros ⟨b, v⟩ hb,
      apply smooth_fiberwise_linear.trans_local_homeomorph_apply,
      rw smooth_fiberwise_linear.source_trans_local_homeomorph at hb,
      simpa [-mem_inter] using hb }
  end,
  symm' := by sorry begin
    rintros e ⟨-, ⟨φ, rfl⟩, -, ⟨U, rfl⟩, -, ⟨hU, rfl⟩, -, ⟨hφ, rfl⟩, -, ⟨h2φ, rfl⟩, heφ⟩,
    dsimp at heφ,
    apply mem_Union.mpr,
    use λ b, (φ b).symm,
    simp_rw mem_Union,
    refine ⟨U, hU, h2φ, _, heφ.symm'⟩,
    simp_rw continuous_linear_equiv.symm_symm,
    exact hφ
  end,
  id_mem' := by sorry begin
    apply mem_Union.mpr,
    use λ b, continuous_linear_equiv.refl 𝕜 F,
    simp_rw mem_Union,
    refine ⟨univ, is_open_univ, cont_mdiff_on_const, cont_mdiff_on_const, ⟨_, λ b hb, _⟩⟩,
    { simp [smooth_fiberwise_linear.local_homeomorph] },
    { simp [smooth_fiberwise_linear.local_homeomorph] },
  end,
  locality' := sorry, -- a bit tricky, need to glue together a family of `φ`
  eq_on_source' := by sorry begin
    rintros e e' ⟨-, ⟨φ, rfl⟩, -, ⟨U, rfl⟩, -, ⟨hU, rfl⟩, -, ⟨hφ, rfl⟩, -, ⟨h2φ, rfl⟩, heφ⟩ hee',
    apply mem_Union.mpr,
    use φ,
    simp_rw mem_Union,
    refine ⟨U, hU, hφ, h2φ, setoid.trans hee' heφ⟩,
  end }

variables (IB F E) {B}

/-! ### Smooth vector bundles -/

variables [fiber_bundle F E] [vector_bundle 𝕜 F E]

/-- Class stating that a topological vector bundle is smooth, in the sense of having smooth
transition functions. -/
class smooth_vector_bundle : Prop :=
(smooth_on_coord_change : ∀ (e e' : trivialization F (π E))
  [mem_trivialization_atlas e] [mem_trivialization_atlas e'],
  smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ b : B, (e.coord_change 𝕜 e' b : F →L[𝕜] F))
  (e.base_set ∩ e'.base_set))

export smooth_vector_bundle (smooth_on_coord_change)
variables [smooth_vector_bundle F E IB]

/-- For a smooth vector bundle `E` over `B` with fibre modelled on `F`, the change-of-co-ordinates
between two trivializations `e`, `e'` for `E`, considered as charts to `B × F`, is smooth and
fibrewise linear. -/
instance : has_groupoid (total_space E) (smooth_fiberwise_linear B F IB) :=
{ compatible := by sorry begin
    rintros _ _ ⟨e, i, rfl⟩ ⟨e', i', rfl⟩,
    simp_rw [← mem_trivialization_atlas_iff] at i i',
    resetI,
    apply mem_Union.mpr,
    use λ b, e.coord_change 𝕜 e' b,
    simp_rw mem_Union,
    use e.base_set ∩ e'.base_set,
    use e.open_base_set.inter e'.open_base_set,
    use smooth_on_coord_change e e',
    refine ⟨_, _, _⟩,
    { rw inter_comm,
      apply cont_mdiff_on.congr (smooth_on_coord_change e' e),
      { intros b hb,
        rw e.symm_coord_change 𝕜 e' hb },
      { apply_instance },
      { apply_instance }, },
    { simp [e.symm_trans_source_eq e', smooth_fiberwise_linear.local_homeomorph] },
    { rintros ⟨b, v⟩ hb,
      have hb' : b ∈ e.base_set ∩ e'.base_set :=
        by simpa only [local_homeomorph.trans_to_local_equiv, local_homeomorph.symm_to_local_equiv,
        local_homeomorph.coe_coe_symm, e.symm_trans_source_eq e',
        prod_mk_mem_set_prod_eq, mem_univ, and_true] using hb,
      exact e.apply_symm_apply_eq_coord_change 𝕜 e' hb' v, }
  end }

/-- A smooth vector bundle `E` is naturally a smooth manifold. -/
instance : smooth_manifold_with_corners (IB.prod 𝓘(𝕜, F)) (total_space E) :=
begin
  refine { .. structure_groupoid.has_groupoid.comp (smooth_fiberwise_linear B F IB) _ },
  intros e he,
  rw [is_local_structomorph_on_cont_diff_groupoid_iff],
  sorry -- check smoothness
end

variables {ι : Type*} {F} (IB) (Z : vector_bundle_core 𝕜 B F ι)

namespace vector_bundle_core

class is_smooth : Prop :=
(smooth_on_coord_change [] :
  ∀ i j, smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (Z.coord_change i j) (Z.base_set i ∩ Z.base_set j))

alias is_smooth.smooth_on_coord_change ← smooth_on_coord_change

variables [Z.is_smooth IB]

instance smooth_vector_bundle :
  smooth_vector_bundle F Z.to_fiber_bundle_core.fiber IB :=
begin
  constructor,
  rintros _ _ ⟨i, rfl⟩ ⟨i', rfl⟩,
  refine (Z.smooth_on_coord_change IB i i').congr (λ b hb, _),
  ext v,
  simp_rw [continuous_linear_equiv.coe_coe, Z.local_triv_coord_change_eq i i' hb],
end

end vector_bundle_core

section prod
variables (F₁ : Type*) [normed_add_comm_group F₁] [normed_space 𝕜 F₁]
  (E₁ : B → Type*) [topological_space (total_space E₁)]
  [Π x, add_comm_monoid (E₁ x)] [Π x, module 𝕜 (E₁ x)]

variables (F₂ : Type*) [normed_add_comm_group F₂] [normed_space 𝕜 F₂]
  (E₂ : B → Type*) [topological_space (total_space E₂)]
  [Π x, add_comm_monoid (E₂ x)] [Π x, module 𝕜 (E₂ x)]
variables [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [fiber_bundle F₁ E₁] [fiber_bundle F₂ E₂]
  [vector_bundle 𝕜 F₁ E₁] [vector_bundle 𝕜 F₂ E₂]
  [smooth_vector_bundle F₁ E₁ IB] [smooth_vector_bundle F₂ E₂ IB]

/-- The product of two vector bundles is a vector bundle. -/
instance _root_.bundle.prod.smooth_vector_bundle :
  smooth_vector_bundle (F₁ × F₂) (E₁ ×ᵇ E₂) IB :=
begin
  constructor,
  rintros - - ⟨⟨e₁, e₂⟩, ⟨i₁, i₂⟩, rfl⟩ ⟨⟨e₁', e₂'⟩, ⟨i₁', i₂'⟩, rfl⟩,
  simp_rw [← mem_trivialization_atlas_iff] at i₁ i₂ i₁' i₂',
  resetI,
  sorry
  -- refine (((smooth_on_coord_change e₁ e₁').mono _).prod_mapL 𝕜
  --   ((smooth_on_coord_change e₂ e₂').mono _)).congr _,
  -- dsimp only [base_set_prod] with mfld_simps,
  -- { mfld_set_tac },
  -- { mfld_set_tac },
  -- { rintro b hb,
  --   rw [continuous_linear_map.ext_iff],
  --   rintro ⟨v₁, v₂⟩,
  --   show (e₁.prod e₂).coord_change R (e₁'.prod e₂') b (v₁, v₂) =
  --     (e₁.coord_change R e₁' b v₁, e₂.coord_change R e₂' b v₂),
  --   rw [e₁.coord_change_apply R e₁', e₂.coord_change_apply R e₂',
  --     (e₁.prod e₂).coord_change_apply' R],
  --   exacts [rfl, hb, ⟨hb.1.2, hb.2.2⟩, ⟨hb.1.1, hb.2.1⟩] }
end

end prod

end

section tangent_bundle

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

end tangent_bundle


-- #lint
