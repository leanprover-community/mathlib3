/-
Copyright (c) 2022 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import geometry.manifold.cont_mdiff
import topology.new_vector_bundle

noncomputable theory

open bundle vector_bundle set
open_locale manifold topological_space bundle

section
variables {𝕜 B B' F M : Type*} {E : B → Type*}

/-! ### Charted space structure on a fiber bundle -/
section
variables [topological_space F] [topological_space (total_space E)] [∀ x, topological_space (E x)]
  {HB : Type*} [topological_space HB]
  [topological_space B] [charted_space HB B]

instance fiber_bundle.charted_space [fiber_bundle F E] :
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
  trans' := begin
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
  symm' := begin
    rintros e ⟨-, ⟨φ, rfl⟩, -, ⟨U, rfl⟩, -, ⟨hU, rfl⟩, -, ⟨hφ, rfl⟩, -, ⟨h2φ, rfl⟩, heφ⟩,
    dsimp at heφ,
    apply mem_Union.mpr,
    use λ b, (φ b).symm,
    simp_rw mem_Union,
    refine ⟨U, hU, h2φ, _, heφ.symm'⟩,
    simp_rw continuous_linear_equiv.symm_symm,
    exact hφ
  end,
  id_mem' := begin
    apply mem_Union.mpr,
    use λ b, continuous_linear_equiv.refl 𝕜 F,
    simp_rw mem_Union,
    refine ⟨univ, is_open_univ, cont_mdiff_on_const, cont_mdiff_on_const, ⟨_, λ b hb, _⟩⟩,
    { simp [smooth_fiberwise_linear.local_homeomorph] },
    { simp [smooth_fiberwise_linear.local_homeomorph] },
  end,
  locality' := sorry, -- a bit tricky, need to glue together a family of `φ`
  eq_on_source' := begin
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
{ compatible := begin
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
variables (I M)

def tangent_bundle_core : vector_bundle_core 𝕜 M E (atlas H M) :=
{ base_set := λ i, i.1.source,
  is_open_base_set := λ i, i.1.open_source,
  index_at := achart H,
  mem_base_set_at := mem_chart_source H,
  coord_change := λ i j x, fderiv_within 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm) (range I) (I (i.1 x)),
  coord_change_self :=
    λ i x hx v, begin
    /- Locally, a self-change of coordinate is just the identity, thus its derivative is the
    identity. One just needs to write this carefully, paying attention to the sets where the
    functions are defined. -/
    have A : I.symm ⁻¹' (i.1.symm.trans i.1).source ∩ range I ∈ 𝓝[range I] (I (i.1 x)),
    { rw inter_comm,
      apply inter_mem_nhds_within,
      apply I.continuous_symm.continuous_at.preimage_mem_nhds
        (is_open.mem_nhds (local_homeomorph.open_source _) _),
      simp only [hx, i.1.map_target] with mfld_simps },
    have B : ∀ᶠ y in 𝓝[range I] (I (i.1 x)),
      (I ∘ i.1 ∘ i.1.symm ∘ I.symm) y = (id : E → E) y,
    { filter_upwards [A] with _ hy,
      rw ← I.image_eq at hy,
      rcases hy with ⟨z, hz⟩,
      simp only with mfld_simps at hz,
      simp only [hz.2.symm, hz.1] with mfld_simps, },
    have C : fderiv_within 𝕜 (I ∘ i.1 ∘ i.1.symm ∘ I.symm) (range I) (I (i.1 x)) =
             fderiv_within 𝕜 (id : E → E) (range I) (I (i.1 x)) :=
      filter.eventually_eq.fderiv_within_eq I.unique_diff_at_image B
      (by simp only [hx] with mfld_simps),
    rw fderiv_within_id I.unique_diff_at_image at C,
    rw C,
    refl
  end,
  continuous_on_coord_change := sorry,
  coord_change_comp := λ i j u x hx, begin
    sorry
    -- /- The cocycle property is just the fact that the derivative of a composition is the product of
    -- the derivatives. One needs however to check that all the functions one considers are smooth, and
    -- to pay attention to the domains where these functions are defined, making this proof a little
    -- bit cumbersome although there is nothing complicated here. -/
    -- have M : I (i.1 x) ∈
    --   (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I) :=
    -- ⟨by simpa only [mem_preimage, model_with_corners.left_inv] using hx, mem_range_self _⟩,
    -- have U : unique_diff_within_at 𝕜
    --   (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I) (I (i.1 x)) :=
    --   I.unique_diff_preimage_source _ M,
    -- have A : fderiv_within 𝕜 ((I ∘ u.1 ∘ j.1.symm ∘ I.symm) ∘ (I ∘ j.1 ∘ i.1.symm ∘ I.symm))
    --          (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
    --          (I (i.1 x))
    --   = (fderiv_within 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm)
    --          (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I)
    --          ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I (i.1 x)))).comp
    --     (fderiv_within 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
    --          (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
    --          (I (i.1 x))),
    -- { apply fderiv_within.comp _ _ _ _ U,
    --   show differentiable_within_at 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
    --     (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
    --     (I (i.1 x)),
    --   { have A : cont_diff_on 𝕜 ∞
    --       (I ∘ (i.1.symm.trans j.1) ∘ I.symm)
    --       (I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I) :=
    --     (has_groupoid.compatible (cont_diff_groupoid ∞ I) i.2 j.2).1,
    --     have B : differentiable_on 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
    --       (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I),
    --     { apply (A.differentiable_on le_top).mono,
    --       have : ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ⊆
    --         (i.1.symm.trans j.1).source := inter_subset_left _ _,
    --       exact inter_subset_inter (preimage_mono this) (subset.refl (range I)) },
    --     apply B,
    --     simpa only [] with mfld_simps using hx },
    --   show differentiable_within_at 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm)
    --     (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I)
    --     ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I (i.1 x))),
    --   { have A : cont_diff_on 𝕜 ∞
    --       (I ∘ (j.1.symm.trans u.1) ∘ I.symm)
    --       (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I) :=
    --     (has_groupoid.compatible (cont_diff_groupoid ∞ I) j.2 u.2).1,
    --     apply A.differentiable_on le_top,
    --     rw [local_homeomorph.trans_source] at hx,
    --     simp only with mfld_simps,
    --     exact hx.2 },
    --   show (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
    --     ⊆ (I ∘ j.1 ∘ i.1.symm ∘ I.symm) ⁻¹' (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I),
    --   { assume y hy,
    --     simp only with mfld_simps at hy,
    --     rw [local_homeomorph.left_inv] at hy,
    --     { simp only [hy] with mfld_simps },
    --     { exact hy.1.1.2 } } },
    -- have B : fderiv_within 𝕜 ((I ∘ u.1 ∘ j.1.symm ∘ I.symm)
    --                       ∘ (I ∘ j.1 ∘ i.1.symm ∘ I.symm))
    --          (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
    --          (I (i.1 x))
    --          = fderiv_within 𝕜 (I ∘ u.1 ∘ i.1.symm ∘ I.symm)
    --          (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
    --          (I (i.1 x)),
    -- { have E :
    --     ∀ y ∈ (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I),
    --       ((I ∘ u.1 ∘ j.1.symm ∘ I.symm) ∘ (I ∘ j.1 ∘ i.1.symm ∘ I.symm)) y =
    --         (I ∘ u.1 ∘ i.1.symm ∘ I.symm) y,
    --   { assume y hy,
    --     simp only [function.comp_app, model_with_corners.left_inv],
    --     rw [j.1.left_inv],
    --     exact hy.1.1.2 },
    --   exact fderiv_within_congr U E (E _ M) },
    -- have C : fderiv_within 𝕜 (I ∘ u.1 ∘ i.1.symm ∘ I.symm)
    --          (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
    --          (I (i.1 x)) =
    --          fderiv_within 𝕜 (I ∘ u.1 ∘ i.1.symm ∘ I.symm)
    --          (range I) (I (i.1 x)),
    -- { rw inter_comm,
    --   apply fderiv_within_inter _ I.unique_diff_at_image,
    --   apply I.continuous_symm.continuous_at.preimage_mem_nhds
    --     (is_open.mem_nhds (local_homeomorph.open_source _) _),
    --   simpa only [model_with_corners.left_inv] using hx },
    -- have D : fderiv_within 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm)
    --   (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I) ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I (i.1 x))) =
    --   fderiv_within 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm) (range I) ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I (i.1 x))),
    -- { rw inter_comm,
    --   apply fderiv_within_inter _ I.unique_diff_at_image,
    --   apply I.continuous_symm.continuous_at.preimage_mem_nhds
    --     (is_open.mem_nhds (local_homeomorph.open_source _) _),
    --   rw [local_homeomorph.trans_source] at hx,
    --   simp only with mfld_simps,
    --   exact hx.2 },
    -- have E : fderiv_within 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
    --            (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
    --            (I (i.1 x)) =
    --          fderiv_within 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm) (range I) (I (i.1 x)),
    -- { rw inter_comm,
    --   apply fderiv_within_inter _ I.unique_diff_at_image,
    --   apply I.continuous_symm.continuous_at.preimage_mem_nhds
    --     (is_open.mem_nhds (local_homeomorph.open_source _) _),
    --   simpa only [model_with_corners.left_inv] using hx },
    -- rw [B, C, D, E] at A,
    -- simp only [A, continuous_linear_map.coe_comp'] with mfld_simps,
  end }

--   def to_topological_vector_bundle_core : topological_vector_bundle_core 𝕜 M F (atlas H M) :=
-- { base_set := λ i, i.1.source,
--   is_open_base_set := λ i, i.1.open_source,
--   index_at := achart H,
--   mem_base_set_at := λ x, mem_chart_source H x,
--   coord_change := λ i j x, Z.coord_change i j (i.1 x),
--   coord_change_self := λ i x hx v, Z.coord_change_self i (i.1 x) (i.1.map_source hx) v,
--   coord_change_comp := λ i j k x ⟨⟨hx1, hx2⟩, hx3⟩ v, begin
--     have := Z.coord_change_comp i j k (i.1 x) _ v,
--     convert this using 2,
--     { simp only [hx1] with mfld_simps },
--     { simp only [hx1, hx2, hx3] with mfld_simps }
--   end,
--   coord_change_continuous := λ i j, begin
--     refine ((Z.coord_change_continuous i j).comp' i.1.continuous_on).mono _,
--     rintros p ⟨hp₁, hp₂⟩,
--     refine ⟨hp₁, i.1.maps_to hp₁, _⟩,
--     simp only [i.1.left_inv hp₁, hp₂] with mfld_simps
--   end }

-- { coord_change := λ i j x, (fderiv_within 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm) (range I) (I x)),
--   coord_change_smooth_clm := λ i j,
--   begin
--     rw I.image_eq,
--     have A : cont_diff_on 𝕜 ∞
--       (I ∘ (i.1.symm.trans j.1) ∘ I.symm)
--       (I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I) :=
--       (has_groupoid.compatible (cont_diff_groupoid ∞ I) i.2 j.2).1,
--     have B : unique_diff_on 𝕜 (I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I) :=
--       I.unique_diff_preimage_source,
--     have C : cont_diff_on 𝕜 ∞
--       (λ (p : E × E), (fderiv_within 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
--             (I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I) p.1 : E → E) p.2)
--       ((I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I) ×ˢ univ) :=
--       cont_diff_on_fderiv_within_apply A B le_top,
--     have D : ∀ x ∈ (I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I),
--       fderiv_within 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
--             (range I) x =
--       fderiv_within 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
--             (I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I) x,
--     { assume x hx,
--       have N : I.symm ⁻¹' (i.1.symm.trans j.1).source ∈ nhds x :=
--         I.continuous_symm.continuous_at.preimage_mem_nhds
--           (is_open.mem_nhds (local_homeomorph.open_source _) hx.1),
--       symmetry,
--       rw inter_comm,
--       exact fderiv_within_inter N (I.unique_diff _ hx.2) },
--     apply (A.fderiv_within B le_top).congr,
--     assume x hx,
--     simp only with mfld_simps at hx,
--     simp only [hx, D] with mfld_simps,
--   end,
--   coord_change_self := λ i x hx v, begin
--     /- Locally, a self-change of coordinate is just the identity, thus its derivative is the
--     identity. One just needs to write this carefully, paying attention to the sets where the
--     functions are defined. -/
--     have A : I.symm ⁻¹' (i.1.symm.trans i.1).source ∩ range I ∈ 𝓝[range I] (I x),
--     { rw inter_comm,
--       apply inter_mem_nhds_within,
--       apply I.continuous_symm.continuous_at.preimage_mem_nhds
--         (is_open.mem_nhds (local_homeomorph.open_source _) _),
--       simp only [hx, i.1.map_target] with mfld_simps },
--     have B : ∀ᶠ y in 𝓝[range I] (I x),
--       (I ∘ i.1 ∘ i.1.symm ∘ I.symm) y = (id : E → E) y,
--     { filter_upwards [A] with _ hy,
--       rw ← I.image_eq at hy,
--       rcases hy with ⟨z, hz⟩,
--       simp only with mfld_simps at hz,
--       simp only [hz.2.symm, hz.1] with mfld_simps, },
--     have C : fderiv_within 𝕜 (I ∘ i.1 ∘ i.1.symm ∘ I.symm) (range I) (I x) =
--              fderiv_within 𝕜 (id : E → E) (range I) (I x) :=
--       filter.eventually_eq.fderiv_within_eq I.unique_diff_at_image B
--       (by simp only [hx] with mfld_simps),
--     rw fderiv_within_id I.unique_diff_at_image at C,
--     rw C,
--     refl
--   end,
--   coord_change_comp := λ i j u x hx, begin
--     /- The cocycle property is just the fact that the derivative of a composition is the product of
--     the derivatives. One needs however to check that all the functions one considers are smooth, and
--     to pay attention to the domains where these functions are defined, making this proof a little
--     bit cumbersome although there is nothing complicated here. -/
--     have M : I x ∈
--       (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I) :=
--     ⟨by simpa only [mem_preimage, model_with_corners.left_inv] using hx, mem_range_self _⟩,
--     have U : unique_diff_within_at 𝕜
--       (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I) (I x) :=
--       I.unique_diff_preimage_source _ M,
--     have A : fderiv_within 𝕜 ((I ∘ u.1 ∘ j.1.symm ∘ I.symm) ∘ (I ∘ j.1 ∘ i.1.symm ∘ I.symm))
--              (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
--              (I x)
--       = (fderiv_within 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm)
--              (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I)
--              ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x))).comp
--         (fderiv_within 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
--              (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
--              (I x)),
--     { apply fderiv_within.comp _ _ _ _ U,
--       show differentiable_within_at 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
--         (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
--         (I x),
--       { have A : cont_diff_on 𝕜 ∞
--           (I ∘ (i.1.symm.trans j.1) ∘ I.symm)
--           (I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I) :=
--         (has_groupoid.compatible (cont_diff_groupoid ∞ I) i.2 j.2).1,
--         have B : differentiable_on 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
--           (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I),
--         { apply (A.differentiable_on le_top).mono,
--           have : ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ⊆
--             (i.1.symm.trans j.1).source := inter_subset_left _ _,
--           exact inter_subset_inter (preimage_mono this) (subset.refl (range I)) },
--         apply B,
--         simpa only [] with mfld_simps using hx },
--       show differentiable_within_at 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm)
--         (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I)
--         ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x)),
--       { have A : cont_diff_on 𝕜 ∞
--           (I ∘ (j.1.symm.trans u.1) ∘ I.symm)
--           (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I) :=
--         (has_groupoid.compatible (cont_diff_groupoid ∞ I) j.2 u.2).1,
--         apply A.differentiable_on le_top,
--         rw [local_homeomorph.trans_source] at hx,
--         simp only with mfld_simps,
--         exact hx.2 },
--       show (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
--         ⊆ (I ∘ j.1 ∘ i.1.symm ∘ I.symm) ⁻¹' (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I),
--       { assume y hy,
--         simp only with mfld_simps at hy,
--         rw [local_homeomorph.left_inv] at hy,
--         { simp only [hy] with mfld_simps },
--         { exact hy.1.1.2 } } },
--     have B : fderiv_within 𝕜 ((I ∘ u.1 ∘ j.1.symm ∘ I.symm)
--                           ∘ (I ∘ j.1 ∘ i.1.symm ∘ I.symm))
--              (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
--              (I x)
--              = fderiv_within 𝕜 (I ∘ u.1 ∘ i.1.symm ∘ I.symm)
--              (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
--              (I x),
--     { have E :
--         ∀ y ∈ (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I),
--           ((I ∘ u.1 ∘ j.1.symm ∘ I.symm) ∘ (I ∘ j.1 ∘ i.1.symm ∘ I.symm)) y =
--             (I ∘ u.1 ∘ i.1.symm ∘ I.symm) y,
--       { assume y hy,
--         simp only [function.comp_app, model_with_corners.left_inv],
--         rw [j.1.left_inv],
--         exact hy.1.1.2 },
--       exact fderiv_within_congr U E (E _ M) },
--     have C : fderiv_within 𝕜 (I ∘ u.1 ∘ i.1.symm ∘ I.symm)
--              (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
--              (I x) =
--              fderiv_within 𝕜 (I ∘ u.1 ∘ i.1.symm ∘ I.symm)
--              (range I) (I x),
--     { rw inter_comm,
--       apply fderiv_within_inter _ I.unique_diff_at_image,
--       apply I.continuous_symm.continuous_at.preimage_mem_nhds
--         (is_open.mem_nhds (local_homeomorph.open_source _) _),
--       simpa only [model_with_corners.left_inv] using hx },
--     have D : fderiv_within 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm)
--       (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I) ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x)) =
--       fderiv_within 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm) (range I) ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x)),
--     { rw inter_comm,
--       apply fderiv_within_inter _ I.unique_diff_at_image,
--       apply I.continuous_symm.continuous_at.preimage_mem_nhds
--         (is_open.mem_nhds (local_homeomorph.open_source _) _),
--       rw [local_homeomorph.trans_source] at hx,
--       simp only with mfld_simps,
--       exact hx.2 },
--     have E : fderiv_within 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
--                (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
--                (I x) =
--              fderiv_within 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm) (range I) (I x),
--     { rw inter_comm,
--       apply fderiv_within_inter _ I.unique_diff_at_image,
--       apply I.continuous_symm.continuous_at.preimage_mem_nhds
--         (is_open.mem_nhds (local_homeomorph.open_source _) _),
--       simpa only [model_with_corners.left_inv] using hx },
--     rw [B, C, D, E] at A,
--     simp only [A, continuous_linear_map.coe_comp'] with mfld_simps,
--   end }

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

instance tangent_bundle_core.is_smooth : (tangent_bundle_core I M).is_smooth I :=
sorry

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
  have A : ∀ x_fst, fderiv_within 𝕜 (I ∘ I.symm) (range I) (I x_fst) = continuous_linear_map.id 𝕜 E,
  { assume x_fst,
    have : fderiv_within 𝕜 (I ∘ I.symm) (range I) (I x_fst)
         = fderiv_within 𝕜 id (range I) (I x_fst),
    { refine fderiv_within_congr I.unique_diff_at_image (λ y hy, _) (by simp),
      exact model_with_corners.right_inv _ hy },
    rwa fderiv_within_id I.unique_diff_at_image at this },
  ext x : 1,
  show (chart_at (model_prod H E) p : tangent_bundle I H → model_prod H E) x =
    (equiv.sigma_equiv_prod H E) x,
  { cases x,
    simp only [chart_at, tangent_bundle_core,
      A, prod.mk.inj_iff,
      continuous_linear_map.coe_id'] with mfld_simps,
      sorry
      -- refine (tangent_bundle_core I H).coord_change_self _ _ trivial x_snd,
       },
  show ∀ x, ((chart_at (model_prod H E) p).to_local_equiv).symm x =
    (equiv.sigma_equiv_prod H E).symm x,
  { rintros ⟨x_fst, x_snd⟩,
    simp only [tangent_bundle_core, A, continuous_linear_map.coe_id',
      chart_at, continuous_linear_map.coe_coe, sigma.mk.inj_iff] with mfld_simps,
    sorry },
  show ((chart_at (model_prod H E) p).to_local_equiv).source = univ,
  sorry
    -- by simp only [chart_at] with mfld_simps,
end

@[simp, mfld_simps] lemma tangent_bundle_model_space_coe_chart_at (p : tangent_bundle I H) :
  ⇑(chart_at (model_prod H E) p) = equiv.sigma_equiv_prod H E :=
by { unfold_coes, simp only with mfld_simps }

@[simp, mfld_simps] lemma tangent_bundle_model_space_coe_chart_at_symm (p : tangent_bundle I H) :
  ((chart_at (model_prod H E) p).symm : model_prod H E → tangent_bundle I H) =
  (equiv.sigma_equiv_prod H E).symm :=
by { unfold_coes, simp only with mfld_simps }

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
      simp only with mfld_simps },
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
