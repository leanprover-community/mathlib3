/-
Copyright (c) 2022 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import geometry.manifold.vector_bundle.fiberwise_linear
import topology.vector_bundle.constructions

open bundle vector_bundle set
open_locale manifold


variables {𝕜 B B' F M : Type*} {E : B → Type*}

/-! ### Charted space structure on a fiber bundle -/
section
variables [topological_space F] [topological_space (total_space E)] [∀ x, topological_space (E x)]
  {HB : Type*} [topological_space HB]
  [topological_space B] [charted_space HB B]

instance fiber_bundle.charted_space [fiber_bundle F E] :
  charted_space (B × F) (total_space E) :=
{ atlas := (λ e : trivialization F (@total_space.proj _ E), e.to_local_homeomorph) ''
    trivialization_atlas F E,
  chart_at := λ x, (trivialization_at F E x.proj).to_local_homeomorph,
  mem_chart_source := λ x, (trivialization_at F E x.proj).mem_source.mpr
    (mem_base_set_trivialization_at F E x.proj),
  chart_mem_atlas := λ x, mem_image_of_mem _ (trivialization_mem_atlas F E _) }

local attribute [reducible] model_prod

instance fiber_bundle.charted_space' [fiber_bundle F E] :
  charted_space (model_prod HB F) (total_space E) :=
charted_space.comp _ (model_prod B F) _

end

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

variables (IB F E) {B}

/-! ### Smooth vector bundles -/

variables [fiber_bundle F E] [vector_bundle 𝕜 F E]

/-- Class stating that a topological vector bundle is smooth, in the sense of having smooth
transition functions. -/
class smooth_vector_bundle : Prop :=
(smooth_on_coord_change : ∀ (e e' : trivialization F (@total_space.proj _ E))
  [mem_trivialization_atlas e] [mem_trivialization_atlas e'],
  smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (λ b : B, (e.coord_changeL 𝕜 e' b : F →L[𝕜] F))
  (e.base_set ∩ e'.base_set))

export smooth_vector_bundle (smooth_on_coord_change)
variables [smooth_vector_bundle F E IB]

/-- For a smooth vector bundle `E` over `B` with fibre modelled on `F`, the change-of-co-ordinates
between two trivializations `e`, `e'` for `E`, considered as charts to `B × F`, is smooth and
fibrewise linear. -/
instance : has_groupoid (total_space E) (smooth_fiberwise_linear B F IB) :=
{ compatible := begin
    rintros _ _ ⟨e, i : mem_trivialization_atlas e, rfl⟩ ⟨e', i' : mem_trivialization_atlas e', rfl⟩,
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

class vector_bundle_core.is_smooth' : Prop :=
(smooth_on_coord_change [] :
  ∀ i j, smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (Z.coord_change i j) (Z.base_set i ∩ Z.base_set j))

variables [Z.is_smooth' IB]

export vector_bundle_core.is_smooth'
  (renaming smooth_on_coord_change → vector_bundle_core.smooth_on_coord_change)
#check Z.smooth_on_coord_change IB


namespace vector_bundle_core

class is_smooth : Prop :=
(smooth_on_coord_change [] :
  ∀ i j, smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (Z.coord_change i j) (Z.base_set i ∩ Z.base_set j))

variables [Z.is_smooth IB]

lemma smooth_on_coord_change (i j : ι) :
  smooth_on IB 𝓘(𝕜, F →L[𝕜] F) (Z.coord_change i j) (Z.base_set i ∩ Z.base_set j) :=
is_smooth.smooth_on_coord_change IB Z i j

export vector_bundle_core.is_smooth
  (renaming smooth_on_coord_change → vector_bundle_core.smooth_on_coord_change)
#check Z.smooth_on_coord_change IB

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
  rintros - -
    ⟨⟨e₁, e₂⟩, ⟨i₁ : mem_trivialization_atlas e₁, i₂ : mem_trivialization_atlas e₂⟩, rfl⟩
    ⟨⟨e₁', e₂'⟩, ⟨i₁' : mem_trivialization_atlas e₁', i₂' : mem_trivialization_atlas e₂'⟩, rfl⟩,
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



-- #lint
