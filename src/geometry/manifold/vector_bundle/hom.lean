/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import geometry.manifold.vector_bundle.basic
import topology.vector_bundle.hom

/-! # Homs of smooth vector bundles over the same base space

Here we show that `bundle.continuous_linear_map` is a smooth vector bundle.

Note that we only do this for bundles of linear maps, not for bundles of arbitrary semilinear maps.
To do it for semilinear maps, we would need to generalize `continuous_linear_map.cont_mdiff`
(and `continuous_linear_map.cont_diff`) to semilinear maps.
-/

noncomputable theory

open bundle set local_homeomorph continuous_linear_map pretrivialization
open_locale manifold bundle

/-
def continuous_linear_map.to_normed_space {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_4}
{F : Type u_6} [seminormed_add_comm_group E] [seminormed_add_comm_group F]
[nontrivially_normed_field 𝕜] [nontrivially_normed_field 𝕜₂] [normed_space 𝕜 E] [normed_space 𝕜₂ F]
 {σ₁₂ : 𝕜 →+* 𝕜₂} [ring_hom_isometric σ₁₂] {𝕜' : Type u_3} [normed_field 𝕜'] [normed_space 𝕜' F]
 [smul_comm_class 𝕜₂ 𝕜' F] :
normed_space 𝕜' (E →SL[σ₁₂] F)
-/

variables {𝕜 K K₁ K₂ B F F₁ F₂ M M₁ M₂ : Type*}
  {E : B → Type*} {E₁ : B → Type*} {E₂ : B → Type*}
  [nontrivially_normed_field 𝕜] [nontrivially_normed_field K] [nontrivially_normed_field K₁] [nontrivially_normed_field K₂]
  [algebra 𝕜 K] [algebra 𝕜 K₁] [algebra 𝕜 K₂]
  [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)] [∀ x, module K (E x)] [∀ x, is_scalar_tower 𝕜 K (E x)]
  [normed_add_comm_group F] [normed_space 𝕜 F] [normed_space K F] [is_scalar_tower 𝕜 K F]
  [topological_space (total_space E)] [∀ x, topological_space (E x)]
  [∀ x, add_comm_monoid (E₁ x)] [∀ x, module 𝕜 (E₁ x)] [∀ x, module K₁ (E₁ x)] [∀ x, is_scalar_tower 𝕜 K₁ (E₁ x)]
  [normed_add_comm_group F₁] [normed_space 𝕜 F₁] [normed_space K₁ F₁] [is_scalar_tower 𝕜 K₁ F₁]
  [topological_space (total_space E₁)] [∀ x, topological_space (E₁ x)]
  [∀ x, add_comm_monoid (E₂ x)] [∀ x, module 𝕜 (E₂ x)] [∀ x, module K₂ (E₂ x)] [∀ x, is_scalar_tower 𝕜 K₂ (E₂ x)]
  [normed_add_comm_group F₂] [normed_space 𝕜 F₂] [normed_space K₂ F₂] [is_scalar_tower 𝕜 K₂ F₂]
  [topological_space (total_space E₂)] [∀ x, topological_space (E₂ x)]

  {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
  {HB : Type*} [topological_space HB] (IB : model_with_corners 𝕜 EB HB)
  [topological_space B] [charted_space HB B]
  {EM : Type*} [normed_add_comm_group EM] [normed_space 𝕜 EM]
  {HM : Type*} [topological_space HM] {IM : model_with_corners 𝕜 EM HM}
  [topological_space M] [charted_space HM M] [Is : smooth_manifold_with_corners IM M]
  {n : ℕ∞}
  [fiber_bundle F₁ E₁] [vector_bundle 𝕜 F₁ E₁] [vector_bundle K₁ F₁ E₁] -- plus typeclass about commuting
  [fiber_bundle F₂ E₂] [vector_bundle 𝕜 F₂ E₂] [vector_bundle K₂ F₂ E₂] -- plus typeclass about commuting
  {e₁ e₁' : trivialization F₁ (π E₁)} {e₂ e₂' : trivialization F₂ (π E₂)}
  (σ : K₁ →+* K₂) [ring_hom_isometric σ]

-- #check @continuous_linear_map.to_normed_space K₁ K₂ F₁ F₂ _ _ _ _ _ _ σ _ 𝕜 _ _ _
-- instance : normed_add_comm_group (F₁ →SL[σ] F₂) := sorry
example : normed_space 𝕜 (F₁ →SL[σ] F₂) := by apply_instance

-- #exit
local notation `LE₁E₂` := total_space (bundle.continuous_linear_map σ F₁ E₁ F₂ E₂)

/- This proof is slow, especially the `simp only` and the elaboration of `h₂`. -/
lemma smooth_on_continuous_linear_map_coord_change
  [smooth_manifold_with_corners IB B]
  [smooth_vector_bundle F₁ E₁ IB] [smooth_vector_bundle F₂ E₂ IB]
  [mem_trivialization_atlas e₁] [mem_trivialization_atlas e₁']
  [mem_trivialization_atlas e₂] [mem_trivialization_atlas e₂'] :
  smooth_on IB 𝓘(𝕜, ((F₁ →SL[σ] F₂) →L[𝕜] (F₁ →SL[σ] F₂)))
    ((continuous_linear_map_coord_change σ e₁ e₁' e₂ e₂').restrict_scalars 𝕜)
    ((e₁.base_set ∩ e₂.base_set) ∩ (e₁'.base_set ∩ e₂'.base_set)) :=
begin
  let L₁ := compL 𝕜 F₁ F₂ F₂,
  have h₁ : smooth _ _ _ := L₁.cont_mdiff,
  have h₂ : smooth _ _ _ := (continuous_linear_map.flip (compL 𝕜 F₁ F₁ F₂)).cont_mdiff,
  have h₃ : smooth_on IB _ _ _ := smooth_on_coord_change e₁' e₁,
  have h₄ : smooth_on IB _ _ _ := smooth_on_coord_change e₂ e₂',
  refine ((h₁.comp_smooth_on (h₄.mono _)).clm_comp (h₂.comp_smooth_on (h₃.mono _))).congr _,
  { mfld_set_tac },
  { mfld_set_tac },
  { intros b hb, ext L v,
    simp only [continuous_linear_map_coord_change, continuous_linear_equiv.coe_coe,
      continuous_linear_equiv.arrow_congrSL_apply, comp_apply, function.comp, compL_apply,
      flip_apply, continuous_linear_equiv.symm_symm] },
end

variables [∀ x, has_continuous_add (E₂ x)] [∀ x, has_continuous_smul 𝕜 (E₂ x)]

lemma hom_chart (y₀ y : LE₁E₂) :
  chart_at (model_prod HB (F₁ →L[𝕜] F₂)) y₀ y =
  (chart_at HB y₀.1 y.1, in_coordinates F₁ E₁ F₂ E₂ y₀.1 y.1 y₀.1 y.1 y.2) :=
by simp_rw [fiber_bundle.charted_space_chart_at, trans_apply, local_homeomorph.prod_apply,
  trivialization.coe_coe, local_homeomorph.refl_apply, function.id_def, hom_trivialization_at_apply]

variables {IB}

lemma cont_mdiff_at_hom_bundle (f : M → LE₁E₂) {x₀ : M} {n : ℕ∞} :
  cont_mdiff_at IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n f x₀ ↔
  cont_mdiff_at IM IB n (λ x, (f x).1) x₀ ∧
  cont_mdiff_at IM 𝓘(𝕜, F₁ →L[𝕜] F₂) n
  (λ x, in_coordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
by apply cont_mdiff_at_total_space

lemma smooth_at_hom_bundle (f : M → LE₁E₂) {x₀ : M} :
  smooth_at IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) f x₀ ↔
  smooth_at IM IB (λ x, (f x).1) x₀ ∧
  smooth_at IM 𝓘(𝕜, F₁ →L[𝕜] F₂)
  (λ x, in_coordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
cont_mdiff_at_hom_bundle f

variables [smooth_manifold_with_corners IB B]
  [smooth_vector_bundle F₁ E₁ IB] [smooth_vector_bundle F₂ E₂ IB]

instance bundle.continuous_linear_map.vector_prebundle.is_smooth :
  (bundle.continuous_linear_map.vector_prebundle (ring_hom.id 𝕜) F₁ E₁ F₂ E₂).is_smooth IB :=
{ exists_smooth_coord_change := begin
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩,
    resetI,
    refine ⟨continuous_linear_map_coord_change (ring_hom.id 𝕜) e₁ e₁' e₂ e₂',
      smooth_on_continuous_linear_map_coord_change IB,
      continuous_linear_map_coord_change_apply (ring_hom.id 𝕜) e₁ e₁' e₂ e₂'⟩
  end }

/-- Todo: remove this definition. It is probably needed because of the type-class pi bug
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/vector.20bundles.20--.20typeclass.20inference.20issue
-/
@[reducible]
def smooth_vector_bundle.continuous_linear_map.aux (x) :
  topological_space (bundle.continuous_linear_map (ring_hom.id 𝕜) F₁ E₁ F₂ E₂ x) :=
by apply_instance
local attribute [instance, priority 1] smooth_vector_bundle.continuous_linear_map.aux

instance smooth_vector_bundle.continuous_linear_map :
  smooth_vector_bundle (F₁ →L[𝕜] F₂) (bundle.continuous_linear_map (ring_hom.id 𝕜) F₁ E₁ F₂ E₂)
    IB :=
(bundle.continuous_linear_map.vector_prebundle (ring_hom.id 𝕜) F₁ E₁ F₂ E₂).smooth_vector_bundle IB
