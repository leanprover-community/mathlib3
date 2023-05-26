/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import geometry.manifold.vector_bundle.hom
import geometry.manifold.vector_bundle.smooth_section
import geometry.manifold.partition_of_unity

/-! # Riemannian metrics -/

noncomputable theory
open_locale manifold
open bundle

variables
  (E : Type*) [normed_add_comm_group E] [normed_space ℝ E]
  (M : Type*) [_i : topological_space M] [charted_space E M]
  [smooth_manifold_with_corners 𝓘(ℝ, E) M]

-- move this
instance (x : M) : has_continuous_add (bundle.trivial M ℝ x) :=
id (infer_instance : has_continuous_add ℝ)

-- move this
instance (x : M) : topological_add_group (bundle.trivial M ℝ x) :=
id (infer_instance : topological_add_group ℝ)

-- move this
instance (x : M) : has_continuous_smul ℝ (bundle.trivial M ℝ x) :=
(infer_instance : has_continuous_smul ℝ ℝ)

include _i

/-- The cotangent space at a point `x` in a smooth manifold `M`. -/
@[derive [inhabited, topological_space, add_comm_group, module ℝ]]
def cotangent_space (x : M) : Type* :=
bundle.continuous_linear_map
  (ring_hom.id ℝ) E (tangent_space 𝓘(ℝ, E)) ℝ (trivial M ℝ) x

namespace cotangent_space

instance : topological_space (total_space (cotangent_space E M)) :=
continuous_linear_map.topological_space_total_space
  (ring_hom.id ℝ) E (tangent_space 𝓘(ℝ, E)) ℝ (trivial M ℝ)

instance : fiber_bundle (E →L[ℝ] ℝ) (cotangent_space E M) :=
continuous_linear_map.fiber_bundle _ _ _ _ _

instance : vector_bundle ℝ (E →L[ℝ] ℝ) (cotangent_space E M) :=
continuous_linear_map.vector_bundle (ring_hom.id ℝ) E (tangent_space 𝓘(ℝ, E)) ℝ (trivial M ℝ)

instance : smooth_vector_bundle (E →L[ℝ] ℝ) (cotangent_space E M) 𝓘(ℝ, E) :=
smooth_vector_bundle.continuous_linear_map

instance (x : M) : linear_map_class (cotangent_space E M x) ℝ (tangent_space 𝓘(ℝ, E) x) ℝ :=
continuous_linear_map.semilinear_map_class (ring_hom.id ℝ) _ _ _ _ _

instance (x : M) : has_continuous_add (cotangent_space E M x) := sorry
instance (x : M) : topological_add_group (cotangent_space E M x) := sorry
instance (x : M) : has_continuous_smul ℝ (cotangent_space E M x) := sorry

end cotangent_space

/-- The "bicotangent space" at a point `x` in a smooth manifold `M`; that is, the space of bilinear
maps from `tangent_space 𝓘(ℝ, E) x` to `ℝ`. -/
@[derive [inhabited, topological_space, add_comm_group, module ℝ]]
def bicotangent_space (x : M) : Type* :=
bundle.continuous_linear_map
  (ring_hom.id ℝ) E (tangent_space 𝓘(ℝ, E)) (E →L[ℝ] ℝ) (cotangent_space E M) x

namespace bicotangent_space

instance : topological_space (total_space (bicotangent_space E M)) :=
continuous_linear_map.topological_space_total_space
  (ring_hom.id ℝ) E (tangent_space 𝓘(ℝ, E)) (E →L[ℝ] ℝ) (cotangent_space E M)

instance : fiber_bundle (E →L[ℝ] E →L[ℝ] ℝ) (bicotangent_space E M) :=
continuous_linear_map.fiber_bundle _ _ _ _ _

instance : vector_bundle ℝ (E →L[ℝ] E →L[ℝ] ℝ) (bicotangent_space E M) :=
continuous_linear_map.vector_bundle _ _ _ _ _

instance : smooth_vector_bundle (E →L[ℝ] E →L[ℝ] ℝ) (bicotangent_space E M) 𝓘(ℝ, E) :=
smooth_vector_bundle.continuous_linear_map

instance (x : M) : linear_map_class (bicotangent_space E M x) ℝ (tangent_space 𝓘(ℝ, E) x)
  (cotangent_space E M x) :=
continuous_linear_map.semilinear_map_class (ring_hom.id ℝ) _ _ _ _ _

instance (x : M) : has_continuous_add (bicotangent_space E M x) := sorry
instance (x : M) : topological_add_group (bicotangent_space E M x) := sorry
instance (x : M) : has_continuous_smul ℝ (bicotangent_space E M x) := sorry

end bicotangent_space

variables {E M}

/-- A Riemannian metric on `M` is a smooth, symmetric, positive-definite section of the bundle of
continuous bilinear maps from the tangent bundle of `M` to `ℝ`. -/
structure riemannian_metric
  (g : smooth_section 𝓘(ℝ, E) (E →L[ℝ] E →L[ℝ] ℝ) (bicotangent_space E M)) : Prop :=
(symm : ∀ x : M, ∀ v w : tangent_space 𝓘(ℝ, E) x, g x v w = g x w v)
(posdef : ∀ x : M, ∀ v : tangent_space 𝓘(ℝ, E) x, v ≠ 0 → 0 < g x v v)

/-- The sum of two Riemannian metrics is a Riemannian metric. -/
lemma riemannian_metric.add
  {g₁ g₂ : smooth_section 𝓘(ℝ, E) (E →L[ℝ] E →L[ℝ] ℝ) (bicotangent_space E M)}
  (hg₁ : riemannian_metric g₁) (hg₂ : riemannian_metric g₂) :
  riemannian_metric (g₁ + g₂) :=
{ symm := λ x v w,
  begin
    simp only [pi.add_apply, cont_mdiff_section.coe_add, continuous_linear_map.add_apply,
      hg₁.symm x v w, hg₂.symm x v w],
  end,
  posdef := λ x v hv,
  begin
    have h₁ : 0 < g₁ x v v := hg₁.posdef x v hv,
    have h₂ : 0 < g₂ x v v := hg₂.posdef x v hv,
    simpa only [pi.add_apply, cont_mdiff_section.coe_add, continuous_linear_map.add_apply]
      using add_pos h₁ h₂,
  end }

/-- The scaling of a Riemannian metric by a positive real number is a Riemannian metric. -/
lemma riemannian_metric.smul
  {g : smooth_section 𝓘(ℝ, E) (E →L[ℝ] E →L[ℝ] ℝ) (bicotangent_space E M)}
  (hg : riemannian_metric g) {c : ℝ} (hc : 0 < c) :
  riemannian_metric (c • g) :=
{ symm := λ x v w,
  begin
    simp only [pi.smul_apply, cont_mdiff_section.coe_smul, continuous_linear_map.smul_apply,
      hg.symm x v w],
  end,
  posdef := λ x v hv,
  begin
    have h : 0 < g x v v := hg.posdef x v hv,
    simpa only [pi.smul_apply, cont_mdiff_section.coe_smul, continuous_linear_map.smul_apply]
      using smul_pos hc h,
  end }


variables
  (F : Type*) [normed_add_comm_group F] [inner_product_space ℝ F] [charted_space F M]
  [smooth_manifold_with_corners 𝓘(ℝ, F) M]
variables (E M) [finite_dimensional ℝ F] [sigma_compact_space M] [t2_space M]

/- A (sigma-compact, Hausdorff, finite-dimensional) manifold admits a Riemannian metric. -/
lemma exists_riemannian_metric :
  ∃ g : smooth_section 𝓘(ℝ, F) (F →L[ℝ] F →L[ℝ] ℝ) (bicotangent_space F M),
  riemannian_metric g :=
begin
  let g₀ : F →L[ℝ] F →L[ℝ] ℝ := innerSL ℝ,
  let U : M → set M := λ x, (chart_at F x).source,
  have hU : ∀ i, is_open (U i) := λ x, (chart_at F x).open_source,
  have hUM : set.univ ⊆ ⋃ i, U i,
  { intros x _,
    rw [set.mem_Union],
    use x,
    exact mem_chart_source _ x, },
  obtain ⟨s, hs⟩ :=
    smooth_partition_of_unity.exists_is_subordinate 𝓘(ℝ, F) is_closed_univ U hU hUM,
  let g : Π x y : M, bicotangent_space F M x,
  { intros x y,
    -- let e : Π y : M, tangent_space 𝓘(ℝ, F) y →L[ℝ] F :=
    --   trivialization.continuous_linear_map_at ℝ (trivialization_at F (tangent_space 𝓘(ℝ, F)) x),
    let e₁ := trivialization_at (F →L[ℝ] ℝ) (cotangent_space F M) y,
    letI : mem_trivialization_atlas e₁ := fiber_bundle.trivialization_at.mem_trivialization_atlas y,
    -- let L₁ : (F →L[ℝ] ℝ) →L[ℝ] cotangent_space F M x := trivialization.symmL ℝ e₁ x,
    -- have  := L₁ ∘L g₀,
    -- let e₂ := trivialization_at (F →L[ℝ] F →L[ℝ] ℝ) (bicotangent_space F M) x,
    -- letI : mem_trivialization_atlas e₂ := fiber_bundle.trivialization_at.mem_trivialization_atlas x,
    -- let L₂ := trivialization.continuous_linear_equiv_at ℝ e₂,

    -- let e' := -- Π y : M, cotangent_space F M y →L[ℝ] (F →L[ℝ] ℝ) :=
    --   trivialization.continuous_linear_map_at ℝ (trivialization_at (F →L[ℝ] ℝ) (cotangent_space F M) x),
    -- have := λ y, g₀ ∘L (e y),
    -- have := λ y, (g₀ ∘L (e y)).flip ∘ (e y),
    -- let l := trivialization_at F (tangent_space 𝓘(ℝ, F)) x,
    -- have := bicotangent_space E M,
    -- have : ∑ᶠ i, s i •
  },

end
