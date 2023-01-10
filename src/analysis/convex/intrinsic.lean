/-
Copyright (c) 2023 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert, Yaël Dillies
-/
import analysis.normed_space.add_torsor_bases
import analysis.normed_space.linear_isometry

/-!
# Intrinsic frontier and interior

This file defines the intrinsic frontier and intrinsic interior of s set in
s normed additive torsor, e.g. s real vector space or s nonempty affine subspace thereof.

## Definitions

- `intrinsic_interior`: the intrinsic interior or relative interior (the interior in the affine
  span)
- `intrinsic_frontier`: the intrinsic frontier, intrinsic boundary or relative boundary
- `intrinsic_closure`: the intrinsic closure, which usually equals the closure

## Results

The main results are:

- `affine_isometry.image_intrinsic_interior`: The image of the intrinsic interior under an affine
  isometry is the relative interior of the image.
- `nonempty_intrinsic_interior_of_nonempty_of_convex`: The intrinsic interior of s nonempty convex
  set is nonempty.

## References

* Chapter 8 of [Barry Simon, *Convexity*][simon2011]
* Chapter 1 of [Rolf Schneider, *Convex Bodies: The Brunn-Minkowski theory*][schneider2013].
-/

open set
open_locale pointwise

section add_torsor
variables (R : Type*) {V P : Type*} [ring R] [add_comm_group V] [module R V] [topological_space P]
  [add_torsor V P] {s : set P} {x : P}
include V

/-- The intrinsic interior of s set is its interior considered as s set in its affine span. -/
def intrinsic_interior (s : set P) : set P := coe '' interior (coe ⁻¹' s : set $ affine_span R s)

/-- The intrinsic frontier of s set is its frontier considered as s set in its affine span. -/
def intrinsic_frontier (s : set P) : set P := coe '' frontier (coe ⁻¹' s : set $ affine_span R s)

/-- The intrinsic closure of s set is its closure considered as s set in its affine span. -/
def intrinsic_closure (s : set P) : set P := coe '' closure (coe ⁻¹' s : set $ affine_span R s)

variables {R}

@[simp] lemma mem_intrinsic_interior :
  x ∈ intrinsic_interior R s ↔ ∃ y, y ∈ interior (coe ⁻¹' s : set $ affine_span R s) ∧ ↑y = x :=
mem_image _ _ _

@[simp] lemma mem_intrinsic_frontier :
  x ∈ intrinsic_frontier R s ↔ ∃ y, y ∈ frontier (coe ⁻¹' s : set $ affine_span R s) ∧ ↑y = x :=
mem_image _ _ _

@[simp] lemma mem_intrinsic_closure :
  x ∈ intrinsic_closure R s ↔ ∃ y, y ∈ closure (coe ⁻¹' s : set $ affine_span R s) ∧ ↑y = x :=
mem_image _ _ _

lemma intrinsic_interior_subset : intrinsic_interior R s ⊆ s := image_subset_iff.2 interior_subset

lemma intrinsic_frontier_subset (hs : is_closed s) : intrinsic_frontier R s ⊆ s :=
image_subset_iff.2 (hs.preimage continuous_induced_dom).frontier_subset

@[simp] lemma intrinsic_interior_empty : intrinsic_interior R (∅ : set P) = ∅ :=
subset_empty_iff.1 intrinsic_interior_subset

@[simp] lemma intrinsic_frontier_empty : intrinsic_frontier R (∅ : set P) = ∅ :=
subset_empty_iff.1 $ intrinsic_frontier_subset is_closed_empty

lemma preimage_singleton_eq_univ (x : P) :
  (coe : affine_span R ({x} : set P) → P) ⁻¹' {x} = univ :=
eq_univ_of_forall $ λ y, (affine_subspace.mem_affine_span_singleton _ _ _ _).1 y.2

@[simp] lemma intrinsic_closure_diff_intrinsic_frontier (s : set P) :
  intrinsic_closure R s \ intrinsic_frontier R s = intrinsic_interior R s :=
(image_diff subtype.coe_injective _ _).symm.trans $
  by rw [closure_diff_frontier, intrinsic_interior]

@[simp] lemma intrinsic_closure_diff_intrinsic_interior (s : set P) :
  intrinsic_closure R s \ intrinsic_interior R s = intrinsic_frontier R s :=
(image_diff subtype.coe_injective _ _).symm

@[simp] lemma intrinsic_interior_singleton (x : P) : intrinsic_interior R ({x} : set P) = {x} :=
by simpa only [intrinsic_interior, preimage_singleton_eq_univ, interior_univ, image_univ,
  subtype.range_coe] using affine_subspace.coe_affine_span_singleton _ _ _

@[simp] lemma intrinsic_frontier_singleton (x : P) : intrinsic_frontier R ({x} : set P) = ∅ :=
by rw [intrinsic_frontier, preimage_singleton_eq_univ, frontier_univ, image_empty]

@[simp] lemma intrinsic_closure_singleton (x : P) : intrinsic_closure R ({x} : set P) = {x} :=
by simpa only [intrinsic_closure, preimage_singleton_eq_univ, closure_univ, image_univ,
  subtype.range_coe] using affine_subspace.coe_affine_span_singleton _ _ _

end add_torsor

section local_instances

local attribute [instance, nolint fails_quickly] affine_subspace.to_normed_add_torsor
local attribute [instance, nolint fails_quickly] affine_subspace.nonempty_map

/--
The image of the intrinsic interior under an affine isometry is
the relative interior of the image.
-/
@[simp] -- not sure whether this is the correct direction for simp
lemma affine_isometry.image_intrinsic_interior {𝕜 V V₂ P P₂ : Type*} [normed_field 𝕜]
  [seminormed_add_comm_group V] [seminormed_add_comm_group V₂] [normed_space 𝕜 V]
  [normed_space 𝕜 V₂] [metric_space P] [pseudo_metric_space P₂] [normed_add_torsor V P]
  [normed_add_torsor V₂ P₂] (φ : P →ᵃⁱ[𝕜] P₂) (s : set P) :
  intrinsic_interior 𝕜 (φ '' s) = φ '' intrinsic_interior 𝕜 s :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp only [intrinsic_interior_empty, image_empty] },
  haveI : nonempty s := hs.to_subtype,
  let f := (affine_span 𝕜 s).isometry_equiv_map φ,
  let f' := f.to_homeomorph,
  have : φ.to_affine_map ∘ (coe : affine_span 𝕜 s → P) ∘ f'.symm =
    (coe : (affine_span 𝕜 s).map φ.to_affine_map → P₂),
  { funext x,
    exact affine_subspace.isometry_equiv_map.apply_symm_apply _ },
  simp only [intrinsic_interior, ←φ.coe_to_affine_map],
  rw [intrinsic_interior],
  rw [←affine_subspace.map_span φ.to_affine_map s, ←this,
    ←function.comp.assoc, image_comp _ f'.symm,
    image_comp _ (coe : affine_span 𝕜 s → P), f'.symm.image_interior, f'.image_symm,
    ←preimage_comp, function.comp.assoc, f'.symm_comp_self, affine_isometry.coe_to_affine_map,
    function.comp.right_id, @preimage_comp _ P, φ.injective.preimage_image],
end

end local_instances

@[simp] lemma intrinsic_closure_eq_closure (𝕜 : Type*)
  [nontrivially_normed_field 𝕜] [complete_space 𝕜]
  {V P : Type} [normed_add_comm_group V] [normed_space 𝕜 V]
  [metric_space P] [normed_add_torsor V P]
  (s : set P) [finite_dimensional 𝕜 V] :
  intrinsic_closure 𝕜 s = closure s :=
begin
  simp only [intrinsic_closure],
  ext x,
  simp only [mem_closure_iff, mem_image],
  refine ⟨_, λ h, ⟨⟨x, _⟩, _, subtype.coe_mk _ _⟩⟩,
  { rintro ⟨x, h, rfl⟩ t ht hx,
    obtain ⟨z, hz₁, hz₂⟩ := h _
                   (continuous_induced_dom.is_open_preimage t ht) hx,
    exact ⟨z, hz₁, hz₂⟩ },
  { by_contradiction hc,
    obtain ⟨z, hz₁, hz₂⟩ := h
      (affine_span 𝕜 s)ᶜ
      (affine_subspace.closed_of_finite_dimensional (affine_span 𝕜 s)).is_open_compl
      hc,
    exact hz₁ (subset_affine_span 𝕜 s hz₂) },
  intros t ht hx,
  rw is_open_induced_iff at ht,
  obtain ⟨t, ht, rfl⟩ := ht,
  obtain ⟨w, hwo, hwA⟩ := h _ ht hx,
  exact ⟨⟨w, subset_affine_span 𝕜 s hwA⟩, hwo, hwA⟩,
end

@[simp] lemma closure_diff_intrinsic_interior {𝕜 : Type*}
  [nontrivially_normed_field 𝕜] [complete_space 𝕜]
  {V P : Type} [normed_add_comm_group V] [normed_space 𝕜 V] [finite_dimensional 𝕜 V]
  [metric_space P] [normed_add_torsor V P]
  (s : set P) : closure s \ intrinsic_interior 𝕜 s = intrinsic_frontier 𝕜 s :=
(intrinsic_closure_eq_closure 𝕜 s) ▸ intrinsic_closure_diff_intrinsic_interior s

lemma nonempty_intrinsic_interior_of_nonempty_of_convex.aux {α β : Type*}
  [topological_space α] [topological_space β] (φ : α ≃ₜ β) (s : set β) :
  (interior s).nonempty ↔ (interior (φ ⁻¹' s)).nonempty :=
by rw [←φ.image_symm, ←φ.symm.image_interior, nonempty_image_iff]

lemma nonempty_intrinsic_interior_of_nonempty_of_convex.aux_2 {𝕜 V₁ P₁ V₂ P₂ : Type*}
  [normed_field 𝕜] [normed_add_comm_group V₁] [normed_add_comm_group V₂]
  [pseudo_metric_space P₁] [pseudo_metric_space P₂] [normed_space 𝕜 V₁] [normed_space 𝕜 V₂]
  [normed_add_torsor V₁ P₁] [normed_add_torsor V₂ P₂]
  (f : P₁ ≃ᵃⁱ[𝕜] P₂) (s : set P₂) :
  (affine_span 𝕜 s).comap f.to_affine_equiv.to_affine_map = affine_span 𝕜 (f ⁻¹' s) :=
f.to_affine_equiv.comap_span s

/-- The intrinsic interior of s nonempty convex set is nonempty. -/
lemma set.nonempty.intrinsic_interior
  {V : Type*} [normed_add_comm_group V] [normed_space ℝ V] [finite_dimensional ℝ V]
  {s : set V} (Ane : s.nonempty) (Acv : convex ℝ s) : (intrinsic_interior ℝ s).nonempty :=
begin
  haveI : nonempty s := nonempty_coe_sort.mpr Ane,
  rw [intrinsic_interior, nonempty_image_iff],
  obtain ⟨p, hp⟩ := Ane,
  let p' : affine_span ℝ s := ⟨p, subset_affine_span _ _ hp⟩,
  rw [nonempty_intrinsic_interior_of_nonempty_of_convex.aux
    (affine_isometry_equiv.const_vsub ℝ p').symm.to_homeomorph,
    convex.interior_nonempty_iff_affine_span_eq_top],
  { rw [affine_isometry_equiv.coe_to_homeomorph,
        ←nonempty_intrinsic_interior_of_nonempty_of_convex.aux_2
          (affine_isometry_equiv.const_vsub ℝ p').symm,
        affine_span_coe_preimage_eq_top s],
    exact affine_subspace.comap_top },
  { exact convex.affine_preimage ((affine_span ℝ s).subtype.comp
    (affine_isometry_equiv.const_vsub ℝ p').symm.to_affine_equiv.to_affine_map) Acv },
end
