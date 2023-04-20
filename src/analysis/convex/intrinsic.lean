/-
Copyright (c) 2023 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert, Yaël Dillies
-/
import analysis.normed_space.add_torsor_bases
import analysis.normed_space.linear_isometry

/-!
# Intrinsic frontier and interior

This file defines the intrinsic frontier, interior and closure of a set in a normed additive torsor.
These are also known as relative frontier, interior, closure.

The intrinsic frontier/interior/closure of a set `s` is the frontier/interior/closure of `s`
considered as a set in its affine span.

The intrinsic interior is in general greater than the topological interior, the intrinsic frontier
in general less than the topological frontier, and the intrinsic closure in cases of interest the
same as the topological closure.

## Definitions

* `intrinsic_interior`: Intrinsic interior
* `intrinsic_frontier`: Intrinsic frontier
* `intrinsic_closure`: Intrinsic closure

## Results

The main results are:
* `affine_isometry.image_intrinsic_interior`/`affine_isometry.image_intrinsic_frontier`/
  `affine_isometry.image_intrinsic_closure`: Intrinsic interiors/frontiers/closures commute with
  taking the image under an affine isometry.
* `set.nonempty.intrinsic_interior`: The intrinsic interior of a nonempty convex set is nonempty.

## References

* Chapter 8 of [Barry Simon, *Convexity*][simon2011]
* Chapter 1 of [Rolf Schneider, *Convex Bodies: The Brunn-Minkowski theory*][schneider2013].

## TODO

* `is_closed s → is_extreme 𝕜 s (intrinsic_frontier 𝕜 s)`
* `x ∈ s → y ∈ intrinsic_interior 𝕜 s → open_segment 𝕜 x y ⊆ intrinsic_interior 𝕜 s`
-/

open affine_subspace set
open_locale pointwise

variables {𝕜 V W Q P : Type*}

section add_torsor
variables (𝕜) [ring 𝕜] [add_comm_group V] [module 𝕜 V] [topological_space P] [add_torsor V P]
  {s t : set P} {x : P}
include V

/-- The intrinsic interior of a set is its interior considered as a set in its affine span. -/
def intrinsic_interior (s : set P) : set P := coe '' interior (coe ⁻¹' s : set $ affine_span 𝕜 s)

/-- The intrinsic frontier of a set is its frontier considered as a set in its affine span. -/
def intrinsic_frontier (s : set P) : set P := coe '' frontier (coe ⁻¹' s : set $ affine_span 𝕜 s)

/-- The intrinsic closure of a set is its closure considered as a set in its affine span. -/
def intrinsic_closure (s : set P) : set P := coe '' closure (coe ⁻¹' s : set $ affine_span 𝕜 s)

variables {𝕜}

@[simp] lemma mem_intrinsic_interior :
  x ∈ intrinsic_interior 𝕜 s ↔ ∃ y, y ∈ interior (coe ⁻¹' s : set $ affine_span 𝕜 s) ∧ ↑y = x :=
mem_image _ _ _

@[simp] lemma mem_intrinsic_frontier :
  x ∈ intrinsic_frontier 𝕜 s ↔ ∃ y, y ∈ frontier (coe ⁻¹' s : set $ affine_span 𝕜 s) ∧ ↑y = x :=
mem_image _ _ _

@[simp] lemma mem_intrinsic_closure :
  x ∈ intrinsic_closure 𝕜 s ↔ ∃ y, y ∈ closure (coe ⁻¹' s : set $ affine_span 𝕜 s) ∧ ↑y = x :=
mem_image _ _ _

lemma intrinsic_interior_subset : intrinsic_interior 𝕜 s ⊆ s := image_subset_iff.2 interior_subset

lemma intrinsic_frontier_subset (hs : is_closed s) : intrinsic_frontier 𝕜 s ⊆ s :=
image_subset_iff.2 (hs.preimage continuous_induced_dom).frontier_subset

lemma intrinsic_frontier_subset_intrinsic_closure :
  intrinsic_frontier 𝕜 s ⊆ intrinsic_closure 𝕜 s :=
image_subset _ frontier_subset_closure

lemma subset_intrinsic_closure : s ⊆ intrinsic_closure 𝕜 s :=
λ x hx, ⟨⟨x, subset_affine_span _ _ hx⟩, subset_closure hx, rfl⟩

@[simp] lemma intrinsic_interior_empty : intrinsic_interior 𝕜 (∅ : set P) = ∅ :=
by simp [intrinsic_interior]

@[simp] lemma intrinsic_frontier_empty : intrinsic_frontier 𝕜 (∅ : set P) = ∅ :=
by simp [intrinsic_frontier]

@[simp] lemma intrinsic_closure_empty : intrinsic_closure 𝕜 (∅ : set P) = ∅ :=
by simp [intrinsic_closure]

@[simp] lemma intrinsic_closure_nonempty : (intrinsic_closure 𝕜 s).nonempty ↔ s.nonempty :=
⟨by { simp_rw nonempty_iff_ne_empty, rintro h rfl, exact h intrinsic_closure_empty },
  nonempty.mono subset_intrinsic_closure⟩

alias intrinsic_closure_nonempty ↔ set.nonempty.of_intrinsic_closure set.nonempty.intrinsic_closure

attribute [protected] set.nonempty.intrinsic_closure

@[simp] lemma intrinsic_interior_singleton (x : P) : intrinsic_interior 𝕜 ({x} : set P) = {x} :=
by simpa only [intrinsic_interior, preimage_coe_affine_span_singleton, interior_univ, image_univ,
  subtype.range_coe] using coe_affine_span_singleton _ _ _

@[simp] lemma intrinsic_frontier_singleton (x : P) : intrinsic_frontier 𝕜 ({x} : set P) = ∅ :=
by rw [intrinsic_frontier, preimage_coe_affine_span_singleton, frontier_univ, image_empty]

@[simp] lemma intrinsic_closure_singleton (x : P) : intrinsic_closure 𝕜 ({x} : set P) = {x} :=
by simpa only [intrinsic_closure, preimage_coe_affine_span_singleton, closure_univ, image_univ,
  subtype.range_coe] using coe_affine_span_singleton _ _ _

/-!
Note that neither `intrinsic_interior` nor `intrinsic_frontier` is monotone.
-/

lemma intrinsic_closure_mono (h : s ⊆ t) : intrinsic_closure 𝕜 s ⊆ intrinsic_closure 𝕜 t :=
begin
  refine image_subset_iff.2 (λ x hx, ⟨set.inclusion (affine_span_mono _ h) x,
    (continuous_inclusion _).closure_preimage_subset _ $ closure_mono _ hx, rfl⟩),
  exact λ y hy, h hy,
end

lemma interior_subset_intrinsic_interior : interior s ⊆ intrinsic_interior 𝕜 s :=
λ x hx, ⟨⟨x, subset_affine_span _ _ $ interior_subset hx⟩,
  preimage_interior_subset_interior_preimage continuous_subtype_coe hx, rfl⟩

lemma intrinsic_closure_subset_closure : intrinsic_closure 𝕜 s ⊆ closure s :=
image_subset_iff.2 $ continuous_subtype_coe.closure_preimage_subset _

lemma intrinsic_frontier_subset_frontier : intrinsic_frontier 𝕜 s ⊆ frontier s :=
image_subset_iff.2 $ continuous_subtype_coe.frontier_preimage_subset _

lemma intrinsic_closure_subset_affine_span : intrinsic_closure 𝕜 s ⊆ affine_span 𝕜 s :=
(image_subset_range _ _).trans subtype.range_coe.subset

@[simp] lemma intrinsic_closure_diff_intrinsic_frontier (s : set P) :
  intrinsic_closure 𝕜 s \ intrinsic_frontier 𝕜 s = intrinsic_interior 𝕜 s :=
(image_diff subtype.coe_injective _ _).symm.trans $
  by rw [closure_diff_frontier, intrinsic_interior]

@[simp] lemma intrinsic_closure_diff_intrinsic_interior (s : set P) :
  intrinsic_closure 𝕜 s \ intrinsic_interior 𝕜 s = intrinsic_frontier 𝕜 s :=
(image_diff subtype.coe_injective _ _).symm

@[simp] lemma intrinsic_interior_union_intrinsic_frontier (s : set P) :
  intrinsic_interior 𝕜 s ∪ intrinsic_frontier 𝕜 s = intrinsic_closure 𝕜 s :=
by simp [intrinsic_closure, intrinsic_interior, intrinsic_frontier,
  closure_eq_interior_union_frontier, image_union]

@[simp] lemma intrinsic_frontier_union_intrinsic_interior (s : set P) :
  intrinsic_frontier 𝕜 s ∪ intrinsic_interior 𝕜 s = intrinsic_closure 𝕜 s :=
by rw [union_comm, intrinsic_interior_union_intrinsic_frontier]

lemma is_closed_intrinsic_closure (hs : is_closed (affine_span 𝕜 s : set P)) :
  is_closed (intrinsic_closure 𝕜 s) :=
(closed_embedding_subtype_coe hs).is_closed_map _ is_closed_closure

lemma is_closed_intrinsic_frontier (hs : is_closed (affine_span 𝕜 s : set P)) :
  is_closed (intrinsic_frontier 𝕜 s) :=
(closed_embedding_subtype_coe hs).is_closed_map _ is_closed_frontier

@[simp] lemma affine_span_intrinsic_closure (s : set P) :
  affine_span 𝕜 (intrinsic_closure 𝕜 s) = affine_span 𝕜 s :=
(affine_span_le.2 intrinsic_closure_subset_affine_span).antisymm $
  affine_span_mono _ subset_intrinsic_closure

protected lemma is_closed.intrinsic_closure (hs : is_closed (coe ⁻¹' s : set $ affine_span 𝕜 s)) :
  intrinsic_closure 𝕜 s = s :=
begin
  rw [intrinsic_closure, hs.closure_eq, image_preimage_eq_of_subset],
  exact (subset_affine_span _ _).trans subtype.range_coe.superset,
end

@[simp] lemma intrinsic_closure_idem (s : set P) :
  intrinsic_closure 𝕜 (intrinsic_closure 𝕜 s) = intrinsic_closure 𝕜 s :=
begin
  refine is_closed.intrinsic_closure _,
  set t := affine_span 𝕜 (intrinsic_closure 𝕜 s) with ht,
  clear_value t,
  obtain rfl := ht.trans (affine_span_intrinsic_closure _),
  rw [intrinsic_closure, preimage_image_eq _ subtype.coe_injective],
  exact is_closed_closure,
end

end add_torsor

namespace affine_isometry
variables [normed_field 𝕜] [seminormed_add_comm_group V] [seminormed_add_comm_group W]
  [normed_space 𝕜 V] [normed_space 𝕜 W] [metric_space P] [pseudo_metric_space Q]
  [normed_add_torsor V P] [normed_add_torsor W Q]
include V W

local attribute [instance, nolint fails_quickly] affine_subspace.to_normed_add_torsor
  affine_subspace.nonempty_map

@[simp] lemma image_intrinsic_interior (φ : P →ᵃⁱ[𝕜] Q) (s : set P) :
  intrinsic_interior 𝕜 (φ '' s) = φ '' intrinsic_interior 𝕜 s :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp only [intrinsic_interior_empty, image_empty] },
  haveI : nonempty s := hs.to_subtype,
  let f := ((affine_span 𝕜 s).isometry_equiv_map φ).to_homeomorph,
  have : φ.to_affine_map ∘ coe ∘ f.symm = coe := funext isometry_equiv_map.apply_symm_apply,
  rw [intrinsic_interior, intrinsic_interior, ←φ.coe_to_affine_map, ←map_span φ.to_affine_map s,
    ←this, ←function.comp.assoc, image_comp, image_comp, f.symm.image_interior, f.image_symm,
    ←preimage_comp, function.comp.assoc, f.symm_comp_self, affine_isometry.coe_to_affine_map,
    function.comp.right_id, preimage_comp, φ.injective.preimage_image],
end

@[simp] lemma image_intrinsic_frontier (φ : P →ᵃⁱ[𝕜] Q) (s : set P) :
  intrinsic_frontier 𝕜 (φ '' s) = φ '' intrinsic_frontier 𝕜 s :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  haveI : nonempty s := hs.to_subtype,
  let f := ((affine_span 𝕜 s).isometry_equiv_map φ).to_homeomorph,
  have : φ.to_affine_map ∘ coe ∘ f.symm = coe := funext isometry_equiv_map.apply_symm_apply,
  rw [intrinsic_frontier, intrinsic_frontier, ←φ.coe_to_affine_map, ←map_span φ.to_affine_map s,
    ←this, ←function.comp.assoc, image_comp, image_comp, f.symm.image_frontier, f.image_symm,
    ←preimage_comp, function.comp.assoc, f.symm_comp_self, affine_isometry.coe_to_affine_map,
    function.comp.right_id, preimage_comp, φ.injective.preimage_image],
end

@[simp] lemma image_intrinsic_closure (φ : P →ᵃⁱ[𝕜] Q) (s : set P) :
  intrinsic_closure 𝕜 (φ '' s) = φ '' intrinsic_closure 𝕜 s :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  haveI : nonempty s := hs.to_subtype,
  let f := ((affine_span 𝕜 s).isometry_equiv_map φ).to_homeomorph,
  have : φ.to_affine_map ∘ coe ∘ f.symm = coe := funext isometry_equiv_map.apply_symm_apply,
  rw [intrinsic_closure, intrinsic_closure, ←φ.coe_to_affine_map, ←map_span φ.to_affine_map s,
    ←this, ←function.comp.assoc, image_comp, image_comp, f.symm.image_closure, f.image_symm,
    ←preimage_comp, function.comp.assoc, f.symm_comp_self, affine_isometry.coe_to_affine_map,
    function.comp.right_id, preimage_comp, φ.injective.preimage_image],
end

end affine_isometry

section normed_add_torsor
variables (𝕜) [nontrivially_normed_field 𝕜] [complete_space 𝕜] [normed_add_comm_group V]
  [normed_space 𝕜 V] [finite_dimensional 𝕜 V] [metric_space P] [normed_add_torsor V P] (s : set P)
include V

@[simp] lemma intrinsic_closure_eq_closure : intrinsic_closure 𝕜 s = closure s :=
begin
  ext x,
  simp only [mem_closure_iff, mem_intrinsic_closure],
  refine ⟨_, λ h, ⟨⟨x, _⟩, _, subtype.coe_mk _ _⟩⟩,
  { rintro ⟨x, h, rfl⟩ t ht hx,
    obtain ⟨z, hz₁, hz₂⟩ := h _ (continuous_induced_dom.is_open_preimage t ht) hx,
    exact ⟨z, hz₁, hz₂⟩ },
  { by_contradiction hc,
    obtain ⟨z, hz₁, hz₂⟩ := h _ (affine_span 𝕜 s).closed_of_finite_dimensional.is_open_compl hc,
    exact hz₁ (subset_affine_span 𝕜 s hz₂) },
  { rintro _ ⟨t, ht, rfl⟩ hx,
    obtain ⟨y, hyt, hys⟩ := h _ ht hx,
    exact ⟨⟨_, subset_affine_span 𝕜 s hys⟩, hyt, hys⟩ }
end

variables {𝕜}

@[simp] lemma closure_diff_intrinsic_interior (s : set P) :
  closure s \ intrinsic_interior 𝕜 s = intrinsic_frontier 𝕜 s :=
intrinsic_closure_eq_closure 𝕜 s ▸ intrinsic_closure_diff_intrinsic_interior s

@[simp] lemma closure_diff_intrinsic_frontier (s : set P) :
  closure s \ intrinsic_frontier 𝕜 s = intrinsic_interior 𝕜 s :=
intrinsic_closure_eq_closure 𝕜 s ▸ intrinsic_closure_diff_intrinsic_frontier s

end normed_add_torsor

private lemma aux {α β : Type*} [topological_space α] [topological_space β] (φ : α ≃ₜ β)
  (s : set β) :
  (interior s).nonempty ↔ (interior (φ ⁻¹' s)).nonempty :=
by rw [←φ.image_symm, ←φ.symm.image_interior, nonempty_image_iff]

variables [normed_add_comm_group V] [normed_space ℝ V] [finite_dimensional ℝ V] {s : set V}

/-- The intrinsic interior of a nonempty convex set is nonempty. -/
protected lemma set.nonempty.intrinsic_interior (hscv : convex ℝ s) (hsne : s.nonempty) :
  (intrinsic_interior ℝ s).nonempty :=
begin
  haveI := hsne.coe_sort,
  obtain ⟨p, hp⟩ := hsne,
  let p' : affine_span ℝ s := ⟨p, subset_affine_span _ _ hp⟩,
  rw [intrinsic_interior, nonempty_image_iff,
    aux (affine_isometry_equiv.const_vsub ℝ p').symm.to_homeomorph,
    convex.interior_nonempty_iff_affine_span_eq_top, affine_isometry_equiv.coe_to_homeomorph,
    ←affine_isometry_equiv.coe_to_affine_equiv, ←comap_span, affine_span_coe_preimage_eq_top,
    comap_top],
  exact hscv.affine_preimage ((affine_span ℝ s).subtype.comp
    (affine_isometry_equiv.const_vsub ℝ p').symm.to_affine_equiv.to_affine_map),
end

lemma intrinsic_interior_nonempty (hs : convex ℝ s) :
  (intrinsic_interior ℝ s).nonempty ↔ s.nonempty :=
⟨by { simp_rw nonempty_iff_ne_empty, rintro h rfl, exact h intrinsic_interior_empty },
  set.nonempty.intrinsic_interior hs⟩
