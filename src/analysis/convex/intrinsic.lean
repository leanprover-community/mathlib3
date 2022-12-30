/-
Copyright (c) 2022 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert, Yaël Dillies
-/
import analysis.convex.basic
import analysis.normed_space.add_torsor_bases
import analysis.normed_space.basic
import analysis.normed_space.linear_isometry
import data.real.basic
import data.set.pointwise.basic
import linear_algebra.affine_space.pointwise

/-!
# Intrinsic frontier and interior

This file defines the intrinsic frontier and intrinsic interior of a set.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011] or chapter 1 of
[Rolf Schneider, *Convex Bodies: The Brunn-Minkowski theory*][schneider2013].
-/

open_locale pointwise

/-- The intrinsic interior of a set is its interior considered as a set in its affine span. -/
def intrinsic_interior (R : Type*) {V P : Type*} [ring R] [seminormed_add_comm_group V] [module R V]
  [pseudo_metric_space P] [normed_add_torsor V P] -- have to redeclare variables to ensure that
                                                  -- all typeclasses are used
  (A : set P) := (coe : affine_span R A → P) '' interior ((coe : affine_span R A → P) ⁻¹' A)

/-- The intrinsic frontier of a set is its frontier considered as a set in its affine span. -/
def intrinsic_frontier (R : Type*) {V P : Type*} [ring R] [seminormed_add_comm_group V] [module R V]
  [pseudo_metric_space P] [normed_add_torsor V P] (A : set P) :=
(coe : affine_span R A → P) '' frontier ((coe : affine_span R A → P) ⁻¹' A)

/-- The intrinsic closure of a set is its closure considered as a set in its affine span. -/
def intrinsic_closure (R : Type*) {V P : Type*} [ring R] [seminormed_add_comm_group V] [module R V]
  [pseudo_metric_space P] [normed_add_torsor V P] (A : set P) :=
(coe : affine_span R A → P) '' closure ((coe : affine_span R A → P) ⁻¹' A)

lemma intrinsic_interior_def (R : Type*) {V P : Type*} [ring R] [seminormed_add_comm_group V]
  [module R V] [pseudo_metric_space P] [normed_add_torsor V P] (A : set P) :
intrinsic_interior R A =
  (coe : affine_span R A → P) '' interior ((coe : affine_span R A → P) ⁻¹' A) := rfl

lemma intrinsic_frontier_def (R : Type*) {V P : Type*} [ring R] [seminormed_add_comm_group V]
  [module R V] [pseudo_metric_space P] [normed_add_torsor V P] (A : set P) :
intrinsic_frontier R A =
  (coe : affine_span R A → P) '' frontier ((coe : affine_span R A → P) ⁻¹' A) := rfl

lemma intrinsic_closure_def (R : Type*) {V P : Type*} [ring R] [seminormed_add_comm_group V]
  [module R V] [pseudo_metric_space P] [normed_add_torsor V P] (A : set P) :
intrinsic_closure R A =
  (coe : affine_span R A → P) '' closure ((coe : affine_span R A → P) ⁻¹' A) := rfl

lemma intrinsic_interior_subset {R : Type*} {V P : Type*} [ring R] [seminormed_add_comm_group V]
  [module R V] [pseudo_metric_space P] [normed_add_torsor V P] (A : set P) :
intrinsic_interior R A ⊆ A :=
set.image_subset_iff.mpr interior_subset

lemma intrinsic_frontier_subset {R : Type*} {V P : Type*} [ring R] [seminormed_add_comm_group V]
  [module R V] [pseudo_metric_space P] [normed_add_torsor V P] {A : set P} (hA : is_closed A) :
intrinsic_frontier R A ⊆ A :=
set.image_subset_iff.mpr (hA.preimage continuous_induced_dom).frontier_subset

@[simp]
lemma intrinsic_interior_empty {R : Type*} {V P : Type*} [ring R] [seminormed_add_comm_group V]
  [module R V] [pseudo_metric_space P] [normed_add_torsor V P] :
intrinsic_interior R (∅ : set P) = ∅ :=
set.subset_empty_iff.mp $ intrinsic_interior_subset _

@[simp]
lemma intrinsic_frontier_empty {R : Type*} {V P : Type*} [ring R] [seminormed_add_comm_group V]
  [module R V] [pseudo_metric_space P] [normed_add_torsor V P] :
intrinsic_frontier R (∅ : set P) = ∅ :=
set.subset_empty_iff.mp $ intrinsic_frontier_subset is_closed_empty

lemma preimage_singleton_eq_univ {R : Type*} {V P : Type*} [ring R]
  [seminormed_add_comm_group V] [module R V] [pseudo_metric_space P] [normed_add_torsor V P]
  (x : P) : (coe : affine_span R ({x} : set P) → P) ⁻¹' {x} = set.univ :=
begin
  refine subset_antisymm (set.subset_univ _) _,
  rintro ⟨y, hy⟩ -,
  obtain rfl := (affine_subspace.mem_affine_span_singleton _ _ _ _).mp hy,
  exact subtype.coe_mk _ _,
end

@[simp] lemma intrinsic_interior_singleton {R : Type*} {V P : Type*} [ring R]
  [seminormed_add_comm_group V] [module R V] [pseudo_metric_space P] [normed_add_torsor V P]
  (x : P) : intrinsic_interior R ({x} : set P) = {x} :=
begin
  rw [intrinsic_interior_def, interior_eq_iff_is_open.mpr], swap,
  { convert is_open_univ,
    exact preimage_singleton_eq_univ x },
  { rw [set.eq_singleton_iff_unique_mem],
    refine ⟨⟨⟨x, _⟩, subtype.coe_mk _ _, subtype.coe_mk _ _⟩, _⟩,
    { exact (affine_subspace.mem_affine_span_singleton _ _ _ _).mpr rfl },
    { rintro - ⟨⟨y, hy₁⟩, hy₂, rfl⟩,
      simpa only [set.mem_preimage, subtype.coe_mk, set.mem_singleton_iff] using hy₂ } },
end

@[simp] lemma intrinsic_frontier_singleton  {R : Type*} {V P : Type*} [ring R]
  [seminormed_add_comm_group V] [module R V] [pseudo_metric_space P] [normed_add_torsor V P]
  (x : P) : intrinsic_frontier R ({x} : set P) = ∅ :=
begin
  rw [intrinsic_frontier_def, set.image_eq_empty],
  convert frontier_univ,
  exact preimage_singleton_eq_univ x,
end

@[simp] lemma intrinsic_closure_diff_intrinsic_interior {R : Type*} {V P : Type*} [ring R]
  [seminormed_add_comm_group V] [module R V] [pseudo_metric_space P] [normed_add_torsor V P]
  (A : set P) :
intrinsic_closure R A \ intrinsic_interior R A = intrinsic_frontier R A :=
begin
  rw [intrinsic_frontier_def, intrinsic_closure_def, intrinsic_interior_def,
    ←set.image_diff subtype.coe_injective],
  refl,
end

section local_instances

local attribute [instance, nolint fails_quickly] affine_subspace.to_normed_add_torsor
local attribute [instance, nolint fails_quickly] affine_subspace.nonempty_map

/--
The image of the intrinsic interior under an affine isometry is
the relative interior of the image.
-/
@[simp] -- not sure whether this is the correct direction for simp
lemma affine_isometry.image_intrinsic_interior {𝕜 V V₂ P P₂: Type*}
  [normed_field 𝕜] [seminormed_add_comm_group V] [seminormed_add_comm_group V₂] [normed_space 𝕜 V]
  [normed_space 𝕜 V₂] [metric_space P] [pseudo_metric_space P₂] [normed_add_torsor V P]
  [normed_add_torsor V₂ P₂]
  (φ : P →ᵃⁱ[𝕜] P₂) (A : set P) :
intrinsic_interior 𝕜 (φ '' A) = φ '' intrinsic_interior 𝕜 A :=
begin
  rcases A.eq_empty_or_nonempty with rfl | hc,
  { simp only [intrinsic_interior_empty, set.image_empty] },
  haveI : nonempty A := hc.to_subtype,
  let f := (affine_span 𝕜 A).isometry_equiv_map φ,
  let f' := f.to_homeomorph,
  have : φ.to_affine_map ∘ (coe : affine_span 𝕜 A → P) ∘ f'.symm =
    (coe : (affine_span 𝕜 A).map φ.to_affine_map → P₂),
  { funext x,
    exact affine_subspace.isometry_equiv_map.apply_symm_apply _ },
  simp only [intrinsic_interior_def, ←φ.coe_to_affine_map],
  rw [intrinsic_interior_def],
  rw [←affine_subspace.map_span φ.to_affine_map A, ←this,
    ←function.comp.assoc, set.image_comp _ f'.symm,
    set.image_comp _ (coe : affine_span 𝕜 A → P), f'.symm.image_interior, f'.image_symm,
    ←set.preimage_comp, function.comp.assoc, f'.symm_comp_self, affine_isometry.coe_to_affine_map,
    function.comp.right_id, @set.preimage_comp _ P, φ.injective.preimage_image],
end

end local_instances

@[simp] lemma intrinsic_closure_eq_closure (𝕜 : Type*)
  [nontrivially_normed_field 𝕜] [complete_space 𝕜]
  {V P : Type} [normed_add_comm_group V] [normed_space 𝕜 V]
  [metric_space P] [normed_add_torsor V P]
  (A : set P) [finite_dimensional 𝕜 V] :
intrinsic_closure 𝕜 A = closure A :=
begin
  simp only [intrinsic_closure_def],
  ext x,
  simp only [mem_closure_iff, set.mem_image],
  split,
  { rintro ⟨x, h, rfl⟩ o ho hxo,
    obtain ⟨z, hz₁, hz₂⟩ := h ((coe : affine_span 𝕜 A → P) ⁻¹' o)
                   (continuous_induced_dom.is_open_preimage o ho) hxo,
    exact ⟨z, hz₁, hz₂⟩ },
  { intro h,
    refine ⟨⟨x, _⟩, _⟩,
    { by_contradiction hc,
      obtain ⟨z, hz₁, hz₂⟩ := h
        (affine_span 𝕜 A)ᶜ
        (affine_subspace.closed_of_finite_dimensional (affine_span 𝕜 A)).is_open_compl
        hc,
      exact hz₁ (subset_affine_span 𝕜 A hz₂) },
    refine ⟨_, subtype.coe_mk _ _⟩,
    intros o ho hxo,
    have ho' := ho,
    rw [is_open_induced_iff] at ho,
    obtain ⟨o, ho, rfl⟩ := ho,
    rw [set.mem_preimage, subtype.coe_mk] at hxo,
    obtain ⟨w, hwo, hwA⟩ := h _ ho hxo,
    have : w ∈ affine_span 𝕜 A := subset_affine_span 𝕜 A hwA,
    refine ⟨⟨w, subset_affine_span 𝕜 A hwA⟩, hwo, hwA⟩ },
end

@[simp] lemma closure_diff_intrinsic_interior {𝕜 : Type*}
  [nontrivially_normed_field 𝕜] [complete_space 𝕜]
  {V P : Type} [normed_add_comm_group V] [normed_space 𝕜 V] [finite_dimensional 𝕜 V]
  [metric_space P] [normed_add_torsor V P]
  (A : set P) :
closure A \ intrinsic_interior 𝕜 A = intrinsic_frontier 𝕜 A :=
(intrinsic_closure_eq_closure 𝕜 A) ▸ intrinsic_closure_diff_intrinsic_interior A

lemma nonempty_intrinsic_interior_of_nonempty_of_convex.aux {α β : Type*}
  [topological_space α] [topological_space β] (φ : α ≃ₜ β) (A : set β) :
(interior A).nonempty ↔ (interior (φ ⁻¹' A)).nonempty :=
begin
  rw [←φ.image_symm, ←φ.symm.image_interior, set.nonempty_image_iff],
end

lemma nonempty_intrinsic_interior_of_nonempty_of_convex.aux_2 {𝕜 V₁ P₁ V₂ P₂ : Type*}
  [normed_field 𝕜] [normed_add_comm_group V₁] [normed_add_comm_group V₂]
  [pseudo_metric_space P₁] [pseudo_metric_space P₂] [normed_space 𝕜 V₁] [normed_space 𝕜 V₂]
  [normed_add_torsor V₁ P₁] [normed_add_torsor V₂ P₂]
  (f : P₁ ≃ᵃⁱ[𝕜] P₂) (A : set P₂) :
affine_subspace.comap f.to_affine_equiv.to_affine_map (affine_span 𝕜 A) =
  affine_span 𝕜 (f ⁻¹' A) :=
f.to_affine_equiv.comap_span A

lemma nonempty_intrinsic_interior_of_nonempty_of_convex
  {V : Type*} [normed_add_comm_group V] [normed_space ℝ V] [finite_dimensional ℝ V]
  {A : set V} (Ane : A.nonempty) (Acv : convex ℝ A) :
(intrinsic_interior ℝ A).nonempty :=
begin
  haveI : nonempty A := set.nonempty_coe_sort.mpr Ane,
  rw [intrinsic_interior_def, set.nonempty_image_iff],
  obtain ⟨p, hp⟩ := Ane,
  let p' : affine_span ℝ A := ⟨p, subset_affine_span _ _ hp⟩,
  rw [nonempty_intrinsic_interior_of_nonempty_of_convex.aux
    (affine_isometry_equiv.const_vsub ℝ p').symm.to_homeomorph,
    convex.interior_nonempty_iff_affine_span_eq_top],
  { rw [affine_isometry_equiv.coe_to_homeomorph,
        ←nonempty_intrinsic_interior_of_nonempty_of_convex.aux_2
          (affine_isometry_equiv.const_vsub ℝ p').symm,
        affine_span_coe_preimage_eq_top A],
    exact affine_subspace.comap_top },
  { exact convex.affine_preimage (((affine_span ℝ A).subtype).comp
    (affine_isometry_equiv.const_vsub ℝ p').symm.to_affine_equiv.to_affine_map) Acv },
end
