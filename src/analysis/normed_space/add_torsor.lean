/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
import analysis.normed_space.basic
import analysis.normed.group.add_torsor
import linear_algebra.affine_space.midpoint_zero
import linear_algebra.affine_space.affine_subspace
import topology.instances.real_vector_space

/-!
# Torsors of normed space actions.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains lemmas about normed additive torsors over normed spaces.
-/

noncomputable theory
open_locale nnreal topology
open filter

variables {α V P W Q : Type*} [seminormed_add_comm_group V] [pseudo_metric_space P]
  [normed_add_torsor V P] [normed_add_comm_group W] [metric_space Q] [normed_add_torsor W Q]

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 V] [normed_space 𝕜 W]

open affine_map

lemma affine_subspace.is_closed_direction_iff (s : affine_subspace 𝕜 Q) :
  is_closed (s.direction : set W) ↔ is_closed (s : set Q) :=
begin
  rcases s.eq_bot_or_nonempty with rfl|⟨x, hx⟩, { simp [is_closed_singleton] },
  rw [← (isometry_equiv.vadd_const x).to_homeomorph.symm.is_closed_image,
    affine_subspace.coe_direction_eq_vsub_set_right hx],
  refl
end

include V

@[simp] lemma dist_center_homothety (p₁ p₂ : P) (c : 𝕜) :
  dist p₁ (homothety p₁ c p₂) = ‖c‖ * dist p₁ p₂ :=
by simp [homothety_def, norm_smul, ← dist_eq_norm_vsub, dist_comm]

@[simp] lemma dist_homothety_center (p₁ p₂ : P) (c : 𝕜) :
  dist (homothety p₁ c p₂) p₁ = ‖c‖ * dist p₁ p₂ :=
by rw [dist_comm, dist_center_homothety]

@[simp] lemma dist_line_map_line_map (p₁ p₂ : P) (c₁ c₂ : 𝕜) :
  dist (line_map p₁ p₂ c₁) (line_map p₁ p₂ c₂) = dist c₁ c₂ * dist p₁ p₂ :=
begin
  rw dist_comm p₁ p₂,
  simp only [line_map_apply, dist_eq_norm_vsub, vadd_vsub_vadd_cancel_right, ← sub_smul, norm_smul,
    vsub_eq_sub],
end

lemma lipschitz_with_line_map (p₁ p₂ : P) :
  lipschitz_with (nndist p₁ p₂) (line_map p₁ p₂ : 𝕜 → P) :=
lipschitz_with.of_dist_le_mul $ λ c₁ c₂,
  ((dist_line_map_line_map p₁ p₂ c₁ c₂).trans (mul_comm _ _)).le

@[simp] lemma dist_line_map_left (p₁ p₂ : P) (c : 𝕜) :
  dist (line_map p₁ p₂ c) p₁ = ‖c‖ * dist p₁ p₂ :=
by simpa only [line_map_apply_zero, dist_zero_right] using dist_line_map_line_map p₁ p₂ c 0

@[simp] lemma dist_left_line_map (p₁ p₂ : P) (c : 𝕜) :
  dist p₁ (line_map p₁ p₂ c) = ‖c‖ * dist p₁ p₂ :=
(dist_comm _ _).trans (dist_line_map_left _ _ _)

@[simp] lemma dist_line_map_right (p₁ p₂ : P) (c : 𝕜) :
  dist (line_map p₁ p₂ c) p₂ = ‖1 - c‖ * dist p₁ p₂ :=
by simpa only [line_map_apply_one, dist_eq_norm'] using dist_line_map_line_map p₁ p₂ c 1

@[simp] lemma dist_right_line_map (p₁ p₂ : P) (c : 𝕜) :
  dist p₂ (line_map p₁ p₂ c) = ‖1 - c‖ * dist p₁ p₂ :=
(dist_comm _ _).trans (dist_line_map_right _ _ _)

@[simp] lemma dist_homothety_self (p₁ p₂ : P) (c : 𝕜) :
  dist (homothety p₁ c p₂) p₂ = ‖1 - c‖ * dist p₁ p₂ :=
by rw [homothety_eq_line_map, dist_line_map_right]

@[simp] lemma dist_self_homothety (p₁ p₂ : P) (c : 𝕜) :
  dist p₂ (homothety p₁ c p₂) = ‖1 - c‖ * dist p₁ p₂ :=
by rw [dist_comm, dist_homothety_self]

section invertible_two

variables [invertible (2:𝕜)]

@[simp] lemma dist_left_midpoint (p₁ p₂ : P) :
  dist p₁ (midpoint 𝕜 p₁ p₂) = ‖(2:𝕜)‖⁻¹ * dist p₁ p₂ :=
by rw [midpoint, dist_comm, dist_line_map_left, inv_of_eq_inv, ← norm_inv]

@[simp] lemma dist_midpoint_left (p₁ p₂ : P) :
  dist (midpoint 𝕜 p₁ p₂) p₁ = ‖(2:𝕜)‖⁻¹ * dist p₁ p₂ :=
by rw [dist_comm, dist_left_midpoint]

@[simp] lemma dist_midpoint_right (p₁ p₂ : P) :
  dist (midpoint 𝕜 p₁ p₂) p₂ = ‖(2:𝕜)‖⁻¹ * dist p₁ p₂ :=
by rw [midpoint_comm, dist_midpoint_left, dist_comm]

@[simp] lemma dist_right_midpoint (p₁ p₂ : P) :
  dist p₂ (midpoint 𝕜 p₁ p₂) = ‖(2:𝕜)‖⁻¹ * dist p₁ p₂ :=
by rw [dist_comm, dist_midpoint_right]

lemma dist_midpoint_midpoint_le' (p₁ p₂ p₃ p₄ : P) :
  dist (midpoint 𝕜 p₁ p₂) (midpoint 𝕜 p₃ p₄) ≤ (dist p₁ p₃ + dist p₂ p₄) / ‖(2 : 𝕜)‖ :=
begin
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, midpoint_vsub_midpoint];
    try { apply_instance },
  rw [midpoint_eq_smul_add, norm_smul, inv_of_eq_inv, norm_inv, ← div_eq_inv_mul],
  exact div_le_div_of_le_of_nonneg (norm_add_le _ _) (norm_nonneg _),
end

end invertible_two

omit V
include W

lemma antilipschitz_with_line_map {p₁ p₂ : Q} (h : p₁ ≠ p₂) :
  antilipschitz_with (nndist p₁ p₂)⁻¹ (line_map p₁ p₂ : 𝕜 → Q) :=
antilipschitz_with.of_le_mul_dist $ λ c₁ c₂, by rw [dist_line_map_line_map, nnreal.coe_inv,
  ← dist_nndist, mul_left_comm, inv_mul_cancel (dist_ne_zero.2 h), mul_one]

variables (𝕜)

lemma eventually_homothety_mem_of_mem_interior (x : Q) {s : set Q} {y : Q} (hy : y ∈ interior s) :
  ∀ᶠ δ in 𝓝 (1 : 𝕜), homothety x δ y ∈ s :=
begin
  rw (normed_add_comm_group.nhds_basis_norm_lt (1 : 𝕜)).eventually_iff,
  cases eq_or_ne y x with h h, { use 1, simp [h.symm, interior_subset hy], },
  have hxy : 0 < ‖y -ᵥ x‖, { rwa [norm_pos_iff, vsub_ne_zero], },
  obtain ⟨u, hu₁, hu₂, hu₃⟩ := mem_interior.mp hy,
  obtain ⟨ε, hε, hyε⟩ := metric.is_open_iff.mp hu₂ y hu₃,
  refine ⟨ε / ‖y -ᵥ x‖, div_pos hε hxy, λ δ (hδ : ‖δ - 1‖ < ε / ‖y -ᵥ x‖), hu₁ (hyε _)⟩,
  rw [lt_div_iff hxy, ← norm_smul, sub_smul, one_smul] at hδ,
  rwa [homothety_apply, metric.mem_ball, dist_eq_norm_vsub W, vadd_vsub_eq_sub_vsub],
end

lemma eventually_homothety_image_subset_of_finite_subset_interior
  (x : Q) {s : set Q} {t : set Q} (ht : t.finite) (h : t ⊆ interior s) :
  ∀ᶠ δ in 𝓝 (1 : 𝕜), homothety x δ '' t ⊆ s :=
begin
  suffices : ∀ y ∈ t, ∀ᶠ δ in 𝓝 (1 : 𝕜), homothety x δ y ∈ s,
  { simp_rw set.image_subset_iff,
    exact (filter.eventually_all_finite ht).mpr this, },
  intros y hy,
  exact eventually_homothety_mem_of_mem_interior 𝕜 x (h hy),
end

end normed_space

variables [normed_space ℝ V] [normed_space ℝ W]

lemma dist_midpoint_midpoint_le (p₁ p₂ p₃ p₄ : V) :
  dist (midpoint ℝ p₁ p₂) (midpoint ℝ p₃ p₄) ≤ (dist p₁ p₃ + dist p₂ p₄) / 2 :=
by simpa using dist_midpoint_midpoint_le' p₁ p₂ p₃ p₄

include V W

/-- A continuous map between two normed affine spaces is an affine map provided that
it sends midpoints to midpoints. -/
def affine_map.of_map_midpoint (f : P → Q)
  (h : ∀ x y, f (midpoint ℝ x y) = midpoint ℝ (f x) (f y))
  (hfc : continuous f) :
  P →ᵃ[ℝ] Q :=
affine_map.mk' f
  ↑((add_monoid_hom.of_map_midpoint ℝ ℝ
    ((affine_equiv.vadd_const ℝ (f $ classical.arbitrary P)).symm ∘ f ∘
      (affine_equiv.vadd_const ℝ (classical.arbitrary P))) (by simp)
      (λ x y, by simp [h])).to_real_linear_map $ by apply_rules [continuous.vadd, continuous.vsub,
        continuous_const, hfc.comp, continuous_id])
  (classical.arbitrary P)
  (λ p, by simp)
