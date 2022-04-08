/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
import analysis.normed_space.basic
import analysis.normed.group.add_torsor
import linear_algebra.affine_space.midpoint
import topology.instances.real_vector_space

/-!
# Torsors of normed space actions.

This file contains lemmas about normed additive torsors over normed spaces.
-/

noncomputable theory
open_locale nnreal topological_space
open filter

variables {α V P : Type*} [semi_normed_group V] [pseudo_metric_space P] [normed_add_torsor V P]
variables {W Q : Type*} [normed_group W] [metric_space Q] [normed_add_torsor W Q]

include V

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 V]

open affine_map

@[simp] lemma dist_center_homothety (p₁ p₂ : P) (c : 𝕜) :
  dist p₁ (homothety p₁ c p₂) = ∥c∥ * dist p₁ p₂ :=
by simp [homothety_def, norm_smul, ← dist_eq_norm_vsub, dist_comm]

@[simp] lemma dist_homothety_center (p₁ p₂ : P) (c : 𝕜) :
  dist (homothety p₁ c p₂) p₁ = ∥c∥ * dist p₁ p₂ :=
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
  dist (line_map p₁ p₂ c) p₁ = ∥c∥ * dist p₁ p₂ :=
by simpa only [line_map_apply_zero, dist_zero_right] using dist_line_map_line_map p₁ p₂ c 0

@[simp] lemma dist_left_line_map (p₁ p₂ : P) (c : 𝕜) :
  dist p₁ (line_map p₁ p₂ c) = ∥c∥ * dist p₁ p₂ :=
(dist_comm _ _).trans (dist_line_map_left _ _ _)

@[simp] lemma dist_line_map_right (p₁ p₂ : P) (c : 𝕜) :
  dist (line_map p₁ p₂ c) p₂ = ∥1 - c∥ * dist p₁ p₂ :=
by simpa only [line_map_apply_one, dist_eq_norm'] using dist_line_map_line_map p₁ p₂ c 1

@[simp] lemma dist_right_line_map (p₁ p₂ : P) (c : 𝕜) :
  dist p₂ (line_map p₁ p₂ c) = ∥1 - c∥ * dist p₁ p₂ :=
(dist_comm _ _).trans (dist_line_map_right _ _ _)

@[simp] lemma dist_homothety_self (p₁ p₂ : P) (c : 𝕜) :
  dist (homothety p₁ c p₂) p₂ = ∥1 - c∥ * dist p₁ p₂ :=
by rw [homothety_eq_line_map, dist_line_map_right]

@[simp] lemma dist_self_homothety (p₁ p₂ : P) (c : 𝕜) :
  dist p₂ (homothety p₁ c p₂) = ∥1 - c∥ * dist p₁ p₂ :=
by rw [dist_comm, dist_homothety_self]

variables [invertible (2:𝕜)]

@[simp] lemma dist_left_midpoint (p₁ p₂ : P) :
  dist p₁ (midpoint 𝕜 p₁ p₂) = ∥(2:𝕜)∥⁻¹ * dist p₁ p₂ :=
by rw [midpoint, dist_comm, dist_line_map_left, inv_of_eq_inv, ← norm_inv]

@[simp] lemma dist_midpoint_left (p₁ p₂ : P) :
  dist (midpoint 𝕜 p₁ p₂) p₁ = ∥(2:𝕜)∥⁻¹ * dist p₁ p₂ :=
by rw [dist_comm, dist_left_midpoint]

@[simp] lemma dist_midpoint_right (p₁ p₂ : P) :
  dist (midpoint 𝕜 p₁ p₂) p₂ = ∥(2:𝕜)∥⁻¹ * dist p₁ p₂ :=
by rw [midpoint_comm, dist_midpoint_left, dist_comm]

@[simp] lemma dist_right_midpoint (p₁ p₂ : P) :
  dist p₂ (midpoint 𝕜 p₁ p₂) = ∥(2:𝕜)∥⁻¹ * dist p₁ p₂ :=
by rw [dist_comm, dist_midpoint_right]

lemma dist_midpoint_midpoint_le' (p₁ p₂ p₃ p₄ : P) :
  dist (midpoint 𝕜 p₁ p₂) (midpoint 𝕜 p₃ p₄) ≤ (dist p₁ p₃ + dist p₂ p₄) / ∥(2 : 𝕜)∥ :=
begin
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, midpoint_vsub_midpoint];
    try { apply_instance },
  rw [midpoint_eq_smul_add, norm_smul, inv_of_eq_inv, norm_inv, ← div_eq_inv_mul],
  exact div_le_div_of_le_of_nonneg (norm_add_le _ _) (norm_nonneg _),
end

end normed_space

variables [normed_space ℝ V] [normed_space ℝ W]

lemma dist_midpoint_midpoint_le (p₁ p₂ p₃ p₄ : V) :
  dist (midpoint ℝ p₁ p₂) (midpoint ℝ p₃ p₄) ≤ (dist p₁ p₃ + dist p₂ p₄) / 2 :=
by simpa using dist_midpoint_midpoint_le' p₁ p₂ p₃ p₄

include W

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
