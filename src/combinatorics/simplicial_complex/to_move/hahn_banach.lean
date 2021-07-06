/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.module.linear_map
import analysis.convex.topology
import analysis.normed_space.operator_norm
import linear_algebra.affine_space.finite_dimensional

open_locale classical affine big_operators
open set
--TODO: Generalise to LCTVS
variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B C : set E}
  {X : finset E}

theorem geometric_hahn_banach_compact_closed {A B : set E}
  (hA₁ : convex A) (hA₂ : is_compact A)
  (hB₁ : convex B) (hB₂ : is_closed B)
  (disj : disjoint A B) :
  ∃ (f : E →L[ℝ] ℝ) (s t : ℝ), s < t ∧ (∀ b ∈ B, f b < s) ∧ (∀ a ∈ A, t < f a) :=
sorry

theorem geometric_hahn_banach_closed_point {A : set E} {x : E}
  (hA₁ : convex A) (hA₂ : is_closed A)
  (disj : x ∉ A) :
  ∃ (f : E →L[ℝ] ℝ) (s : ℝ), (∀ a ∈ A, f a < s) ∧ s < f x := sorry

theorem geometric_hahn_banach_open_point {A : set E} {x : E}
  (hA₁ : convex A) (hA₂ : is_open A)
  (disj : x ∉ A) :
  ∃ (f : E →L[ℝ] ℝ), (∀ a ∈ A, f a < f x) := sorry

theorem geometric_hahn_banach_point_open {x : E} {B : set E}
  (hB₁ : convex B) (hB₂ : is_open B)
  (disj : x ∉ B) :
  ∃ (f : E →L[ℝ] ℝ), (∀ b ∈ B, f x < f b) :=
let ⟨f, hf⟩ := geometric_hahn_banach_open_point hB₁ hB₂ disj in ⟨-f, by simpa⟩

theorem geometric_hahn_banach_point_point {x y : E} (hxy : x ≠ y) :
  ∃ (f : E →L[ℝ] ℝ), f x < f y :=
sorry
