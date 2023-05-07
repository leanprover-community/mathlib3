/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
import analysis.convex.jensen
import analysis.convex.topology
import analysis.normed.group.pointwise
import analysis.normed_space.ray

/-!
# Topological and metric properties of convex sets in normed spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We prove the following facts:

* `convex_on_norm`, `convex_on_dist` : norm and distance to a fixed point is convex on any convex
  set;
* `convex_on_univ_norm`, `convex_on_univ_dist` : norm and distance to a fixed point is convex on
  the whole space;
* `convex_hull_ediam`, `convex_hull_diam` : convex hull of a set has the same (e)metric diameter
  as the original set;
* `bounded_convex_hull` : convex hull of a set is bounded if and only if the original set
  is bounded.
* `bounded_std_simplex`, `is_closed_std_simplex`, `compact_std_simplex`: topological properties
  of the standard simplex.
-/

variables {ι : Type*} {E : Type*}

open metric set
open_locale pointwise convex

variables [seminormed_add_comm_group E] [normed_space ℝ E] {s t : set E}

/-- The norm on a real normed space is convex on any convex set. See also `seminorm.convex_on`
and `convex_on_univ_norm`. -/
lemma convex_on_norm (hs : convex ℝ s) : convex_on ℝ s norm :=
⟨hs, λ x hx y hy a b ha hb hab,
  calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ : norm_add_le _ _
    ... = a * ‖x‖ + b * ‖y‖
        : by rw [norm_smul, norm_smul, real.norm_of_nonneg ha, real.norm_of_nonneg hb]⟩

/-- The norm on a real normed space is convex on the whole space. See also `seminorm.convex_on`
and `convex_on_norm`. -/
lemma convex_on_univ_norm : convex_on ℝ univ (norm : E → ℝ) := convex_on_norm convex_univ

lemma convex_on_dist (z : E) (hs : convex ℝ s) : convex_on ℝ s (λ z', dist z' z) :=
by simpa [dist_eq_norm, preimage_preimage]
  using (convex_on_norm (hs.translate (-z))).comp_affine_map
    (affine_map.id ℝ E - affine_map.const ℝ E z)

lemma convex_on_univ_dist (z : E) : convex_on ℝ univ (λz', dist z' z) :=
convex_on_dist z convex_univ

lemma convex_ball (a : E) (r : ℝ) : convex ℝ (metric.ball a r) :=
by simpa only [metric.ball, sep_univ] using (convex_on_univ_dist a).convex_lt r

lemma convex_closed_ball (a : E) (r : ℝ) : convex ℝ (metric.closed_ball a r) :=
by simpa only [metric.closed_ball, sep_univ] using (convex_on_univ_dist a).convex_le r

lemma convex.thickening (hs : convex ℝ s) (δ : ℝ) : convex ℝ (thickening δ s) :=
by { rw ←add_ball_zero, exact hs.add (convex_ball 0 _) }

lemma convex.cthickening (hs : convex ℝ s) (δ : ℝ) : convex ℝ (cthickening δ s) :=
begin
  obtain hδ | hδ := le_total 0 δ,
  { rw cthickening_eq_Inter_thickening hδ,
    exact convex_Inter₂ (λ _ _, hs.thickening _) },
  { rw cthickening_of_nonpos hδ,
    exact hs.closure }
end

/-- Given a point `x` in the convex hull of `s` and a point `y`, there exists a point
of `s` at distance at least `dist x y` from `y`. -/
lemma convex_hull_exists_dist_ge {s : set E} {x : E} (hx : x ∈ convex_hull ℝ s) (y : E) :
  ∃ x' ∈ s, dist x y ≤ dist x' y :=
(convex_on_dist y (convex_convex_hull ℝ _)).exists_ge_of_mem_convex_hull hx

/-- Given a point `x` in the convex hull of `s` and a point `y` in the convex hull of `t`,
there exist points `x' ∈ s` and `y' ∈ t` at distance at least `dist x y`. -/
lemma convex_hull_exists_dist_ge2 {s t : set E} {x y : E}
  (hx : x ∈ convex_hull ℝ s) (hy : y ∈ convex_hull ℝ t) :
  ∃ (x' ∈ s) (y' ∈ t), dist x y ≤ dist x' y' :=
begin
  rcases convex_hull_exists_dist_ge hx y with ⟨x', hx', Hx'⟩,
  rcases convex_hull_exists_dist_ge hy x' with ⟨y', hy', Hy'⟩,
  use [x', hx', y', hy'],
  exact le_trans Hx' (dist_comm y x' ▸ dist_comm y' x' ▸ Hy')
end

/-- Emetric diameter of the convex hull of a set `s` equals the emetric diameter of `s. -/
@[simp] lemma convex_hull_ediam (s : set E) :
  emetric.diam (convex_hull ℝ s) = emetric.diam s :=
begin
  refine (emetric.diam_le $ λ x hx y hy, _).antisymm (emetric.diam_mono $ subset_convex_hull ℝ s),
  rcases convex_hull_exists_dist_ge2 hx hy with ⟨x', hx', y', hy', H⟩,
  rw edist_dist,
  apply le_trans (ennreal.of_real_le_of_real H),
  rw ← edist_dist,
  exact emetric.edist_le_diam_of_mem hx' hy'
end

/-- Diameter of the convex hull of a set `s` equals the emetric diameter of `s. -/
@[simp] lemma convex_hull_diam (s : set E) :
  metric.diam (convex_hull ℝ s) = metric.diam s :=
by simp only [metric.diam, convex_hull_ediam]

/-- Convex hull of `s` is bounded if and only if `s` is bounded. -/
@[simp] lemma bounded_convex_hull {s : set E} :
  metric.bounded (convex_hull ℝ s) ↔ metric.bounded s :=
by simp only [metric.bounded_iff_ediam_ne_top, convex_hull_ediam]

@[priority 100]
instance normed_space.path_connected : path_connected_space E :=
topological_add_group.path_connected

@[priority 100]
instance normed_space.loc_path_connected : loc_path_connected_space E :=
loc_path_connected_of_bases (λ x, metric.nhds_basis_ball)
  (λ x r r_pos, (convex_ball x r).is_path_connected $ by simp [r_pos])

lemma dist_add_dist_of_mem_segment {x y z : E} (h : y ∈ [x -[ℝ] z]) :
  dist x y + dist y z = dist x z :=
begin
  simp only [dist_eq_norm, mem_segment_iff_same_ray] at *,
  simpa only [sub_add_sub_cancel', norm_sub_rev] using h.norm_add.symm
end

/-- The set of vectors in the same ray as `x` is connected. -/
lemma is_connected_set_of_same_ray (x : E) : is_connected {y | same_ray ℝ x y} :=
begin
  by_cases hx : x = 0, { simpa [hx] using is_connected_univ },
  simp_rw ←exists_nonneg_left_iff_same_ray hx,
  exact is_connected_Ici.image _ ((continuous_id.smul continuous_const).continuous_on)
end

/-- The set of nonzero vectors in the same ray as the nonzero vector `x` is connected. -/
lemma is_connected_set_of_same_ray_and_ne_zero {x : E} (hx : x ≠ 0) :
  is_connected {y | same_ray ℝ x y ∧ y ≠ 0} :=
begin
  simp_rw ←exists_pos_left_iff_same_ray_and_ne_zero hx,
  exact is_connected_Ioi.image _ ((continuous_id.smul continuous_const).continuous_on)
end
