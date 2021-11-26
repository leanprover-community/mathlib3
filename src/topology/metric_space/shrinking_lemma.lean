/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import topology.metric_space.basic
import topology.metric_space.emetric_paracompact
import topology.shrinking_lemma

/-!
# Shrinking lemma in a proper metric space

In this file we prove a few versions of the shrinking lemma for coverings by balls in a proper
(pseudo) metric space.

## Tags

shrinking lemma, metric space
-/

universes u v
open set metric
open_locale topological_space

variables {α : Type u} {ι : Type v} [metric_space α] [proper_space α] {c : ι → α}
variables {x : α} {r : ℝ} {s : set α}

/-- Shrinking lemma for coverings by open balls in a proper metric space. A point-finite open cover
of a closed subset of a proper metric space by open balls can be shrunk to a new cover by open balls
so that each of the new balls has strictly smaller radius than the old one. This version assumes
that `λ x, ball (c i) (r i)` is a locally finite covering and provides a covering indexed by the
same type. -/
lemma exists_subset_Union_ball_radius_lt {r : ι → ℝ} (hs : is_closed s)
  (uf : ∀ x ∈ s, finite {i | x ∈ ball (c i) (r i)}) (us : s ⊆ ⋃ i, ball (c i) (r i)) :
  ∃ r' : ι → ℝ, s ⊆ (⋃ i, ball (c i) (r' i)) ∧ ∀ i, r' i < r i :=
begin
  rcases exists_subset_Union_closed_subset hs (λ i, @is_open_ball _ _ (c i) (r i)) uf us
    with ⟨v, hsv, hvc, hcv⟩,
  have := λ i, exists_lt_subset_ball (hvc i) (hcv i),
  choose r' hlt hsub,
  exact ⟨r', subset.trans hsv $ Union_subset_Union $ hsub, hlt⟩
end

/-- Shrinking lemma for coverings by open balls in a proper metric space. A point-finite open cover
of a proper metric space by open balls can be shrunk to a new cover by open balls so that each of
the new balls has strictly smaller radius than the old one. -/
lemma exists_Union_ball_eq_radius_lt {r : ι → ℝ} (uf : ∀ x, finite {i | x ∈ ball (c i) (r i)})
  (uU : (⋃ i, ball (c i) (r i)) = univ) :
  ∃ r' : ι → ℝ, (⋃ i, ball (c i) (r' i)) = univ ∧ ∀ i, r' i < r i :=
let ⟨r', hU, hv⟩ := exists_subset_Union_ball_radius_lt is_closed_univ (λ x _, uf x) uU.ge
in ⟨r', univ_subset_iff.1 hU, hv⟩

/-- Shrinking lemma for coverings by open balls in a proper metric space. A point-finite open cover
of a closed subset of a proper metric space by nonempty open balls can be shrunk to a new cover by
nonempty open balls so that each of the new balls has strictly smaller radius than the old one. -/
lemma exists_subset_Union_ball_radius_pos_lt {r : ι → ℝ} (hr : ∀ i, 0 < r i) (hs : is_closed s)
  (uf : ∀ x ∈ s, finite {i | x ∈ ball (c i) (r i)}) (us : s ⊆ ⋃ i, ball (c i) (r i)) :
  ∃ r' : ι → ℝ, s ⊆ (⋃ i, ball (c i) (r' i)) ∧ ∀ i, r' i ∈ Ioo 0 (r i) :=
begin
  rcases exists_subset_Union_closed_subset hs (λ i, @is_open_ball _ _ (c i) (r i)) uf us
    with ⟨v, hsv, hvc, hcv⟩,
  have := λ i, exists_pos_lt_subset_ball (hr i) (hvc i) (hcv i),
  choose r' hlt hsub,
  exact ⟨r', subset.trans hsv $ Union_subset_Union hsub, hlt⟩
end

/-- Shrinking lemma for coverings by open balls in a proper metric space. A point-finite open cover
of a proper metric space by nonempty open balls can be shrunk to a new cover by nonempty open balls
so that each of the new balls has strictly smaller radius than the old one. -/
lemma exists_Union_ball_eq_radius_pos_lt {r : ι → ℝ} (hr : ∀ i, 0 < r i)
  (uf : ∀ x, finite {i | x ∈ ball (c i) (r i)}) (uU : (⋃ i, ball (c i) (r i)) = univ) :
  ∃ r' : ι → ℝ, (⋃ i, ball (c i) (r' i)) = univ ∧ ∀ i, r' i ∈ Ioo 0 (r i) :=
let ⟨r', hU, hv⟩ := exists_subset_Union_ball_radius_pos_lt hr is_closed_univ (λ x _, uf x) uU.ge
in ⟨r', univ_subset_iff.1 hU, hv⟩

/-- Let `R : α → ℝ` be a (possibly discontinuous) function on a proper metric space.
Let `s` be a closed set in `α` such that `R` is positive on `s`. Then there exists a collection of
pairs of balls `metric.ball (c i) (r i)`, `metric.ball (c i) (r' i)` such that

* all centers belong to `s`;
* for all `i` we have `0 < r i < r' i < R (c i)`;
* the family of balls `metric.ball (c i) (r' i)` is locally finite;
* the balls `metric.ball (c i) (r i)` cover `s`.

This is a simple corollary of `refinement_of_locally_compact_sigma_compact_of_nhds_basis_set`
and `exists_subset_Union_ball_radius_pos_lt`. -/
lemma exists_locally_finite_subset_Union_ball_radius_lt (hs : is_closed s)
  {R : α → ℝ} (hR : ∀ x ∈ s, 0 < R x) :
  ∃ (ι : Type u) (c : ι → α) (r r' : ι → ℝ),
    (∀ i, c i ∈ s ∧ 0 < r i ∧ r i < r' i ∧ r' i < R (c i)) ∧
    locally_finite (λ i, ball (c i) (r' i)) ∧ s ⊆ ⋃ i, ball (c i) (r i) :=
begin
  have : ∀ x ∈ s, (𝓝 x).has_basis (λ r : ℝ, 0 < r ∧ r < R x) (λ r, ball x r),
    from λ x hx, nhds_basis_uniformity (uniformity_basis_dist_lt (hR x hx)),
  rcases refinement_of_locally_compact_sigma_compact_of_nhds_basis_set hs this
    with ⟨ι, c, r', hr', hsub', hfin⟩,
  rcases exists_subset_Union_ball_radius_pos_lt (λ i, (hr' i).2.1) hs
    (λ x hx, hfin.point_finite x) hsub' with ⟨r, hsub, hlt⟩,
  exact ⟨ι, c, r, r', λ i, ⟨(hr' i).1, (hlt i).1, (hlt i).2, (hr' i).2.2⟩, hfin, hsub⟩
end

/-- Let `R : α → ℝ` be a (possibly discontinuous) positive function on a proper metric space. Then
there exists a collection of pairs of balls `metric.ball (c i) (r i)`, `metric.ball (c i) (r' i)`
such that

* for all `i` we have `0 < r i < r' i < R (c i)`;
* the family of balls `metric.ball (c i) (r' i)` is locally finite;
* the balls `metric.ball (c i) (r i)` cover the whole space.

This is a simple corollary of `refinement_of_locally_compact_sigma_compact_of_nhds_basis`
and `exists_Union_ball_eq_radius_pos_lt` or `exists_locally_finite_subset_Union_ball_radius_lt`. -/
lemma exists_locally_finite_Union_eq_ball_radius_lt {R : α → ℝ} (hR : ∀ x, 0 < R x) :
  ∃ (ι : Type u) (c : ι → α) (r r' : ι → ℝ), (∀ i, 0 < r i ∧ r i < r' i ∧ r' i < R (c i)) ∧
    locally_finite (λ i, ball (c i) (r' i)) ∧ (⋃ i, ball (c i) (r i)) = univ :=
let ⟨ι, c, r, r', hlt, hfin, hsub⟩ := exists_locally_finite_subset_Union_ball_radius_lt
  is_closed_univ (λ x _, hR x)
in ⟨ι, c, r, r', λ i, (hlt i).2, hfin, univ_subset_iff.1 hsub⟩
