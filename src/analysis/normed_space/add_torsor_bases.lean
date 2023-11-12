/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import analysis.normed_space.finite_dimension
import analysis.calculus.affine_map
import analysis.convex.combination
import linear_algebra.affine_space.finite_dimensional

/-!
# Bases in normed affine spaces.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains results about bases in normed affine spaces.

## Main definitions:

 * `continuous_barycentric_coord`
 * `is_open_map_barycentric_coord`
 * `affine_basis.interior_convex_hull`
 * `exists_subset_affine_independent_span_eq_top_of_open`
 * `interior_convex_hull_nonempty_iff_affine_span_eq_top`
-/

section barycentric

variables {ι 𝕜 E P : Type*} [nontrivially_normed_field 𝕜] [complete_space 𝕜]
variables [normed_add_comm_group E] [normed_space 𝕜 E]
variables [metric_space P] [normed_add_torsor E P]

include E

lemma is_open_map_barycentric_coord [nontrivial ι] (b : affine_basis ι 𝕜 P) (i : ι) :
  is_open_map (b.coord i) :=
affine_map.is_open_map_linear_iff.mp $ (b.coord i).linear.is_open_map_of_finite_dimensional $
  (b.coord i).linear_surjective_iff.mpr (b.surjective_coord i)

variables [finite_dimensional 𝕜 E] (b : affine_basis ι 𝕜 P)

@[continuity]
lemma continuous_barycentric_coord (i : ι) : continuous (b.coord i) :=
(b.coord i).continuous_of_finite_dimensional

lemma smooth_barycentric_coord (b : affine_basis ι 𝕜 E) (i : ι) : cont_diff 𝕜 ⊤ (b.coord i) :=
(⟨b.coord i, continuous_barycentric_coord b i⟩ : E →A[𝕜] 𝕜).cont_diff

end barycentric

open set

/-- Given a finite-dimensional normed real vector space, the interior of the convex hull of an
affine basis is the set of points whose barycentric coordinates are strictly positive with respect
to this basis.

TODO Restate this result for affine spaces (instead of vector spaces) once the definition of
convexity is generalised to this setting. -/
lemma affine_basis.interior_convex_hull {ι E : Type*} [finite ι] [normed_add_comm_group E]
  [normed_space ℝ E] (b : affine_basis ι ℝ E) :
  interior (convex_hull ℝ (range b)) = {x | ∀ i, 0 < b.coord i x} :=
begin
  casesI subsingleton_or_nontrivial ι,
  { -- The zero-dimensional case.
    have : range b = univ,
      from affine_subspace.eq_univ_of_subsingleton_span_eq_top (subsingleton_range _) b.tot,
    simp [this] },
  { -- The positive-dimensional case.
    haveI : finite_dimensional ℝ E := b.finite_dimensional,
    have : convex_hull ℝ (range b) = ⋂ i, (b.coord i)⁻¹' Ici 0,
    { rw [b.convex_hull_eq_nonneg_coord, set_of_forall], refl },
    ext,
    simp only [this, interior_Inter, ← is_open_map.preimage_interior_eq_interior_preimage
      (is_open_map_barycentric_coord b _) (continuous_barycentric_coord b _),
      interior_Ici, mem_Inter, mem_set_of_eq, mem_Ioi, mem_preimage], },
end

variables {V P : Type*} [normed_add_comm_group V] [normed_space ℝ V] [metric_space P]
  [normed_add_torsor V P]
include V

open affine_map

/-- Given a set `s` of affine-independent points belonging to an open set `u`, we may extend `s` to
an affine basis, all of whose elements belong to `u`. -/
lemma is_open.exists_between_affine_independent_span_eq_top {s u : set P} (hu : is_open u)
  (hsu : s ⊆ u) (hne : s.nonempty) (h : affine_independent ℝ (coe : s → P)) :
  ∃ t : set P, s ⊆ t ∧ t ⊆ u ∧ affine_independent ℝ (coe : t → P) ∧ affine_span ℝ t = ⊤ :=
begin
  obtain ⟨q, hq⟩ := hne,
  obtain ⟨ε, ε0, hεu⟩ := metric.nhds_basis_closed_ball.mem_iff.1 (hu.mem_nhds $ hsu hq),
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_subset_affine_independent_affine_span_eq_top h,
  let f : P → P := λ y, line_map q y (ε / dist y q),
  have hf : ∀ y, f y ∈ u,
  { refine λ y, hεu _,
    simp only [f],
    rw [metric.mem_closed_ball, line_map_apply, dist_vadd_left, norm_smul, real.norm_eq_abs,
      dist_eq_norm_vsub V y q, abs_div, abs_of_pos ε0, abs_of_nonneg (norm_nonneg _), div_mul_comm],
    exact mul_le_of_le_one_left ε0.le (div_self_le_one _) },
  have hεyq : ∀ y ∉ s, ε / dist y q ≠ 0,
    from λ y hy, div_ne_zero ε0.ne' (dist_ne_zero.2 (ne_of_mem_of_not_mem hq hy).symm),
  classical,
  let w : t → ℝˣ := λ p, if hp : (p : P) ∈ s then 1 else units.mk0 _ (hεyq ↑p hp),
  refine ⟨set.range (λ (p : t), line_map q p (w p : ℝ)), _, _, _, _⟩,
  { intros p hp, use ⟨p, ht₁ hp⟩, simp [w, hp], },
  { rintros y ⟨⟨p, hp⟩, rfl⟩,
    by_cases hps : p ∈ s; simp only [w, hps, line_map_apply_one, units.coe_mk0, dif_neg, dif_pos,
      not_false_iff, units.coe_one, subtype.coe_mk];
      [exact hsu hps, exact hf p], },
  { exact (ht₂.units_line_map ⟨q, ht₁ hq⟩ w).range, },
  { rw [affine_span_eq_affine_span_line_map_units (ht₁ hq) w, ht₃], },
end

lemma is_open.exists_subset_affine_independent_span_eq_top {u : set P} (hu : is_open u)
  (hne : u.nonempty) :
  ∃ s ⊆ u, affine_independent ℝ (coe : s → P) ∧ affine_span ℝ s = ⊤ :=
begin
  rcases hne with ⟨x, hx⟩,
  rcases hu.exists_between_affine_independent_span_eq_top (singleton_subset_iff.mpr hx)
    (singleton_nonempty _) (affine_independent_of_subsingleton _ _) with ⟨s, -, hsu, hs⟩,
  exact ⟨s, hsu, hs⟩
end

/-- The affine span of a nonempty open set is `⊤`. -/
lemma is_open.affine_span_eq_top {u : set P} (hu : is_open u) (hne : u.nonempty) :
  affine_span ℝ u = ⊤ :=
let ⟨s, hsu, hs, hs'⟩ := hu.exists_subset_affine_independent_span_eq_top hne
in top_unique $ hs' ▸ affine_span_mono _ hsu

lemma affine_span_eq_top_of_nonempty_interior {s : set V}
  (hs : (interior $ convex_hull ℝ s).nonempty) :
  affine_span ℝ s = ⊤ :=
top_unique $ is_open_interior.affine_span_eq_top hs ▸
  (affine_span_mono _ interior_subset).trans_eq (affine_span_convex_hull _)

lemma affine_basis.centroid_mem_interior_convex_hull {ι} [fintype ι] (b : affine_basis ι ℝ V) :
  finset.univ.centroid ℝ b ∈ interior (convex_hull ℝ (range b)) :=
begin
  haveI := b.nonempty,
  simp only [b.interior_convex_hull, mem_set_of_eq, b.coord_apply_centroid (finset.mem_univ _),
    inv_pos, nat.cast_pos, finset.card_pos, finset.univ_nonempty, forall_true_iff]
end

lemma interior_convex_hull_nonempty_iff_affine_span_eq_top [finite_dimensional ℝ V] {s : set V} :
  (interior (convex_hull ℝ s)).nonempty ↔ affine_span ℝ s = ⊤ :=
begin
  refine ⟨affine_span_eq_top_of_nonempty_interior, λ h, _⟩,
  obtain ⟨t, hts, b, hb⟩ := affine_basis.exists_affine_subbasis h,
  suffices : (interior (convex_hull ℝ (range b))).nonempty,
  { rw [hb, subtype.range_coe_subtype, set_of_mem_eq] at this,
    refine this.mono _,
    mono* },
  lift t to finset V using b.finite_set,
  exact ⟨_, b.centroid_mem_interior_convex_hull⟩
end

lemma convex.interior_nonempty_iff_affine_span_eq_top [finite_dimensional ℝ V] {s : set V}
  (hs : convex ℝ s) : (interior s).nonempty ↔ affine_span ℝ s = ⊤ :=
by rw [← interior_convex_hull_nonempty_iff_affine_span_eq_top, hs.convex_hull_eq]
