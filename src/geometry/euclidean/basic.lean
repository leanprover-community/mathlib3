/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
import analysis.convex.strict_convex_between
import analysis.inner_product_space.projection
import algebra.quadratic_discriminant

/-!
# Euclidean spaces

This file makes some definitions and proves very basic geometrical
results about real inner product spaces and Euclidean affine spaces.
Results about real inner product spaces that involve the norm and
inner product but not angles generally go in
`analysis.normed_space.inner_product`.  Results with longer
proofs or more geometrical content generally go in separate files.

## Main definitions

* `euclidean_geometry.orthogonal_projection` is the orthogonal
  projection of a point onto an affine subspace.

* `euclidean_geometry.reflection` is the reflection of a point in an
  affine subspace.

## Implementation notes

To declare `P` as the type of points in a Euclidean affine space with
`V` as the type of vectors, use `[inner_product_space ℝ V] [metric_space P]
[normed_add_torsor V P]`.  This works better with `out_param` to make
`V` implicit in most cases than having a separate type alias for
Euclidean affine spaces.

Rather than requiring Euclidean affine spaces to be finite-dimensional
(as in the definition on Wikipedia), this is specified only for those
theorems that need it.

## References

* https://en.wikipedia.org/wiki/Euclidean_space

-/

noncomputable theory
open_locale big_operators
open_locale classical
open_locale real_inner_product_space

namespace euclidean_geometry
/-!
### Geometrical results on Euclidean affine spaces

This section develops some geometrical definitions and results on
Euclidean affine spaces.
-/

variables {V : Type*} {P : Type*} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P]
include V

/-- The midpoint of the segment AB is the same distance from A as it is from B. -/
lemma dist_left_midpoint_eq_dist_right_midpoint (p1 p2 : P) :
  dist p1 (midpoint ℝ p1 p2) = dist p2 (midpoint ℝ p1 p2) :=
by rw [dist_left_midpoint p1 p2, dist_right_midpoint p1 p2]

/-- The inner product of two vectors given with `weighted_vsub`, in
terms of the pairwise distances. -/
lemma inner_weighted_vsub {ι₁ : Type*} {s₁ : finset ι₁} {w₁ : ι₁ → ℝ} (p₁ : ι₁ → P)
    (h₁ : ∑ i in s₁, w₁ i = 0) {ι₂ : Type*} {s₂ : finset ι₂} {w₂ : ι₂ → ℝ} (p₂ : ι₂ → P)
    (h₂ : ∑ i in s₂, w₂ i = 0) :
  ⟪s₁.weighted_vsub p₁ w₁, s₂.weighted_vsub p₂ w₂⟫ =
    (-∑ i₁ in s₁, ∑ i₂ in s₂,
      w₁ i₁ * w₂ i₂ * (dist (p₁ i₁) (p₂ i₂) * dist (p₁ i₁) (p₂ i₂))) / 2 :=
begin
  rw [finset.weighted_vsub_apply, finset.weighted_vsub_apply,
      inner_sum_smul_sum_smul_of_sum_eq_zero _ h₁ _ h₂],
  simp_rw [vsub_sub_vsub_cancel_right],
  rcongr i₁ i₂; rw dist_eq_norm_vsub V (p₁ i₁) (p₂ i₂)
end

/-- The distance between two points given with `affine_combination`,
in terms of the pairwise distances between the points in that
combination. -/
lemma dist_affine_combination {ι : Type*} {s : finset ι} {w₁ w₂ : ι → ℝ} (p : ι → P)
    (h₁ : ∑ i in s, w₁ i = 1) (h₂ : ∑ i in s, w₂ i = 1) :
  by have a₁ := s.affine_combination p w₁; have a₂ := s.affine_combination p w₂; exact
  dist a₁ a₂ * dist a₁ a₂ = (-∑ i₁ in s, ∑ i₂ in s,
      (w₁ - w₂) i₁ * (w₁ - w₂) i₂ * (dist (p i₁) (p i₂) * dist (p i₁) (p i₂))) / 2 :=
begin
  rw [dist_eq_norm_vsub V (s.affine_combination p w₁) (s.affine_combination p w₂),
      ←inner_self_eq_norm_mul_norm, finset.affine_combination_vsub],
  have h : ∑ i in s, (w₁ - w₂) i = 0,
  { simp_rw [pi.sub_apply, finset.sum_sub_distrib, h₁, h₂, sub_self] },
  exact inner_weighted_vsub p h p h
end

/-- Suppose that `c₁` is equidistant from `p₁` and `p₂`, and the same
applies to `c₂`.  Then the vector between `c₁` and `c₂` is orthogonal
to that between `p₁` and `p₂`.  (In two dimensions, this says that the
diagonals of a kite are orthogonal.) -/
lemma inner_vsub_vsub_of_dist_eq_of_dist_eq {c₁ c₂ p₁ p₂ : P} (hc₁ : dist p₁ c₁ = dist p₂ c₁)
  (hc₂ : dist p₁ c₂ = dist p₂ c₂) : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p₁⟫ = 0 :=
begin
  have h : ⟪(c₂ -ᵥ c₁) + (c₂ -ᵥ c₁), p₂ -ᵥ p₁⟫ = 0,
  { conv_lhs { congr, congr, rw ←vsub_sub_vsub_cancel_right c₂ c₁ p₁,
               skip, rw ←vsub_sub_vsub_cancel_right c₂ c₁ p₂ },
    rw [sub_add_sub_comm, inner_sub_left],
    conv_lhs { congr, rw ←vsub_sub_vsub_cancel_right p₂ p₁ c₂,
               skip, rw ←vsub_sub_vsub_cancel_right p₂ p₁ c₁ },
    rw [dist_comm p₁, dist_comm p₂, dist_eq_norm_vsub V _ p₁,
        dist_eq_norm_vsub V _ p₂, ←real_inner_add_sub_eq_zero_iff] at hc₁ hc₂,
    simp_rw [←neg_vsub_eq_vsub_rev c₁, ←neg_vsub_eq_vsub_rev c₂, sub_neg_eq_add,
             neg_add_eq_sub, hc₁, hc₂, sub_zero] },
  simpa [inner_add_left, ←mul_two, (by norm_num : (2 : ℝ) ≠ 0)] using h
end

/-- The squared distance between points on a line (expressed as a
multiple of a fixed vector added to a point) and another point,
expressed as a quadratic. -/
lemma dist_smul_vadd_sq (r : ℝ) (v : V) (p₁ p₂ : P) :
  dist (r • v +ᵥ p₁) p₂ * dist (r • v +ᵥ p₁) p₂ =
    ⟪v, v⟫ * r * r + 2 * ⟪v, p₁ -ᵥ p₂⟫ * r + ⟪p₁ -ᵥ p₂, p₁ -ᵥ p₂⟫ :=
begin
  rw [dist_eq_norm_vsub V _ p₂, ←real_inner_self_eq_norm_mul_norm, vadd_vsub_assoc,
    real_inner_add_add_self, real_inner_smul_left, real_inner_smul_left, real_inner_smul_right],
  ring
end

/-- The condition for two points on a line to be equidistant from
another point. -/
lemma dist_smul_vadd_eq_dist {v : V} (p₁ p₂ : P) (hv : v ≠ 0) (r : ℝ) :
  dist (r • v +ᵥ p₁) p₂ = dist p₁ p₂ ↔ (r = 0 ∨ r = -2 * ⟪v, p₁ -ᵥ p₂⟫ / ⟪v, v⟫) :=
begin
  conv_lhs { rw [←mul_self_inj_of_nonneg dist_nonneg dist_nonneg, dist_smul_vadd_sq,
                 ←sub_eq_zero, add_sub_assoc, dist_eq_norm_vsub V p₁ p₂,
                 ←real_inner_self_eq_norm_mul_norm, sub_self] },
  have hvi : ⟪v, v⟫ ≠ 0, by simpa using hv,
  have hd : discrim ⟪v, v⟫ (2 * ⟪v, p₁ -ᵥ p₂⟫) 0 =
    (2 * ⟪v, p₁ -ᵥ p₂⟫) * (2 * ⟪v, p₁ -ᵥ p₂⟫),
  { rw discrim, ring },
  rw [quadratic_eq_zero_iff hvi hd, add_left_neg, zero_div, neg_mul_eq_neg_mul,
      ←mul_sub_right_distrib, sub_eq_add_neg, ←mul_two, mul_assoc, mul_div_assoc,
      mul_div_mul_left, mul_div_assoc],
  norm_num
end

open affine_subspace finite_dimensional

/-- Distances `r₁` `r₂` of `p` from two different points `c₁` `c₂` determine at
most two points `p₁` `p₂` in a two-dimensional subspace containing those points
(two circles intersect in at most two points). -/
lemma eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two {s : affine_subspace ℝ P}
  [finite_dimensional ℝ s.direction] (hd : finrank ℝ s.direction = 2) {c₁ c₂ p₁ p₂ p : P}
  (hc₁s : c₁ ∈ s) (hc₂s : c₂ ∈ s) (hp₁s : p₁ ∈ s) (hp₂s : p₂ ∈ s) (hps : p ∈ s) {r₁ r₂ : ℝ}
  (hc : c₁ ≠ c₂) (hp : p₁ ≠ p₂) (hp₁c₁ : dist p₁ c₁ = r₁) (hp₂c₁ : dist p₂ c₁ = r₁)
  (hpc₁ : dist p c₁ = r₁) (hp₁c₂ : dist p₁ c₂ = r₂) (hp₂c₂ : dist p₂ c₂ = r₂)
  (hpc₂ : dist p c₂ = r₂) : p = p₁ ∨ p = p₂ :=
begin
  have ho : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p₁⟫ = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq (hp₁c₁.trans hp₂c₁.symm) (hp₁c₂.trans hp₂c₂.symm),
  have hop : ⟪c₂ -ᵥ c₁, p -ᵥ p₁⟫ = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq (hp₁c₁.trans hpc₁.symm) (hp₁c₂.trans hpc₂.symm),
  let b : fin 2 → V := ![c₂ -ᵥ c₁, p₂ -ᵥ p₁],
  have hb : linear_independent ℝ b,
  { refine linear_independent_of_ne_zero_of_inner_eq_zero _ _,
    { intro i,
      fin_cases i; simp [b, hc.symm, hp.symm], },
    { intros i j hij,
      fin_cases i; fin_cases j; try { exact false.elim (hij rfl) },
      { exact ho },
      { rw real_inner_comm, exact ho } } },
  have hbs : submodule.span ℝ (set.range b) = s.direction,
  { refine eq_of_le_of_finrank_eq _ _,
    { rw [submodule.span_le, set.range_subset_iff],
      intro i,
      fin_cases i,
      { exact vsub_mem_direction hc₂s hc₁s },
      { exact vsub_mem_direction hp₂s hp₁s } },
    { rw [finrank_span_eq_card hb, fintype.card_fin, hd] } },
  have hv : ∀ v ∈ s.direction, ∃ t₁ t₂ : ℝ, v = t₁ • (c₂ -ᵥ c₁) + t₂ • (p₂ -ᵥ p₁),
  { intros v hv,
    have hr : set.range b = {c₂ -ᵥ c₁, p₂ -ᵥ p₁},
    { have hu : (finset.univ : finset (fin 2)) = {0, 1}, by dec_trivial,
      rw [←fintype.coe_image_univ, hu],
      simp,
      refl },
    rw [←hbs, hr, submodule.mem_span_insert] at hv,
    rcases hv with ⟨t₁, v', hv', hv⟩,
    rw submodule.mem_span_singleton at hv',
    rcases hv' with ⟨t₂, rfl⟩,
    exact ⟨t₁, t₂, hv⟩ },
  rcases hv (p -ᵥ p₁) (vsub_mem_direction hps hp₁s) with ⟨t₁, t₂, hpt⟩,
  simp only [hpt, inner_add_right, inner_smul_right, ho, mul_zero, add_zero, mul_eq_zero,
             inner_self_eq_zero, vsub_eq_zero_iff_eq, hc.symm, or_false] at hop,
  rw [hop, zero_smul, zero_add, ←eq_vadd_iff_vsub_eq] at hpt,
  subst hpt,
  have hp' : (p₂ -ᵥ p₁ : V) ≠ 0, { simp [hp.symm] },
  have hp₂ : dist ((1 : ℝ) • (p₂ -ᵥ p₁) +ᵥ p₁) c₁ = r₁, { simp [hp₂c₁] },
  rw [←hp₁c₁, dist_smul_vadd_eq_dist _ _ hp'] at hpc₁ hp₂,
  simp only [one_ne_zero, false_or] at hp₂,
  rw hp₂.symm at hpc₁,
  cases hpc₁; simp [hpc₁]
end

/-- Distances `r₁` `r₂` of `p` from two different points `c₁` `c₂` determine at
most two points `p₁` `p₂` in two-dimensional space (two circles intersect in at
most two points). -/
lemma eq_of_dist_eq_of_dist_eq_of_finrank_eq_two [finite_dimensional ℝ V] (hd : finrank ℝ V = 2)
  {c₁ c₂ p₁ p₂ p : P} {r₁ r₂ : ℝ} (hc : c₁ ≠ c₂) (hp : p₁ ≠ p₂) (hp₁c₁ : dist p₁ c₁ = r₁)
  (hp₂c₁ : dist p₂ c₁ = r₁) (hpc₁ : dist p c₁ = r₁) (hp₁c₂ : dist p₁ c₂ = r₂)
  (hp₂c₂ : dist p₂ c₂ = r₂) (hpc₂ : dist p c₂ = r₂) : p = p₁ ∨ p = p₂ :=
begin
  have hd' : finrank ℝ (⊤ : affine_subspace ℝ P).direction = 2,
  { rw [direction_top, finrank_top],
    exact hd },
  exact eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two hd'
    (mem_top ℝ V _) (mem_top ℝ V _) (mem_top ℝ V _) (mem_top ℝ V _) (mem_top ℝ V _)
    hc hp hp₁c₁ hp₂c₁ hpc₁ hp₁c₂ hp₂c₂ hpc₂
end

variables {V}

/-- The orthogonal projection of a point onto a nonempty affine
subspace, whose direction is complete, as an unbundled function.  This
definition is only intended for use in setting up the bundled version
`orthogonal_projection` and should not be used once that is
defined. -/
def orthogonal_projection_fn (s : affine_subspace ℝ P) [nonempty s] [complete_space s.direction]
  (p : P) : P :=
classical.some $ inter_eq_singleton_of_nonempty_of_is_compl
  (nonempty_subtype.mp ‹_›)
  (mk'_nonempty p s.directionᗮ)
  begin
    rw direction_mk' p s.directionᗮ,
    exact submodule.is_compl_orthogonal_of_complete_space,
  end

/-- The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonal_projection_fn` of that
point onto the subspace.  This lemma is only intended for use in
setting up the bundled version and should not be used once that is
defined. -/
lemma inter_eq_singleton_orthogonal_projection_fn {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] (p : P) :
  (s : set P) ∩ (mk' p s.directionᗮ) = {orthogonal_projection_fn s p} :=
classical.some_spec $ inter_eq_singleton_of_nonempty_of_is_compl
  (nonempty_subtype.mp ‹_›)
  (mk'_nonempty p s.directionᗮ)
  begin
    rw direction_mk' p s.directionᗮ,
    exact submodule.is_compl_orthogonal_of_complete_space
  end

/-- The `orthogonal_projection_fn` lies in the given subspace.  This
lemma is only intended for use in setting up the bundled version and
should not be used once that is defined. -/
lemma orthogonal_projection_fn_mem {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] (p : P) : orthogonal_projection_fn s p ∈ s :=
begin
  rw [←mem_coe, ←set.singleton_subset_iff, ←inter_eq_singleton_orthogonal_projection_fn],
  exact set.inter_subset_left _ _
end

/-- The `orthogonal_projection_fn` lies in the orthogonal
subspace.  This lemma is only intended for use in setting up the
bundled version and should not be used once that is defined. -/
lemma orthogonal_projection_fn_mem_orthogonal {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] (p : P) :
  orthogonal_projection_fn s p ∈ mk' p s.directionᗮ :=
begin
  rw [←mem_coe, ←set.singleton_subset_iff, ←inter_eq_singleton_orthogonal_projection_fn],
  exact set.inter_subset_right _ _
end

/-- Subtracting `p` from its `orthogonal_projection_fn` produces a
result in the orthogonal direction.  This lemma is only intended for
use in setting up the bundled version and should not be used once that
is defined. -/
lemma orthogonal_projection_fn_vsub_mem_direction_orthogonal {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] (p : P) :
  orthogonal_projection_fn s p -ᵥ p ∈ s.directionᗮ :=
direction_mk' p s.directionᗮ ▸
  vsub_mem_direction (orthogonal_projection_fn_mem_orthogonal p) (self_mem_mk' _ _)

local attribute [instance] affine_subspace.to_add_torsor

/-- The orthogonal projection of a point onto a nonempty affine
subspace, whose direction is complete. The corresponding linear map
(mapping a vector to the difference between the projections of two
points whose difference is that vector) is the `orthogonal_projection`
for real inner product spaces, onto the direction of the affine
subspace being projected onto. -/
def orthogonal_projection (s : affine_subspace ℝ P) [nonempty s] [complete_space s.direction] :
  P →ᵃ[ℝ] s :=
{ to_fun := λ p, ⟨orthogonal_projection_fn s p, orthogonal_projection_fn_mem p⟩,
  linear := orthogonal_projection s.direction,
  map_vadd' := λ p v, begin
    have hs : ((orthogonal_projection s.direction) v : V) +ᵥ orthogonal_projection_fn s p ∈ s :=
      vadd_mem_of_mem_direction (orthogonal_projection s.direction v).2
                                (orthogonal_projection_fn_mem p),
    have ho : ((orthogonal_projection s.direction) v : V) +ᵥ orthogonal_projection_fn s p ∈
      mk' (v +ᵥ p) s.directionᗮ,
    { rw [←vsub_right_mem_direction_iff_mem (self_mem_mk' _ _) _, direction_mk',
          vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_comm, add_sub_assoc],
      refine submodule.add_mem _ (orthogonal_projection_fn_vsub_mem_direction_orthogonal p) _,
      rw submodule.mem_orthogonal',
      intros w hw,
      rw [←neg_sub, inner_neg_left, orthogonal_projection_inner_eq_zero _ w hw, neg_zero], },
    have hm : ((orthogonal_projection s.direction) v : V) +ᵥ orthogonal_projection_fn s p ∈
      ({orthogonal_projection_fn s (v +ᵥ p)} : set P),
    { rw ←inter_eq_singleton_orthogonal_projection_fn (v +ᵥ p),
      exact set.mem_inter hs ho },
    rw set.mem_singleton_iff at hm,
    ext,
    exact hm.symm
  end }

@[simp] lemma orthogonal_projection_fn_eq {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] (p : P) :
  orthogonal_projection_fn s p = orthogonal_projection s p :=
rfl

/-- The linear map corresponding to `orthogonal_projection`. -/
@[simp] lemma orthogonal_projection_linear {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] :
  (orthogonal_projection s).linear = _root_.orthogonal_projection s.direction :=
rfl

/-- The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonal_projection` of that point
onto the subspace. -/
lemma inter_eq_singleton_orthogonal_projection {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] (p : P) :
  (s : set P) ∩ (mk' p s.directionᗮ) = {orthogonal_projection s p} :=
begin
  rw ←orthogonal_projection_fn_eq,
  exact inter_eq_singleton_orthogonal_projection_fn p
end

/-- The `orthogonal_projection` lies in the given subspace. -/
lemma orthogonal_projection_mem {s : affine_subspace ℝ P} [nonempty s] [complete_space s.direction]
  (p : P) : ↑(orthogonal_projection s p) ∈ s :=
(orthogonal_projection s p).2

/-- The `orthogonal_projection` lies in the orthogonal subspace. -/
lemma orthogonal_projection_mem_orthogonal (s : affine_subspace ℝ P) [nonempty s]
  [complete_space s.direction] (p : P) :
  ↑(orthogonal_projection s p) ∈ mk' p s.directionᗮ :=
orthogonal_projection_fn_mem_orthogonal p

/-- Subtracting a point in the given subspace from the
`orthogonal_projection` produces a result in the direction of the
given subspace. -/
lemma orthogonal_projection_vsub_mem_direction {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {p1 : P} (p2 : P) (hp1 : p1 ∈ s) :
  ↑(orthogonal_projection s p2 -ᵥ ⟨p1, hp1⟩ : s.direction) ∈ s.direction :=
(orthogonal_projection s p2 -ᵥ ⟨p1, hp1⟩ : s.direction).2

/-- Subtracting the `orthogonal_projection` from a point in the given
subspace produces a result in the direction of the given subspace. -/
lemma vsub_orthogonal_projection_mem_direction {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {p1 : P} (p2 : P) (hp1 : p1 ∈ s) :
  ↑((⟨p1, hp1⟩ : s) -ᵥ orthogonal_projection s p2 : s.direction) ∈ s.direction :=
((⟨p1, hp1⟩ : s) -ᵥ orthogonal_projection s p2 : s.direction).2

/-- A point equals its orthogonal projection if and only if it lies in
the subspace. -/
lemma orthogonal_projection_eq_self_iff {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {p : P} :
  ↑(orthogonal_projection s p) = p ↔ p ∈ s :=
begin
  split,
  { exact λ h, h ▸ orthogonal_projection_mem p },
  { intro h,
    have hp : p ∈ ((s : set P) ∩ mk' p s.directionᗮ) := ⟨h, self_mem_mk' p _⟩,
    rw [inter_eq_singleton_orthogonal_projection p] at hp,
    symmetry,
    exact hp }
end

@[simp] lemma orthogonal_projection_mem_subspace_eq_self {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] (p : s) :
  orthogonal_projection s p = p :=
begin
  ext,
  rw orthogonal_projection_eq_self_iff,
  exact p.2
end

/-- Orthogonal projection is idempotent. -/
@[simp] lemma orthogonal_projection_orthogonal_projection (s : affine_subspace ℝ P) [nonempty s]
  [complete_space s.direction] (p : P) :
  orthogonal_projection s (orthogonal_projection s p) = orthogonal_projection s p :=
begin
  ext,
  rw orthogonal_projection_eq_self_iff,
  exact orthogonal_projection_mem p,
end

lemma eq_orthogonal_projection_of_eq_subspace {s s' : affine_subspace ℝ P} [nonempty s]
  [nonempty s'] [complete_space s.direction] [complete_space s'.direction] (h : s = s') (p : P) :
  (orthogonal_projection s p : P) = (orthogonal_projection s' p : P) :=
begin
  change orthogonal_projection_fn s p = orthogonal_projection_fn s' p,
  congr,
  exact h
end

/-- The distance to a point's orthogonal projection is 0 iff it lies in the subspace. -/
lemma dist_orthogonal_projection_eq_zero_iff {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {p : P} :
  dist p (orthogonal_projection s p) = 0 ↔ p ∈ s :=
by rw [dist_comm, dist_eq_zero, orthogonal_projection_eq_self_iff]

/-- The distance between a point and its orthogonal projection is
nonzero if it does not lie in the subspace. -/
lemma dist_orthogonal_projection_ne_zero_of_not_mem {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {p : P} (hp : p ∉ s) :
  dist p (orthogonal_projection s p) ≠ 0 :=
mt dist_orthogonal_projection_eq_zero_iff.mp hp

/-- Subtracting `p` from its `orthogonal_projection` produces a result
in the orthogonal direction. -/
lemma orthogonal_projection_vsub_mem_direction_orthogonal (s : affine_subspace ℝ P) [nonempty s]
  [complete_space s.direction] (p : P) :
  (orthogonal_projection s p : P) -ᵥ p ∈ s.directionᗮ :=
orthogonal_projection_fn_vsub_mem_direction_orthogonal p

/-- Subtracting the `orthogonal_projection` from `p` produces a result
in the orthogonal direction. -/
lemma vsub_orthogonal_projection_mem_direction_orthogonal (s : affine_subspace ℝ P) [nonempty s]
  [complete_space s.direction] (p : P) :
  p -ᵥ orthogonal_projection s p ∈ s.directionᗮ :=
direction_mk' p s.directionᗮ ▸
  vsub_mem_direction (self_mem_mk' _ _) (orthogonal_projection_mem_orthogonal s p)

/-- Subtracting the `orthogonal_projection` from `p` produces a result in the kernel of the linear
part of the orthogonal projection. -/
lemma orthogonal_projection_vsub_orthogonal_projection (s : affine_subspace ℝ P) [nonempty s]
  [complete_space s.direction] (p : P) :
  _root_.orthogonal_projection s.direction (p -ᵥ orthogonal_projection s p) = 0 :=
begin
  apply orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero,
  intros c hc,
  rw [← neg_vsub_eq_vsub_rev, inner_neg_right,
    (orthogonal_projection_vsub_mem_direction_orthogonal s p c hc), neg_zero]
end

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector was
in the orthogonal direction. -/
lemma orthogonal_projection_vadd_eq_self {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {p : P} (hp : p ∈ s) {v : V}
  (hv : v ∈ s.directionᗮ) :
  orthogonal_projection s (v +ᵥ p) = ⟨p, hp⟩ :=
begin
  have h := vsub_orthogonal_projection_mem_direction_orthogonal s (v +ᵥ p),
  rw [vadd_vsub_assoc, submodule.add_mem_iff_right _ hv] at h,
  refine (eq_of_vsub_eq_zero _).symm,
  ext,
  refine submodule.disjoint_def.1 s.direction.orthogonal_disjoint _ _ h,
  exact (_ : s.direction).2
end

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector is a
multiple of the result of subtracting a point's orthogonal projection
from that point. -/
lemma orthogonal_projection_vadd_smul_vsub_orthogonal_projection {s : affine_subspace ℝ P}
  [nonempty s] [complete_space s.direction] {p1 : P} (p2 : P) (r : ℝ) (hp : p1 ∈ s) :
  orthogonal_projection s (r • (p2 -ᵥ orthogonal_projection s p2 : V) +ᵥ p1) = ⟨p1, hp⟩ :=
orthogonal_projection_vadd_eq_self hp
  (submodule.smul_mem _ _ (vsub_orthogonal_projection_mem_direction_orthogonal s _))

/-- The square of the distance from a point in `s` to `p2` equals the
sum of the squares of the distances of the two points to the
`orthogonal_projection`. -/
lemma dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq
  {s : affine_subspace ℝ P} [nonempty s] [complete_space s.direction] {p1 : P}
  (p2 : P) (hp1 : p1 ∈ s) :
  dist p1 p2 * dist p1 p2 =
    dist p1 (orthogonal_projection s p2) * dist p1 (orthogonal_projection s p2) +
    dist p2 (orthogonal_projection s p2) * dist p2 (orthogonal_projection s p2) :=
begin
  rw [dist_comm p2 _, dist_eq_norm_vsub V p1 _, dist_eq_norm_vsub V p1 _,
    dist_eq_norm_vsub V _ p2, ← vsub_add_vsub_cancel p1 (orthogonal_projection s p2) p2,
    norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero],
  exact submodule.inner_right_of_mem_orthogonal
    (vsub_orthogonal_projection_mem_direction p2 hp1)
    (orthogonal_projection_vsub_mem_direction_orthogonal s p2),
end

/-- The square of the distance between two points constructed by
adding multiples of the same orthogonal vector to points in the same
subspace. -/
lemma dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd {s : affine_subspace ℝ P}
    {p1 p2 : P} (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) (r1 r2 : ℝ) {v : V}
    (hv : v ∈ s.directionᗮ) :
  dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) * dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) =
    dist p1 p2 * dist p1 p2 + (r1 - r2) * (r1 - r2) * (‖v‖ * ‖v‖) :=
calc dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) * dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2)
    = ‖(p1 -ᵥ p2) + (r1 - r2) • v‖ * ‖(p1 -ᵥ p2) + (r1 - r2) • v‖
  : by rw [dist_eq_norm_vsub V (r1 • v +ᵥ p1), vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, sub_smul,
      add_comm, add_sub_assoc]
... = ‖p1 -ᵥ p2‖ * ‖p1 -ᵥ p2‖ + ‖(r1 - r2) • v‖ * ‖(r1 - r2) • v‖
  : norm_add_sq_eq_norm_sq_add_norm_sq_real
      (submodule.inner_right_of_mem_orthogonal (vsub_mem_direction hp1 hp2)
        (submodule.smul_mem _ _ hv))
... = ‖(p1 -ᵥ p2 : V)‖ * ‖(p1 -ᵥ p2 : V)‖ + |r1 - r2| * |r1 - r2| * ‖v‖ * ‖v‖
  : by { rw [norm_smul, real.norm_eq_abs], ring }
... = dist p1 p2 * dist p1 p2 + (r1 - r2) * (r1 - r2) * (‖v‖ * ‖v‖)
  : by { rw [dist_eq_norm_vsub V p1, abs_mul_abs_self, mul_assoc] }

/-- Reflection in an affine subspace, which is expected to be nonempty
and complete.  The word "reflection" is sometimes understood to mean
specifically reflection in a codimension-one subspace, and sometimes
more generally to cover operations such as reflection in a point.  The
definition here, of reflection in an affine subspace, is a more
general sense of the word that includes both those common cases. -/
def reflection (s : affine_subspace ℝ P) [nonempty s] [complete_space s.direction] :
  P ≃ᵃⁱ[ℝ] P :=
affine_isometry_equiv.mk'
  (λ p, (↑(orthogonal_projection s p) -ᵥ p) +ᵥ orthogonal_projection s p)
  (_root_.reflection s.direction)
  ↑(classical.arbitrary s)
  begin
    intros p,
    let v := p -ᵥ ↑(classical.arbitrary s),
    let a : V := _root_.orthogonal_projection s.direction v,
    let b : P := ↑(classical.arbitrary s),
    have key : a +ᵥ b -ᵥ (v +ᵥ b) +ᵥ (a +ᵥ b) = a + a - v +ᵥ (b -ᵥ b +ᵥ b),
    { rw [← add_vadd, vsub_vadd_eq_vsub_sub, vsub_vadd, vadd_vsub],
      congr' 1,
      abel },
    have : p = v +ᵥ ↑(classical.arbitrary s) := (vsub_vadd p ↑(classical.arbitrary s)).symm,
    simpa only [coe_vadd, reflection_apply, affine_map.map_vadd, orthogonal_projection_linear,
      orthogonal_projection_mem_subspace_eq_self, vadd_vsub, continuous_linear_map.coe_coe,
      continuous_linear_equiv.coe_coe, this] using key,
  end

/-- The result of reflecting. -/
lemma reflection_apply (s : affine_subspace ℝ P) [nonempty s] [complete_space s.direction] (p : P) :
  reflection s p = (↑(orthogonal_projection s p) -ᵥ p) +ᵥ orthogonal_projection s p :=
rfl

lemma eq_reflection_of_eq_subspace {s s' : affine_subspace ℝ P} [nonempty s]
  [nonempty s'] [complete_space s.direction] [complete_space s'.direction] (h : s = s') (p : P) :
  (reflection s p : P) = (reflection s' p : P) :=
by unfreezingI { subst h }

/-- Reflecting twice in the same subspace. -/
@[simp] lemma reflection_reflection (s : affine_subspace ℝ P) [nonempty s]
  [complete_space s.direction] (p : P) :
  reflection s (reflection s p) = p :=
begin
  have : ∀ a : s, ∀ b : V, (_root_.orthogonal_projection s.direction) b = 0
    → reflection s (reflection s (b +ᵥ a)) = b +ᵥ a,
  { intros a b h,
    have : (a:P) -ᵥ (b +ᵥ a) = - b,
    { rw [vsub_vadd_eq_vsub_sub, vsub_self, zero_sub] },
    simp [reflection, h, this] },
  rw ← vsub_vadd p (orthogonal_projection s p),
  exact this (orthogonal_projection s p) _ (orthogonal_projection_vsub_orthogonal_projection s p),
end

/-- Reflection is its own inverse. -/
@[simp] lemma reflection_symm (s : affine_subspace ℝ P) [nonempty s] [complete_space s.direction] :
  (reflection s).symm = reflection s :=
by { ext, rw ← (reflection s).injective.eq_iff, simp }

/-- Reflection is involutive. -/
lemma reflection_involutive (s : affine_subspace ℝ P) [nonempty s] [complete_space s.direction] :
  function.involutive (reflection s) :=
reflection_reflection s

/-- A point is its own reflection if and only if it is in the
subspace. -/
lemma reflection_eq_self_iff {s : affine_subspace ℝ P} [nonempty s] [complete_space s.direction]
  (p : P) : reflection s p = p ↔ p ∈ s :=
begin
  rw [←orthogonal_projection_eq_self_iff, reflection_apply],
  split,
  { intro h,
    rw [←@vsub_eq_zero_iff_eq V, vadd_vsub_assoc,
        ←two_smul ℝ (↑(orthogonal_projection s p) -ᵥ p), smul_eq_zero] at h,
    norm_num at h,
    exact h },
  { intro h,
    simp [h] }
end

/-- Reflecting a point in two subspaces produces the same result if
and only if the point has the same orthogonal projection in each of
those subspaces. -/
lemma reflection_eq_iff_orthogonal_projection_eq (s₁ s₂ : affine_subspace ℝ P)
  [nonempty s₁] [nonempty s₂] [complete_space s₁.direction] [complete_space s₂.direction] (p : P) :
  reflection s₁ p = reflection s₂ p ↔
    (orthogonal_projection s₁ p : P) = orthogonal_projection s₂ p :=
begin
  rw [reflection_apply, reflection_apply],
  split,
  { intro h,
    rw [←@vsub_eq_zero_iff_eq V, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_comm,
        add_sub_assoc, vsub_sub_vsub_cancel_right,
        ←two_smul ℝ ((orthogonal_projection s₁ p : P) -ᵥ orthogonal_projection s₂ p),
        smul_eq_zero] at h,
    norm_num at h,
    exact h },
  { intro h,
    rw h }
end

/-- The distance between `p₁` and the reflection of `p₂` equals that
between the reflection of `p₁` and `p₂`. -/
lemma dist_reflection (s : affine_subspace ℝ P) [nonempty s] [complete_space s.direction]
  (p₁ p₂ : P) :
  dist p₁ (reflection s p₂) = dist (reflection s p₁) p₂ :=
begin
  conv_lhs { rw ←reflection_reflection s p₁ },
  exact (reflection s).dist_map _ _
end

/-- A point in the subspace is equidistant from another point and its
reflection. -/
lemma dist_reflection_eq_of_mem (s : affine_subspace ℝ P) [nonempty s] [complete_space s.direction]
  {p₁ : P} (hp₁ : p₁ ∈ s) (p₂ : P) :
  dist p₁ (reflection s p₂) = dist p₁ p₂ :=
begin
  rw ←reflection_eq_self_iff p₁ at hp₁,
  convert (reflection s).dist_map p₁ p₂,
  rw hp₁
end

/-- The reflection of a point in a subspace is contained in any larger
subspace containing both the point and the subspace reflected in. -/
lemma reflection_mem_of_le_of_mem {s₁ s₂ : affine_subspace ℝ P} [nonempty s₁]
  [complete_space s₁.direction] (hle : s₁ ≤ s₂) {p : P}
  (hp : p ∈ s₂) : reflection s₁ p ∈ s₂ :=
begin
  rw [reflection_apply],
  have ho : ↑(orthogonal_projection s₁ p) ∈ s₂ := hle (orthogonal_projection_mem p),
  exact vadd_mem_of_mem_direction (vsub_mem_direction ho hp) ho
end

/-- Reflecting an orthogonal vector plus a point in the subspace
produces the negation of that vector plus the point. -/
lemma reflection_orthogonal_vadd {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {p : P} (hp : p ∈ s) {v : V}
  (hv : v ∈ s.directionᗮ) : reflection s (v +ᵥ p) = -v +ᵥ p :=
begin
  rw [reflection_apply, orthogonal_projection_vadd_eq_self hp hv, vsub_vadd_eq_vsub_sub],
  simp
end

/-- Reflecting a vector plus a point in the subspace produces the
negation of that vector plus the point if the vector is a multiple of
the result of subtracting a point's orthogonal projection from that
point. -/
lemma reflection_vadd_smul_vsub_orthogonal_projection {s : affine_subspace ℝ P} [nonempty s]
  [complete_space s.direction] {p₁ : P} (p₂ : P) (r : ℝ) (hp₁ : p₁ ∈ s) :
  reflection s (r • (p₂ -ᵥ orthogonal_projection s p₂) +ᵥ p₁) =
    -(r • (p₂ -ᵥ orthogonal_projection s p₂)) +ᵥ p₁ :=
reflection_orthogonal_vadd hp₁
  (submodule.smul_mem _ _ (vsub_orthogonal_projection_mem_direction_orthogonal s _))

omit V

variables (P)

/-- A `sphere P` bundles a `center` and `radius`. This definition does not require the radius to
be positive; that should be given as a hypothesis to lemmas that require it. -/
@[ext] structure sphere :=
(center : P)
(radius : ℝ)

variables {P}

instance [nonempty P] : nonempty (sphere P) := ⟨⟨classical.arbitrary P, 0⟩⟩

instance : has_coe (sphere P) (set P) := ⟨λ s, metric.sphere s.center s.radius⟩
instance : has_mem P (sphere P) := ⟨λ p s, p ∈ (s : set P)⟩

lemma sphere.mk_center (c : P) (r : ℝ) : (⟨c, r⟩ : sphere P).center = c := rfl

lemma sphere.mk_radius (c : P) (r : ℝ) : (⟨c, r⟩ : sphere P).radius = r := rfl

@[simp] lemma sphere.mk_center_radius (s : sphere P) : (⟨s.center, s.radius⟩ : sphere P) = s :=
by ext; refl

lemma sphere.coe_def (s : sphere P) : (s : set P) = metric.sphere s.center s.radius := rfl

@[simp] lemma sphere.coe_mk (c : P) (r : ℝ) : ↑(⟨c, r⟩ : sphere P) = metric.sphere c r := rfl

@[simp] lemma sphere.mem_coe {p : P} {s : sphere P} : p ∈ (s : set P) ↔ p ∈ s := iff.rfl

lemma mem_sphere {p : P} {s : sphere P} : p ∈ s ↔ dist p s.center = s.radius := iff.rfl

lemma mem_sphere' {p : P} {s : sphere P} : p ∈ s ↔ dist s.center p = s.radius :=
metric.mem_sphere'

lemma subset_sphere {ps : set P} {s : sphere P} : ps ⊆ s ↔ ∀ p ∈ ps, p ∈ s := iff.rfl

lemma dist_of_mem_subset_sphere {p : P} {ps : set P} {s : sphere P} (hp : p ∈ ps)
  (hps : ps ⊆ (s : set P)) : dist p s.center = s.radius :=
mem_sphere.1 (sphere.mem_coe.1 (set.mem_of_mem_of_subset hp hps))

lemma dist_of_mem_subset_mk_sphere {p c : P} {ps : set P} {r : ℝ} (hp : p ∈ ps)
  (hps : ps ⊆ ↑(⟨c, r⟩ : sphere P)) : dist p c = r :=
dist_of_mem_subset_sphere hp hps

lemma sphere.ne_iff {s₁ s₂ : sphere P} :
  s₁ ≠ s₂ ↔ s₁.center ≠ s₂.center ∨ s₁.radius ≠ s₂.radius :=
by rw [←not_and_distrib, ←sphere.ext_iff]

lemma sphere.center_eq_iff_eq_of_mem {s₁ s₂ : sphere P} {p : P} (hs₁ : p ∈ s₁) (hs₂ : p ∈ s₂) :
  s₁.center = s₂.center ↔ s₁ = s₂ :=
begin
  refine ⟨λ h, sphere.ext _ _ h _, λ h, h ▸ rfl⟩,
  rw mem_sphere at hs₁ hs₂,
  rw [←hs₁, ←hs₂, h]
end

lemma sphere.center_ne_iff_ne_of_mem {s₁ s₂ : sphere P} {p : P} (hs₁ : p ∈ s₁) (hs₂ : p ∈ s₂) :
  s₁.center ≠ s₂.center ↔ s₁ ≠ s₂ :=
(sphere.center_eq_iff_eq_of_mem hs₁ hs₂).not

lemma dist_center_eq_dist_center_of_mem_sphere {p₁ p₂ : P} {s : sphere P} (hp₁ : p₁ ∈ s)
  (hp₂ : p₂ ∈ s) : dist p₁ s.center = dist p₂ s.center :=
by rw [mem_sphere.1 hp₁, mem_sphere.1 hp₂]

lemma dist_center_eq_dist_center_of_mem_sphere' {p₁ p₂ : P} {s : sphere P} (hp₁ : p₁ ∈ s)
  (hp₂ : p₂ ∈ s) : dist s.center p₁ = dist s.center p₂ :=
by rw [mem_sphere'.1 hp₁, mem_sphere'.1 hp₂]

/-- A set of points is cospherical if they are equidistant from some
point.  In two dimensions, this is the same thing as being
concyclic. -/
def cospherical (ps : set P) : Prop :=
∃ (center : P) (radius : ℝ), ∀ p ∈ ps, dist p center = radius

/-- The definition of `cospherical`. -/
lemma cospherical_def (ps : set P) :
  cospherical ps ↔ ∃ (center : P) (radius : ℝ), ∀ p ∈ ps, dist p center = radius :=
iff.rfl

/-- A set of points is cospherical if and only if they lie in some sphere. -/
lemma cospherical_iff_exists_sphere {ps : set P} :
  cospherical ps ↔ ∃ s : sphere P, ps ⊆ (s : set P) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨c, r, h⟩,
    exact ⟨⟨c, r⟩, h⟩ },
  { rcases h with ⟨s, h⟩,
    exact ⟨s.center, s.radius, h⟩ }
end

/-- The set of points in a sphere is cospherical. -/
lemma sphere.cospherical (s : sphere P) : cospherical (s : set P) :=
cospherical_iff_exists_sphere.2 ⟨s, set.subset.rfl⟩

/-- A subset of a cospherical set is cospherical. -/
lemma cospherical.subset {ps₁ ps₂ : set P} (hs : ps₁ ⊆ ps₂) (hc : cospherical ps₂) :
  cospherical ps₁ :=
begin
  rcases hc with ⟨c, r, hcr⟩,
  exact ⟨c, r, λ p hp, hcr p (hs hp)⟩
end

include V

/-- The empty set is cospherical. -/
lemma cospherical_empty : cospherical (∅ : set P) :=
begin
  use add_torsor.nonempty.some,
  simp,
end

omit V

/-- A single point is cospherical. -/
lemma cospherical_singleton (p : P) : cospherical ({p} : set P) :=
begin
  use p,
  simp
end

include V

/-- Two points are cospherical. -/
lemma cospherical_pair (p₁ p₂ : P) : cospherical ({p₁, p₂} : set P) :=
begin
  use [(2⁻¹ : ℝ) • (p₂ -ᵥ p₁) +ᵥ p₁, (2⁻¹ : ℝ) * (dist p₂ p₁)],
  intro p,
  rw [set.mem_insert_iff, set.mem_singleton_iff],
  rintro ⟨_|_⟩,
  { rw [dist_eq_norm_vsub V p₁, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, norm_neg, norm_smul,
        dist_eq_norm_vsub V p₂],
    simp },
  { rw [H, dist_eq_norm_vsub V p₂, vsub_vadd_eq_vsub_sub, dist_eq_norm_vsub V p₂],
    conv_lhs { congr, congr, rw ←one_smul ℝ (p₂ -ᵥ p₁ : V) },
    rw [←sub_smul, norm_smul],
    norm_num }
end

/-- Any three points in a cospherical set are affinely independent. -/
lemma cospherical.affine_independent {s : set P} (hs : cospherical s) {p : fin 3 → P}
  (hps : set.range p ⊆ s) (hpi : function.injective p) :
  affine_independent ℝ p :=
begin
  rw affine_independent_iff_not_collinear,
  intro hc,
  rw collinear_iff_of_mem (set.mem_range_self (0 : fin 3)) at hc,
  rcases hc with ⟨v, hv⟩,
  rw set.forall_range_iff at hv,
  have hv0 : v ≠ 0,
  { intro h,
    have he : p 1 = p 0, by simpa [h] using hv 1,
    exact (dec_trivial : (1 : fin 3) ≠ 0) (hpi he) },
  rcases hs with ⟨c, r, hs⟩,
  have hs' := λ i, hs (p i) (set.mem_of_mem_of_subset (set.mem_range_self _) hps),
  choose f hf using hv,
  have hsd : ∀ i, dist ((f i • v) +ᵥ p 0) c = r,
  { intro i,
    rw ←hf,
    exact hs' i },
  have hf0 : f 0 = 0,
  { have hf0' := hf 0,
    rw [eq_comm, ←@vsub_eq_zero_iff_eq V, vadd_vsub, smul_eq_zero] at hf0',
    simpa [hv0] using hf0' },
  have hfi : function.injective f,
  { intros i j h,
    have hi := hf i,
    rw [h, ←hf j] at hi,
    exact hpi hi },
  simp_rw [←hsd 0, hf0, zero_smul, zero_vadd, dist_smul_vadd_eq_dist (p 0) c hv0] at hsd,
  have hfn0 : ∀ i, i ≠ 0 → f i ≠ 0 := λ i, (hfi.ne_iff' hf0).2,
  have hfn0' : ∀ i, i ≠ 0 → f i = (-2) * ⟪v, (p 0 -ᵥ c)⟫ / ⟪v, v⟫,
  { intros i hi,
    have hsdi := hsd i,
    simpa [hfn0, hi] using hsdi },
  have hf12 : f 1 = f 2, { rw [hfn0' 1 dec_trivial, hfn0' 2 dec_trivial] },
  exact (dec_trivial : (1 : fin 3) ≠ 2) (hfi hf12)
end

/-- Any three points in a cospherical set are affinely independent. -/
lemma cospherical.affine_independent_of_mem_of_ne {s : set P} (hs : cospherical s) {p₁ p₂ p₃ : P}
  (h₁ : p₁ ∈ s) (h₂ : p₂ ∈ s) (h₃ : p₃ ∈ s) (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃) :
  affine_independent ℝ ![p₁, p₂, p₃] :=
begin
  refine hs.affine_independent _ _,
  { simp [h₁, h₂, h₃, set.insert_subset] },
  { erw [fin.cons_injective_iff, fin.cons_injective_iff],
    simp [h₁₂, h₁₃, h₂₃, function.injective] }
end

/-- The three points of a cospherical set are affinely independent. -/
lemma cospherical.affine_independent_of_ne {p₁ p₂ p₃ : P} (hs : cospherical ({p₁, p₂, p₃} : set P))
  (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃) :
  affine_independent ℝ ![p₁, p₂, p₃] :=
hs.affine_independent_of_mem_of_ne (set.mem_insert _ _)
  (set.mem_insert_of_mem _ (set.mem_insert _ _))
  (set.mem_insert_of_mem _ (set.mem_insert_of_mem _ (set.mem_singleton _))) h₁₂ h₁₃ h₂₃

/-- Suppose that `p₁` and `p₂` lie in spheres `s₁` and `s₂`.  Then the vector between the centers
of those spheres is orthogonal to that between `p₁` and `p₂`; this is a version of
`inner_vsub_vsub_of_dist_eq_of_dist_eq` for bundled spheres.  (In two dimensions, this says that
the diagonals of a kite are orthogonal.) -/
lemma inner_vsub_vsub_of_mem_sphere_of_mem_sphere {p₁ p₂ : P} {s₁ s₂ : sphere P}
  (hp₁s₁ : p₁ ∈ s₁) (hp₂s₁ : p₂ ∈ s₁) (hp₁s₂ : p₁ ∈ s₂) (hp₂s₂ : p₂ ∈ s₂) :
  ⟪s₂.center -ᵥ s₁.center, p₂ -ᵥ p₁⟫ = 0 :=
inner_vsub_vsub_of_dist_eq_of_dist_eq (dist_center_eq_dist_center_of_mem_sphere hp₁s₁ hp₂s₁)
                                      (dist_center_eq_dist_center_of_mem_sphere hp₁s₂ hp₂s₂)

/-- Two spheres intersect in at most two points in a two-dimensional subspace containing their
centers; this is a version of `eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two` for bundled
spheres. -/
lemma eq_of_mem_sphere_of_mem_sphere_of_mem_of_finrank_eq_two {s : affine_subspace ℝ P}
  [finite_dimensional ℝ s.direction] (hd : finrank ℝ s.direction = 2) {s₁ s₂ : sphere P}
  {p₁ p₂ p : P} (hs₁ : s₁.center ∈ s) (hs₂ : s₂.center ∈ s) (hp₁s : p₁ ∈ s) (hp₂s : p₂ ∈ s)
  (hps : p ∈ s) (hs : s₁ ≠ s₂) (hp : p₁ ≠ p₂) (hp₁s₁ : p₁ ∈ s₁) (hp₂s₁ : p₂ ∈ s₁) (hps₁ : p ∈ s₁)
  (hp₁s₂ : p₁ ∈ s₂) (hp₂s₂ : p₂ ∈ s₂) (hps₂ : p ∈ s₂) : p = p₁ ∨ p = p₂ :=
eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two hd hs₁ hs₂ hp₁s hp₂s hps
  ((sphere.center_ne_iff_ne_of_mem hps₁ hps₂).2 hs) hp hp₁s₁ hp₂s₁ hps₁ hp₁s₂ hp₂s₂ hps₂

/-- Two spheres intersect in at most two points in two-dimensional space; this is a version of
`eq_of_dist_eq_of_dist_eq_of_finrank_eq_two` for bundled spheres. -/
lemma eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two [finite_dimensional ℝ V]
  (hd : finrank ℝ V = 2) {s₁ s₂ : sphere P} {p₁ p₂ p : P} (hs : s₁ ≠ s₂) (hp : p₁ ≠ p₂)
  (hp₁s₁ : p₁ ∈ s₁) (hp₂s₁ : p₂ ∈ s₁) (hps₁ : p ∈ s₁) (hp₁s₂ : p₁ ∈ s₂) (hp₂s₂ : p₂ ∈ s₂)
  (hps₂ : p ∈ s₂) : p = p₁ ∨ p = p₂ :=
eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hd ((sphere.center_ne_iff_ne_of_mem hps₁ hps₂).2 hs)
  hp hp₁s₁ hp₂s₁ hps₁ hp₁s₂ hp₂s₂ hps₂

/-- Given a point on a sphere and a point not outside it, the inner product between the
difference of those points and the radius vector is positive unless the points are equal. -/
lemma inner_pos_or_eq_of_dist_le_radius {s : sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
  (hp₂ : dist p₂ s.center ≤ s.radius) : 0 < ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.center⟫ ∨ p₁ = p₂ :=
begin
  by_cases h : p₁ = p₂, { exact or.inr h },
  refine or.inl _,
  rw mem_sphere at hp₁,
  rw [←vsub_sub_vsub_cancel_right p₁ p₂ s.center, inner_sub_left,
      real_inner_self_eq_norm_mul_norm/-, ←dist_eq_norm_vsub, hp₁-/, sub_pos],
  refine lt_of_le_of_ne
    ((real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right _ (norm_nonneg _)))
    _,
  { rwa [←dist_eq_norm_vsub, ←dist_eq_norm_vsub, hp₁] },
  { rcases hp₂.lt_or_eq with hp₂' | hp₂',
    { refine ((real_inner_le_norm _ _).trans_lt (mul_lt_mul_of_pos_right _ _)).ne,
      { rwa [←hp₁, @dist_eq_norm_vsub V, @dist_eq_norm_vsub V] at hp₂' },
      { rw [norm_pos_iff, vsub_ne_zero],
        rintro rfl,
        rw ←hp₁ at hp₂',
        refine (dist_nonneg.not_lt : ¬dist p₂ s.center < 0) _,
        simpa using hp₂' } },
    { rw [←hp₁, @dist_eq_norm_vsub V, @dist_eq_norm_vsub V] at hp₂',
      nth_rewrite 0 ←hp₂',
      rw [ne.def, inner_eq_norm_mul_iff_real, hp₂', ←sub_eq_zero, ←smul_sub,
          vsub_sub_vsub_cancel_right, ←ne.def, smul_ne_zero_iff, vsub_ne_zero,
          and_iff_left (ne.symm h), norm_ne_zero_iff, vsub_ne_zero],
      rintro rfl,
      refine h (eq.symm _),
      simpa using hp₂' } }
end

/-- Given a point on a sphere and a point not outside it, the inner product between the
difference of those points and the radius vector is nonnegative. -/
lemma inner_nonneg_of_dist_le_radius {s : sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
  (hp₂ : dist p₂ s.center ≤ s.radius) : 0 ≤ ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.center⟫ :=
begin
  rcases inner_pos_or_eq_of_dist_le_radius hp₁ hp₂ with h | rfl,
  { exact h.le },
  { simp }
end

/-- Given a point on a sphere and a point inside it, the inner product between the difference of
those points and the radius vector is positive. -/
lemma inner_pos_of_dist_lt_radius {s : sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
  (hp₂ : dist p₂ s.center < s.radius) : 0 < ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.center⟫ :=
begin
  by_cases h : p₁ = p₂,
  { rw [h, mem_sphere] at hp₁,
    exact false.elim (hp₂.ne hp₁) },
  exact (inner_pos_or_eq_of_dist_le_radius hp₁ hp₂.le).resolve_right h
end

/-- Given three collinear points, two on a sphere and one not outside it, the one not outside it
is weakly between the other two points. -/
lemma wbtw_of_collinear_of_dist_center_le_radius {s : sphere P} {p₁ p₂ p₃ : P}
  (h : collinear ℝ ({p₁, p₂, p₃} : set P)) (hp₁ : p₁ ∈ s) (hp₂ : dist p₂ s.center ≤ s.radius)
  (hp₃ : p₃ ∈ s) (hp₁p₃ : p₁ ≠ p₃) : wbtw ℝ p₁ p₂ p₃ :=
h.wbtw_of_dist_eq_of_dist_le hp₁ hp₂ hp₃ hp₁p₃

/-- Given three collinear points, two on a sphere and one inside it, the one inside it is
strictly between the other two points. -/
lemma sbtw_of_collinear_of_dist_center_lt_radius {s : sphere P} {p₁ p₂ p₃ : P}
  (h : collinear ℝ ({p₁, p₂, p₃} : set P)) (hp₁ : p₁ ∈ s) (hp₂ : dist p₂ s.center < s.radius)
  (hp₃ : p₃ ∈ s) (hp₁p₃ : p₁ ≠ p₃) : sbtw ℝ p₁ p₂ p₃ :=
h.sbtw_of_dist_eq_of_dist_lt hp₁ hp₂ hp₃ hp₁p₃

/-- The second intersection of a sphere with a line through a point on that sphere; that point
if it is the only point of intersection of the line with the sphere. The intended use of this
definition is when `p ∈ s`; the definition does not use `s.radius`, so in general it returns
the second intersection with the sphere through `p` and with center `s.center`. -/
def sphere.second_inter (s : sphere P) (p : P) (v : V) : P :=
(-2 * ⟪v, p -ᵥ s.center⟫ / ⟪v, v⟫) • v +ᵥ p

/-- The distance between `second_inter` and the center equals the distance between the original
point and the center. -/
@[simp] lemma sphere.second_inter_dist (s : sphere P) (p : P) (v : V) :
  dist (s.second_inter p v) s.center = dist p s.center :=
begin
  rw sphere.second_inter,
  by_cases hv : v = 0, { simp [hv] },
  rw dist_smul_vadd_eq_dist _ _ hv,
  exact or.inr rfl
end

/-- The point given by `second_inter` lies on the sphere. -/
@[simp] lemma sphere.second_inter_mem {s : sphere P} {p : P} (v : V) :
  s.second_inter p v ∈ s ↔ p ∈ s :=
by simp_rw [mem_sphere, sphere.second_inter_dist]

variables (V)

/-- If the vector is zero, `second_inter` gives the original point. -/
@[simp] lemma sphere.second_inter_zero (s : sphere P) (p : P) :
  s.second_inter p (0 : V) = p :=
by simp [sphere.second_inter]

variables {V}

/-- The point given by `second_inter` equals the original point if and only if the line is
orthogonal to the radius vector. -/
lemma sphere.second_inter_eq_self_iff {s : sphere P} {p : P} {v : V} :
  s.second_inter p v = p ↔ ⟪v, p -ᵥ s.center⟫ = 0 :=
begin
  refine ⟨λ hp, _, λ hp, _⟩,
  { by_cases hv : v = 0, { simp [hv] },
    rwa [sphere.second_inter, eq_comm, eq_vadd_iff_vsub_eq, vsub_self, eq_comm, smul_eq_zero,
         or_iff_left hv, div_eq_zero_iff, inner_self_eq_zero, or_iff_left hv, mul_eq_zero,
         or_iff_right (by norm_num : (-2 : ℝ) ≠ 0)] at hp },
  { rw [sphere.second_inter, hp, mul_zero, zero_div, zero_smul, zero_vadd] }
end

/-- A point on a line through a point on a sphere equals that point or `second_inter`. -/
lemma sphere.eq_or_eq_second_inter_of_mem_mk'_span_singleton_iff_mem {s : sphere P} {p : P}
  (hp : p ∈ s) {v : V} {p' : P} (hp' : p' ∈ affine_subspace.mk' p (ℝ ∙ v)) :
  (p' = p ∨ p' = s.second_inter p v) ↔ p' ∈ s :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with h | h,
    { rwa h },
    { rwa [h, sphere.second_inter_mem] } },
  { rw [affine_subspace.mem_mk'_iff_vsub_mem, submodule.mem_span_singleton] at hp',
    rcases hp' with ⟨r, hr⟩,
    rw [eq_comm, ←eq_vadd_iff_vsub_eq] at hr,
    subst hr,
    by_cases hv : v = 0, { simp [hv] },
    rw sphere.second_inter,
    rw mem_sphere at h hp,
    rw [←hp, dist_smul_vadd_eq_dist _ _ hv] at h,
    rcases h with h | h;
      simp [h] }
end

/-- `second_inter` is unchanged by multiplying the vector by a nonzero real. -/
@[simp] lemma sphere.second_inter_smul (s : sphere P) (p : P) (v : V) {r : ℝ}
  (hr : r ≠ 0) : s.second_inter p (r • v) = s.second_inter p v :=
begin
  simp_rw [sphere.second_inter, real_inner_smul_left, inner_smul_right, smul_smul,
           div_mul_eq_div_div],
  rw [mul_comm, ←mul_div_assoc, ←mul_div_assoc, mul_div_cancel_left _ hr, mul_comm, mul_assoc,
      mul_div_cancel_left _ hr, mul_comm]
end

/-- `second_inter` is unchanged by negating the vector. -/
@[simp] lemma sphere.second_inter_neg (s : sphere P) (p : P) (v : V) :
  s.second_inter p (-v) = s.second_inter p v :=
by rw [←neg_one_smul ℝ v, s.second_inter_smul p v (by norm_num : (-1 : ℝ) ≠ 0)]

/-- Applying `second_inter` twice returns the original point. -/
@[simp] lemma sphere.second_inter_second_inter (s : sphere P) (p : P) (v : V) :
  s.second_inter (s.second_inter p v) v = p :=
begin
  by_cases hv : v = 0, { simp [hv] },
  have hv' : ⟪v, v⟫ ≠ 0 := inner_self_eq_zero.not.2 hv,
  simp only [sphere.second_inter, vadd_vsub_assoc, vadd_vadd, inner_add_right, inner_smul_right,
             div_mul_cancel _ hv'],
  rw [←@vsub_eq_zero_iff_eq V, vadd_vsub, ←add_smul, ←add_div],
  convert zero_smul ℝ _,
  convert zero_div _,
  ring
end

/-- If the vector passed to `second_inter` is given by a subtraction involving the point in
`second_inter`, the result of `second_inter` may be expressed using `line_map`. -/
lemma sphere.second_inter_eq_line_map (s : sphere P) (p p' : P) :
  s.second_inter p (p' -ᵥ p) =
    affine_map.line_map p p' (-2 * ⟪p' -ᵥ p, p -ᵥ s.center⟫ / ⟪p' -ᵥ p, p' -ᵥ p⟫) :=
rfl

/-- If the vector passed to `second_inter` is given by a subtraction involving the point in
`second_inter`, the result lies in the span of the two points. -/
lemma sphere.second_inter_vsub_mem_affine_span (s : sphere P) (p₁ p₂ : P) :
  s.second_inter p₁ (p₂ -ᵥ p₁) ∈ line[ℝ, p₁, p₂] :=
smul_vsub_vadd_mem_affine_span_pair _ _ _

/-- If the vector passed to `second_inter` is given by a subtraction involving the point in
`second_inter`, the three points are collinear. -/
lemma sphere.second_inter_collinear (s : sphere P) (p p' : P) :
  collinear ℝ ({p, p', s.second_inter p (p' -ᵥ p)} : set P) :=
begin
  rw [set.pair_comm, set.insert_comm],
  exact (collinear_insert_iff_of_mem_affine_span (s.second_inter_vsub_mem_affine_span _ _)).2
    (collinear_pair ℝ _ _)
end

/-- If the vector passed to `second_inter` is given by a subtraction involving the point in
`second_inter`, and the second point is not outside the sphere, the second point is weakly
between the first point and the result of `second_inter`. -/
lemma sphere.wbtw_second_inter {s : sphere P} {p p' : P} (hp : p ∈ s)
  (hp' : dist p' s.center ≤ s.radius) : wbtw ℝ p p' (s.second_inter p (p' -ᵥ p)) :=
begin
  by_cases h : p' = p, { simp [h] },
  refine wbtw_of_collinear_of_dist_center_le_radius (s.second_inter_collinear p p')
    hp hp' ((sphere.second_inter_mem _).2 hp) _,
  intro he,
  rw [eq_comm, sphere.second_inter_eq_self_iff, ←neg_neg (p' -ᵥ p), inner_neg_left,
      neg_vsub_eq_vsub_rev, neg_eq_zero, eq_comm] at he,
  exact ((inner_pos_or_eq_of_dist_le_radius hp hp').resolve_right (ne.symm h)).ne he
end

/-- If the vector passed to `second_inter` is given by a subtraction involving the point in
`second_inter`, and the second point is inside the sphere, the second point is strictly between
the first point and the result of `second_inter`. -/
lemma sphere.sbtw_second_inter {s : sphere P} {p p' : P} (hp : p ∈ s)
  (hp' : dist p' s.center < s.radius) : sbtw ℝ p p' (s.second_inter p (p' -ᵥ p)) :=
begin
  refine ⟨sphere.wbtw_second_inter hp hp'.le, _, _⟩,
  { rintro rfl, rw mem_sphere at hp, simpa [hp] using hp' },
  { rintro h,
    rw [h, mem_sphere.1 ((sphere.second_inter_mem _).2 hp)] at hp',
    exact lt_irrefl _ hp' }
end

/-- A set of points is concyclic if it is cospherical and coplanar. (Most results are stated
directly in terms of `cospherical` instead of using `concyclic`.) -/
structure concyclic (ps : set P) : Prop :=
(cospherical : cospherical ps)
(coplanar : coplanar ℝ ps)

/-- A subset of a concyclic set is concyclic. -/
lemma concyclic.subset {ps₁ ps₂ : set P} (hs : ps₁ ⊆ ps₂) (h : concyclic ps₂) : concyclic ps₁ :=
⟨h.1.subset hs, h.2.subset hs⟩

/-- The empty set is concyclic. -/
lemma concyclic_empty : concyclic (∅ : set P) :=
⟨cospherical_empty, coplanar_empty ℝ P⟩

/-- A single point is concyclic. -/
lemma concyclic_singleton (p : P) : concyclic ({p} : set P) :=
⟨cospherical_singleton p, coplanar_singleton ℝ p⟩

/-- Two points are concyclic. -/
lemma concyclic_pair (p₁ p₂ : P) : concyclic ({p₁, p₂} : set P) :=
⟨cospherical_pair p₁ p₂, coplanar_pair ℝ p₁ p₂⟩

end euclidean_geometry
