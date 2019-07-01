/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

The tangent cone to a set at a point is the set of all tangent directions to this set.
We define it as `tangent_cone_at`.
When it spans the whole space, this implies that the derivative of a function within this set at this
point has to be unique. We define predicates `unique_diff_within_at` and `unique_diff_on`
expressing this property, and develop their basic features. The fact that this implies the
uniqueness of the derivative is proved in `deriv.lean`.
-/

import analysis.normed_space.bounded_linear_maps

variables (k : Type*) [nondiscrete_normed_field k]
variables {E : Type*} [normed_group E] [normed_space k E]

set_option class.instance_max_depth 50
open filter set

/- A notation for sets on which the differential has to be unique. This is for instance the case
on open sets, which is the main case of applications, but also on closed halfspaces or closed
disks. It is only on such sets that it makes sense to talk about "the" derivative, and to talk
about higher smoothness.

The differential is unique when the tangent directions (called the tangent cone below) spans a
dense subset of the underlying normed space. -/

def tangent_cone_at (s : set E) (x : E) : set E :=
{y : E | ∃(c:ℕ → k) (d: ℕ → E), {n:ℕ | x + d n ∈ s} ∈ (at_top : filter ℕ) ∧
  (tendsto (λn, ∥c n∥) at_top at_top) ∧ (tendsto (λn, c n • d n) at_top (nhds y))}

/-- A property ensuring that the tangent cone to `s` at `x` spans a dense subset of the whole space.
The main role of this property is to ensure that the differential within `s` at `x` is unique,
hence this name. The uniqueness it asserts is proved in `unique_diff_within_at.eq` -/
def unique_diff_within_at (s : set E) (x : E) : Prop :=
closure ((submodule.span k (tangent_cone_at k s x)) : set E) = univ

/-- A property ensuring that the tangent cone to `s` at any of its points spans a dense subset of
the whole space.  The main role of this property is to ensure that the differential along `s` is
unique, hence this name. The uniqueness it asserts is proved in `unique_diff_on.eq` -/
def unique_diff_on (s : set E) : Prop :=
∀x ∈ s, unique_diff_within_at k s x

variables {k} {s t : set E} {x : E}

lemma tangent_cone_univ : tangent_cone_at k univ x = univ :=
begin
  refine univ_subset_iff.1 (λy hy, _),
  rcases exists_one_lt_norm k with ⟨w, hw⟩,
  refine ⟨λn, w^n, λn, (w^n)⁻¹ • y, univ_mem_sets' (λn, mem_univ _),  _, _⟩,
  { simp only [norm_pow],
    exact tendsto_pow_at_top_at_top_of_gt_1 hw },
  { convert tendsto_const_nhds,
    ext n,
    have : w ^ n * (w ^ n)⁻¹ = 1,
    { apply mul_inv_cancel,
      apply pow_ne_zero,
      simpa [norm_eq_zero] using (ne_of_lt (lt_trans zero_lt_one hw)).symm },
    rw [smul_smul, this, one_smul] }
end

lemma tangent_cone_mono (h : s ⊆ t) :
  tangent_cone_at k s x ⊆ tangent_cone_at k t x :=
begin
  rintros y ⟨c, d, ds, ctop, clim⟩,
  exact ⟨c, d, mem_sets_of_superset ds (λn hn, h hn), ctop, clim⟩
end

/-- Auxiliary lemma ensuring that, under the assumptions defining the tangent cone,
the sequence `d` tends to 0 at infinity. -/
lemma tangent_cone_at.lim_zero {y : E} {c : ℕ → k} {d : ℕ → E}
  (hc : tendsto (λn, ∥c n∥) at_top at_top) (hd : tendsto (λn, c n • d n) at_top (nhds y)) :
  tendsto d at_top (nhds 0) :=
begin
  have A : tendsto (λn, ∥c n∥⁻¹) at_top (nhds 0) :=
    tendsto_inverse_at_top_nhds_0.comp hc,
  have B : tendsto (λn, ∥c n • d n∥) at_top (nhds ∥y∥) :=
    (continuous_norm.tendsto _).comp hd,
  have C : tendsto (λn, ∥c n∥⁻¹ * ∥c n • d n∥) at_top (nhds (0 * ∥y∥)) :=
    tendsto_mul A B,
  rw zero_mul at C,
  have : {n | ∥c n∥⁻¹ * ∥c n • d n∥ = ∥d n∥} ∈ (@at_top ℕ _),
  { have : {n | 1 ≤ ∥c n∥} ∈ (@at_top ℕ _) :=
      hc (mem_at_top 1),
    apply mem_sets_of_superset this (λn hn, _),
    rw mem_set_of_eq at hn,
    rw [mem_set_of_eq, ← norm_inv, ← norm_smul, smul_smul, inv_mul_cancel, one_smul],
    simpa [norm_eq_zero] using (ne_of_lt (lt_of_lt_of_le zero_lt_one hn)).symm },
  have D : tendsto (λ (n : ℕ), ∥d n∥) at_top (nhds 0) :=
    tendsto.congr' this C,
  rw tendsto_zero_iff_norm_tendsto_zero,
  exact D
end

/-- Intersecting with an open set does not change the tangent cone. -/
lemma tangent_cone_inter_open {x : E} {s t : set E} (xs : x ∈ s) (xt : x ∈ t) (ht : is_open t) :
  tangent_cone_at k (s ∩ t) x = tangent_cone_at k s x :=
begin
  refine subset.antisymm (tangent_cone_mono (inter_subset_left _ _)) _,
  rintros y ⟨c, d, ds, ctop, clim⟩,
  refine ⟨c, d, _, ctop, clim⟩,
  have : {n : ℕ | x + d n ∈ t} ∈ at_top,
  { have : tendsto (λn, x + d n) at_top (nhds (x + 0)) :=
      tendsto_add tendsto_const_nhds (tangent_cone_at.lim_zero ctop clim),
    rw add_zero at this,
    exact tendsto_nhds.1 this t ht xt },
  exact inter_mem_sets ds this
end

lemma unique_diff_within_univ_at : unique_diff_within_at k univ x :=
by { rw [unique_diff_within_at, tangent_cone_univ], simp }

lemma unique_diff_within_at_inter (xs : x ∈ s) (xt : x ∈ t) (hs : unique_diff_within_at k s x)
  (ht : is_open t) : unique_diff_within_at k (s ∩ t) x :=
begin
  unfold unique_diff_within_at,
  rw tangent_cone_inter_open xs xt ht,
  exact hs
end

lemma is_open.unique_diff_within_at (xs : x ∈ s) (hs : is_open s) : unique_diff_within_at k s x :=
begin
  have := unique_diff_within_at_inter (mem_univ _) xs unique_diff_within_univ_at hs,
  rwa univ_inter at this
end

lemma unique_diff_on_inter (hs : unique_diff_on k s) (ht : is_open t) : unique_diff_on k (s ∩ t) :=
λx hx, unique_diff_within_at_inter hx.1 hx.2 (hs x hx.1) ht

lemma is_open.unique_diff_on (hs : is_open s) : unique_diff_on k s :=
λx hx, is_open.unique_diff_within_at hx hs
