/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

In this file, we define two predicates `unique_diff_within_at k s x` and `unique_diff_on k s`
ensuring that, if a function has two derivatives, then they have to coincide. As a direct
definition of this fact (quantifying on all target types and all functions) would depend on
universes, we use a more intrinsic definition: if all the possible tangent directions to the set
`s` at the point `x` span a dense subset of the whole subset, it is easy to check that the
derivative has to be unique.

Therefore, we introduce the set of all tangent directions, named `tangent_cone_at`,
and express `unique_diff_within_at` and `unique_diff_on` in terms of it.
One should however think of this definition as an implementation detail: the only reason to
introduce the predicates `unique_diff_within_at` and `unique_diff_on` is to ensure the uniqueness
of the derivative. This is why their names reflect their uses, and not how they are defined.

Note that this file is imported by `deriv.lean`. Hence, derivatives are not defined yet. The
property of uniqueness of the derivative is therefore proved in `deriv.lean`, but based on the
properties of the tangent cone we prove here.
-/

import analysis.convex analysis.normed_space.bounded_linear_maps

variables (k : Type*) [nondiscrete_normed_field k]
variables {E : Type*} [normed_group E] [normed_space k E]
variables {F : Type*} [normed_group F] [normed_space k F]
variables {G : Type*} [normed_group G] [normed_space ℝ G]

set_option class.instance_max_depth 50
open filter set

/-- The set of all tangent directions to the set `s` at the point `x`. -/
def tangent_cone_at (s : set E) (x : E) : set E :=
{y : E | ∃(c : ℕ → k) (d : ℕ → E), {n:ℕ | x + d n ∈ s} ∈ (at_top : filter ℕ) ∧
  (tendsto (λn, ∥c n∥) at_top at_top) ∧ (tendsto (λn, c n • d n) at_top (nhds y))}

/-- A property ensuring that the tangent cone to `s` at `x` spans a dense subset of the whole space.
The main role of this property is to ensure that the differential within `s` at `x` is unique,
hence this name. The uniqueness it asserts is proved in `unique_diff_within_at.eq` in `deriv.lean`.
To avoid pathologies in dimension 0, we also require that `x` belongs to the closure of `s` (which
is automatic when `E` is not `0`-dimensional).
 -/
def unique_diff_within_at (s : set E) (x : E) : Prop :=
closure ((submodule.span k (tangent_cone_at k s x)) : set E) = univ ∧ x ∈ closure s

/-- A property ensuring that the tangent cone to `s` at any of its points spans a dense subset of
the whole space.  The main role of this property is to ensure that the differential along `s` is
unique, hence this name. The uniqueness it asserts is proved in `unique_diff_on.eq` in
`deriv.lean`. -/
def unique_diff_on (s : set E) : Prop :=
∀x ∈ s, unique_diff_within_at k s x

variables {k} {x y : E} {s t : set E}

section tangent_cone
/- This section is devoted to the properties of the tangent cone. -/

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
lemma tangent_cone_at.lim_zero {c : ℕ → k} {d : ℕ → E}
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

/-- Intersecting with a neighborhood of the point does not change the tangent cone. -/
lemma tangent_cone_inter_nhds (ht : t ∈ nhds x) :
  tangent_cone_at k (s ∩ t) x = tangent_cone_at k s x :=
begin
  refine subset.antisymm (tangent_cone_mono (inter_subset_left _ _)) _,
  rintros y ⟨c, d, ds, ctop, clim⟩,
  refine ⟨c, d, _, ctop, clim⟩,
  have : {n : ℕ | x + d n ∈ t} ∈ at_top,
  { have : tendsto (λn, x + d n) at_top (nhds (x + 0)) :=
      tendsto_add tendsto_const_nhds (tangent_cone_at.lim_zero ctop clim),
    rw add_zero at this,
    exact mem_map.1 (this ht) },
  exact inter_mem_sets ds this
end

/-- The tangent cone of a product contains the tangent cone of its left factor. -/
lemma subset_tangent_cone_prod_left {t : set F} {y : F} (ht : y ∈ closure t) :
  set.prod (tangent_cone_at k s x) {(0 : F)} ⊆ tangent_cone_at k (set.prod s t) (x, y) :=
begin
  rintros ⟨v, w⟩ ⟨⟨c, d, hd, hc, hy⟩, hw⟩,
  have : w = 0, by simpa using hw,
  rw this,
  have : ∀n, ∃d', y + d' ∈ t ∧ ∥c n • d'∥ ≤ ((1:ℝ)/2)^n,
  { assume n,
    have c_pos : 0 < 1 + ∥c n∥ :=
      add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _),
    rcases metric.mem_closure_iff'.1 ht ((1 + ∥c n∥)⁻¹ * (1/2)^n) _ with ⟨z, z_pos, hz⟩,
    refine ⟨z - y, _, _⟩,
    { convert z_pos, abel },
    { rw [norm_smul, ← dist_eq_norm, dist_comm],
      calc ∥c n∥ * dist y z ≤ (1 + ∥c n∥) * ((1 + ∥c n∥)⁻¹ * (1/2)^n) :
      begin
        apply mul_le_mul _ (le_of_lt hz) dist_nonneg (le_of_lt c_pos),
        simp only [zero_le_one, le_add_iff_nonneg_left]
      end
      ... = (1/2)^n :
      begin
        rw [← mul_assoc, mul_inv_cancel, one_mul],
        exact ne_of_gt c_pos
      end },
    { apply mul_pos (inv_pos c_pos) (pow_pos _ _),
      norm_num } },
  choose d' hd' using this,
  refine ⟨c, λn, (d n, d' n), _, hc, _⟩,
  show {n : ℕ | (x, y) + (d n, d' n) ∈ set.prod s t} ∈ at_top,
  { apply filter.mem_sets_of_superset hd,
    assume n hn,
    simp at hn,
    simp [hn, (hd' n).1] },
  { apply tendsto_prod_mk_nhds hy,
    change tendsto (λ (n : ℕ), c n • d' n) at_top (nhds 0),
    rw tendsto_zero_iff_norm_tendsto_zero,
    refine squeeze_zero (λn, norm_nonneg _) (λn, (hd' n).2) _,
    apply tendsto_pow_at_top_nhds_0_of_lt_1; norm_num }
end

/-- The tangent cone of a product contains the tangent cone of its right factor. -/
lemma subset_tangent_cone_prod_right {t : set F} {y : F}
  (hs : x ∈ closure s) :
  set.prod {(0 : E)} (tangent_cone_at k t y) ⊆ tangent_cone_at k (set.prod s t) (x, y) :=
begin
  rintros ⟨v, w⟩ ⟨hv, ⟨c, d, hd, hc, hy⟩⟩,
  have : v = 0, by simpa using hv,
  rw this,
  have : ∀n, ∃d', x + d' ∈ s ∧ ∥c n • d'∥ ≤ ((1:ℝ)/2)^n,
  { assume n,
    have c_pos : 0 < 1 + ∥c n∥ :=
      add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _),
    rcases metric.mem_closure_iff'.1 hs ((1 + ∥c n∥)⁻¹ * (1/2)^n) _ with ⟨z, z_pos, hz⟩,
    refine ⟨z - x, _, _⟩,
    { convert z_pos, abel },
    { rw [norm_smul, ← dist_eq_norm, dist_comm],
      calc ∥c n∥ * dist x z ≤ (1 + ∥c n∥) * ((1 + ∥c n∥)⁻¹ * (1/2)^n) :
      begin
        apply mul_le_mul _ (le_of_lt hz) dist_nonneg (le_of_lt c_pos),
        simp only [zero_le_one, le_add_iff_nonneg_left]
      end
      ... = (1/2)^n :
      begin
        rw [← mul_assoc, mul_inv_cancel, one_mul],
        exact ne_of_gt c_pos
      end },
    { apply mul_pos (inv_pos c_pos) (pow_pos _ _),
      norm_num } },
  choose d' hd' using this,
  refine ⟨c, λn, (d' n, d n), _, hc, _⟩,
  show {n : ℕ | (x, y) + (d' n, d n) ∈ set.prod s t} ∈ at_top,
  { apply filter.mem_sets_of_superset hd,
    assume n hn,
    simp at hn,
    simp [hn, (hd' n).1] },
  { apply tendsto_prod_mk_nhds _ hy,
    change tendsto (λ (n : ℕ), c n • d' n) at_top (nhds 0),
    rw tendsto_zero_iff_norm_tendsto_zero,
    refine squeeze_zero (λn, norm_nonneg _) (λn, (hd' n).2) _,
    apply tendsto_pow_at_top_nhds_0_of_lt_1; norm_num }
end

/-- If a subset of a real vector space contains a segment, then the direction of this
segment belongs to the tangent cone at its endpoints. -/
lemma mem_tangent_cone_of_segment_subset {s : set G} {x y : G} (h : segment x y ⊆ s) :
  y - x ∈ tangent_cone_at ℝ s x :=
begin
  let w : ℝ := 2,
  let c := λn:ℕ, (2:ℝ)^n,
  let d := λn:ℕ, (c n)⁻¹ • (y-x),
  refine ⟨c, d, filter.univ_mem_sets' (λn, h _), _, _⟩,
  show x + d n ∈ segment x y,
  { refine ⟨(c n)⁻¹, ⟨_, _⟩, _⟩,
    { rw inv_nonneg, apply pow_nonneg, norm_num },
    { apply inv_le_one, apply one_le_pow_of_one_le, norm_num },
    { simp only [d], abel } },
  show filter.tendsto (λ (n : ℕ), ∥c n∥) filter.at_top filter.at_top,
  { have : (λ (n : ℕ), ∥c n∥) = c,
      by { ext n, exact abs_of_nonneg (pow_nonneg (by norm_num) _) },
    rw this,
    exact tendsto_pow_at_top_at_top_of_gt_1 (by norm_num) },
  show filter.tendsto (λ (n : ℕ), c n • d n) filter.at_top (nhds (y - x)),
  { have : (λ (n : ℕ), c n • d n) = (λn, y - x),
    { ext n,
      simp only [d, smul_smul],
      rw [mul_inv_cancel, one_smul],
      exact pow_ne_zero _ (by norm_num) },
    rw this,
    apply tendsto_const_nhds }
end

end tangent_cone

section unique_diff
/- This section is devoted to properties of the predicates `unique_diff_within_at` and
`unique_diff_on`. -/

lemma unique_diff_within_at_univ : unique_diff_within_at k univ x :=
by { rw [unique_diff_within_at, tangent_cone_univ], simp }

lemma unique_diff_on_univ : unique_diff_on k (univ : set E) :=
λx hx, unique_diff_within_at_univ

lemma unique_diff_within_at_inter (ht : t ∈ nhds x) :
  unique_diff_within_at k (s ∩ t) x ↔ unique_diff_within_at k s x :=
begin
  have : x ∈ closure (s ∩ t) ↔ x ∈ closure s,
  { split,
    { assume h, exact closure_mono (inter_subset_left _ _) h },
    { assume h,
      rw mem_closure_iff_nhds at ⊢ h,
      assume u hu,
      rw [inter_comm s t, ← inter_assoc],
      exact h _ (filter.inter_mem_sets hu ht) } },
  rw [unique_diff_within_at, unique_diff_within_at, tangent_cone_inter_nhds ht, this]
end

lemma unique_diff_within_at.inter (hs : unique_diff_within_at k s x) (ht : t ∈ nhds x) :
  unique_diff_within_at k (s ∩ t) x :=
(unique_diff_within_at_inter ht).2 hs

lemma unique_diff_within_at.mono (h : unique_diff_within_at k s x) (st : s ⊆ t) :
  unique_diff_within_at k t x :=
begin
  unfold unique_diff_within_at at *,
  rw [← univ_subset_iff, ← h.1],
  exact ⟨closure_mono (submodule.span_mono (tangent_cone_mono st)), closure_mono st h.2⟩
end

lemma is_open.unique_diff_within_at (hs : is_open s) (xs : x ∈ s) : unique_diff_within_at k s x :=
begin
  have := unique_diff_within_at_univ.inter (mem_nhds_sets hs xs),
  rwa univ_inter at this
end

lemma unique_diff_on_inter (hs : unique_diff_on k s) (ht : is_open t) : unique_diff_on k (s ∩ t) :=
λx hx, (hs x hx.1).inter (mem_nhds_sets ht hx.2)

lemma is_open.unique_diff_on (hs : is_open s) : unique_diff_on k s :=
λx hx, is_open.unique_diff_within_at hs hx

/-- The product of two sets of unique differentiability at points `x` and `y` has unique
differentiability at `(x, y)`. -/
lemma unique_diff_within_at.prod {t : set F} {y : F}
  (hs : unique_diff_within_at k s x) (ht : unique_diff_within_at k t y) :
  unique_diff_within_at k (set.prod s t) (x, y) :=
begin
  rw [unique_diff_within_at, ← univ_subset_iff] at ⊢ hs ht,
  split,
  { assume v _,
    rw metric.mem_closure_iff',
    assume ε ε_pos,
    rcases v with ⟨v₁, v₂⟩,
    rcases metric.mem_closure_iff'.1 (hs.1 (mem_univ v₁)) ε ε_pos with ⟨w₁, w₁_mem, h₁⟩,
    rcases metric.mem_closure_iff'.1 (ht.1 (mem_univ v₂)) ε ε_pos with ⟨w₂, w₂_mem, h₂⟩,
    have I₁ : (w₁, (0 : F)) ∈ submodule.span k (tangent_cone_at k (set.prod s t) (x, y)),
    { apply submodule.span_induction w₁_mem,
      { assume w hw,
        have : (w, (0 : F)) ∈ (set.prod (tangent_cone_at k s x) {(0 : F)}),
        { rw mem_prod,
          simp [hw],
          apply mem_insert },
        have : (w, (0 : F)) ∈ tangent_cone_at k (set.prod s t) (x, y) :=
          subset_tangent_cone_prod_left ht.2 this,
        exact submodule.subset_span this },
      { exact submodule.zero_mem _ },
      { assume a b ha hb,
        have : (a, (0 : F)) + (b, (0 : F)) = (a + b, (0 : F)), by simp,
        rw ← this,
        exact submodule.add_mem _ ha hb },
      { assume c a ha,
        have : c • (0 : F) = (0 : F), by simp,
        rw ← this,
        exact submodule.smul_mem _ _ ha } },
    have I₂ : ((0 : E), w₂) ∈ submodule.span k (tangent_cone_at k (set.prod s t) (x, y)),
    { apply submodule.span_induction w₂_mem,
      { assume w hw,
        have : ((0 : E), w) ∈ (set.prod {(0 : E)} (tangent_cone_at k t y)),
        { rw mem_prod,
          simp [hw],
          apply mem_insert },
        have : ((0 : E), w) ∈ tangent_cone_at k (set.prod s t) (x, y) :=
          subset_tangent_cone_prod_right hs.2 this,
        exact submodule.subset_span this },
      { exact submodule.zero_mem _ },
      { assume a b ha hb,
        have : ((0 : E), a) + ((0 : E), b) = ((0 : E), a + b), by simp,
        rw ← this,
        exact submodule.add_mem _ ha hb },
      { assume c a ha,
        have : c • (0 : E) = (0 : E), by simp,
        rw ← this,
        exact submodule.smul_mem _ _ ha } },
    have I : (w₁, w₂) ∈ submodule.span k (tangent_cone_at k (set.prod s t) (x, y)),
    { have : (w₁, (0 : F)) + ((0 : E), w₂) = (w₁, w₂), by simp,
      rw ← this,
      exact submodule.add_mem _ I₁ I₂ },
    refine ⟨(w₁, w₂), I, _⟩,
    simp [dist, h₁, h₂] },
  { simp [closure_prod_eq, mem_prod_iff, hs.2, ht.2] }
end

/-- The product of two sets of unique differentiability is a set of unique differentiability. -/
lemma unique_diff_on.prod {t : set F} (hs : unique_diff_on k s) (ht : unique_diff_on k t) :
  unique_diff_on k (set.prod s t) :=
λ ⟨x, y⟩ h, unique_diff_within_at.prod (hs x h.1) (ht y h.2)

/-- In a real vector space, a convex set with nonempty interior is a set of unique
differentiability. -/
theorem unique_diff_on_convex {s : set G} (conv : convex s) (hs : interior s ≠ ∅) :
  unique_diff_on ℝ s :=
begin
  assume x xs,
  have A : ∀v, ∃a∈ tangent_cone_at ℝ s x, ∃b∈ tangent_cone_at ℝ s x, ∃δ>(0:ℝ), δ • v = b-a,
  { assume v,
    rcases ne_empty_iff_exists_mem.1 hs with ⟨y, hy⟩,
    have ys : y ∈ s := interior_subset hy,
    have : ∃(δ : ℝ), 0<δ ∧ y + δ • v ∈ s,
    { by_cases h : ∥v∥ = 0,
      { exact ⟨1, zero_lt_one, by simp [(norm_eq_zero _).1 h, ys]⟩ },
      { rcases mem_interior.1 hy with ⟨u, us, u_open, yu⟩,
        rcases metric.is_open_iff.1 u_open y yu with ⟨ε, εpos, hε⟩,
        let δ := (ε/2) / ∥v∥,
        have δpos : 0 < δ := div_pos (half_pos εpos) (lt_of_le_of_ne (norm_nonneg _) (ne.symm h)),
        have : y + δ • v ∈ s,
        { apply us (hε _),
          rw [metric.mem_ball, dist_eq_norm],
          calc ∥(y + δ • v) - y ∥ = ∥δ • v∥ : by {congr' 1, abel }
          ... = ∥δ∥ * ∥v∥ : norm_smul _ _
          ... = δ * ∥v∥ : by simp only [norm, abs_of_nonneg (le_of_lt δpos)]
          ... = ε /2 : div_mul_cancel _ h
          ... < ε : half_lt_self εpos },
        exact ⟨δ, δpos, this⟩ } },
    rcases this with ⟨δ, δpos, hδ⟩,
    refine ⟨y-x, _, (y + δ • v) - x, _, δ, δpos, by abel⟩,
    exact mem_tangent_cone_of_segment_subset ((convex_segment_iff _).1 conv x y xs ys),
    exact mem_tangent_cone_of_segment_subset ((convex_segment_iff _).1 conv x _ xs hδ) },
  have B : ∀v:G, v ∈ submodule.span ℝ (tangent_cone_at ℝ s x),
  { assume v,
    rcases A v with ⟨a, ha, b, hb, δ, hδ, h⟩,
    have : v = δ⁻¹ • (b - a),
      by { rw [← h, smul_smul, inv_mul_cancel, one_smul], exact (ne_of_gt hδ) },
    rw this,
    exact submodule.smul_mem _ _
      (submodule.sub_mem _ (submodule.subset_span hb) (submodule.subset_span ha)) },
  refine ⟨univ_subset_iff.1 (λv hv, subset_closure (B v)), subset_closure xs⟩
end

/-- The real interval `[0, 1]` is a set of unique differentiability. -/
lemma unique_diff_on_Icc_zero_one : unique_diff_on ℝ (Icc (0:ℝ) 1) :=
begin
  apply unique_diff_on_convex (convex_Icc 0 1),
  have : (1/(2:ℝ)) ∈ interior (Icc (0:ℝ) 1) :=
    mem_interior.2 ⟨Ioo (0:ℝ) 1, Ioo_subset_Icc_self, is_open_Ioo, by norm_num, by norm_num⟩,
  exact ne_empty_of_mem this,
end

end unique_diff
