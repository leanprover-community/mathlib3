/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
import analysis.convex.combination
import analysis.convex.strict
import topology.path_connected
import topology.algebra.affine
import topology.algebra.module.basic

/-!
# Topological properties of convex sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We prove the following facts:

* `convex.interior` : interior of a convex set is convex;
* `convex.closure` : closure of a convex set is convex;
* `set.finite.compact_convex_hull` : convex hull of a finite set is compact;
* `set.finite.is_closed_convex_hull` : convex hull of a finite set is closed.
-/

assert_not_exists has_norm

open metric set
open_locale pointwise convex

variables {ι 𝕜 E : Type*}

lemma real.convex_iff_is_preconnected {s : set ℝ} : convex ℝ s ↔ is_preconnected s :=
convex_iff_ord_connected.trans is_preconnected_iff_ord_connected.symm

alias real.convex_iff_is_preconnected ↔ _ is_preconnected.convex

/-! ### Standard simplex -/

section std_simplex

variables [fintype ι]

/-- Every vector in `std_simplex 𝕜 ι` has `max`-norm at most `1`. -/
lemma std_simplex_subset_closed_ball :
  std_simplex ℝ ι ⊆ metric.closed_ball 0 1 :=
begin
  assume f hf,
  rw [metric.mem_closed_ball, dist_pi_le_iff zero_le_one],
  intros x,
  rw [pi.zero_apply, real.dist_0_eq_abs, abs_of_nonneg $ hf.1 x],
  exact (mem_Icc_of_mem_std_simplex hf x).2,
end

variable (ι)

/-- `std_simplex ℝ ι` is bounded. -/
lemma bounded_std_simplex : metric.bounded (std_simplex ℝ ι) :=
(metric.bounded_iff_subset_ball 0).2 ⟨1, std_simplex_subset_closed_ball⟩

/-- `std_simplex ℝ ι` is closed. -/
lemma is_closed_std_simplex : is_closed (std_simplex ℝ ι) :=
(std_simplex_eq_inter ℝ ι).symm ▸ is_closed.inter
  (is_closed_Inter $ λ i, is_closed_le continuous_const (continuous_apply i))
  (is_closed_eq (continuous_finset_sum _ $ λ x _, continuous_apply x) continuous_const)

/-- `std_simplex ℝ ι` is compact. -/
lemma is_compact_std_simplex : is_compact (std_simplex ℝ ι) :=
metric.is_compact_iff_is_closed_bounded.2 ⟨is_closed_std_simplex ι, bounded_std_simplex ι⟩

end std_simplex

/-! ### Topological vector space -/

section topological_space
variables [linear_ordered_ring 𝕜] [densely_ordered 𝕜] [topological_space 𝕜] [order_topology 𝕜]
  [add_comm_group E] [topological_space E] [has_continuous_add E] [module 𝕜 E]
  [has_continuous_smul 𝕜 E] {x y : E}

lemma segment_subset_closure_open_segment : [x -[𝕜] y] ⊆ closure (open_segment 𝕜 x y) :=
begin
  rw [segment_eq_image, open_segment_eq_image, ←closure_Ioo (zero_ne_one' 𝕜)],
  exact image_closure_subset_closure_image (by continuity),
end

end topological_space

section pseudo_metric_space
variables [linear_ordered_ring 𝕜] [densely_ordered 𝕜] [pseudo_metric_space 𝕜] [order_topology 𝕜]
  [proper_space 𝕜] [compact_Icc_space 𝕜] [add_comm_group E] [topological_space E] [t2_space E]
  [has_continuous_add E] [module 𝕜 E] [has_continuous_smul 𝕜 E]

@[simp] lemma closure_open_segment (x y : E) : closure (open_segment 𝕜 x y) = [x -[𝕜] y] :=
begin
  rw [segment_eq_image, open_segment_eq_image, ←closure_Ioo (zero_ne_one' 𝕜)],
  exact (image_closure_of_is_compact (bounded_Ioo _ _).is_compact_closure $
    continuous.continuous_on $ by continuity).symm,
end

end pseudo_metric_space

section has_continuous_const_smul

variables [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] [topological_space E]
  [topological_add_group E] [has_continuous_const_smul 𝕜 E]

/-- If `s` is a convex set, then `a • interior s + b • closure s ⊆ interior s` for all `0 < a`,
`0 ≤ b`, `a + b = 1`. See also `convex.combo_interior_self_subset_interior` for a weaker version. -/
lemma convex.combo_interior_closure_subset_interior {s : set E} (hs : convex 𝕜 s) {a b : 𝕜}
  (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
  a • interior s + b • closure s ⊆ interior s :=
interior_smul₀ ha.ne' s ▸
  calc interior (a • s) + b • closure s ⊆ interior (a • s) + closure (b • s) :
    add_subset_add subset.rfl (smul_closure_subset b s)
  ... = interior (a • s) + b • s : by rw is_open_interior.add_closure (b • s)
  ... ⊆ interior (a • s + b • s) : subset_interior_add_left
  ... ⊆ interior s : interior_mono $ hs.set_combo_subset ha.le hb hab

/-- If `s` is a convex set, then `a • interior s + b • s ⊆ interior s` for all `0 < a`, `0 ≤ b`,
`a + b = 1`. See also `convex.combo_interior_closure_subset_interior` for a stronger version. -/
lemma convex.combo_interior_self_subset_interior {s : set E} (hs : convex 𝕜 s) {a b : 𝕜}
  (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
  a • interior s + b • s ⊆ interior s :=
calc a • interior s + b • s ⊆ a • interior s + b • closure s :
  add_subset_add subset.rfl $ image_subset _ subset_closure
... ⊆ interior s : hs.combo_interior_closure_subset_interior ha hb hab

/-- If `s` is a convex set, then `a • closure s + b • interior s ⊆ interior s` for all `0 ≤ a`,
`0 < b`, `a + b = 1`. See also `convex.combo_self_interior_subset_interior` for a weaker version. -/
lemma convex.combo_closure_interior_subset_interior {s : set E} (hs : convex 𝕜 s) {a b : 𝕜}
  (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) :
  a • closure s + b • interior s ⊆ interior s :=
by { rw add_comm, exact hs.combo_interior_closure_subset_interior hb ha (add_comm a b ▸ hab) }

/-- If `s` is a convex set, then `a • s + b • interior s ⊆ interior s` for all `0 ≤ a`, `0 < b`,
`a + b = 1`. See also `convex.combo_closure_interior_subset_interior` for a stronger version. -/
lemma convex.combo_self_interior_subset_interior {s : set E} (hs : convex 𝕜 s) {a b : 𝕜}
  (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) :
  a • s + b • interior s ⊆ interior s :=
by { rw add_comm, exact hs.combo_interior_self_subset_interior hb ha (add_comm a b ▸ hab) }

lemma convex.combo_interior_closure_mem_interior {s : set E} (hs : convex 𝕜 s) {x y : E}
  (hx : x ∈ interior s) (hy : y ∈ closure s) {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
  a • x + b • y ∈ interior s :=
hs.combo_interior_closure_subset_interior ha hb hab $
  add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)

lemma convex.combo_interior_self_mem_interior {s : set E} (hs : convex 𝕜 s) {x y : E}
  (hx : x ∈ interior s) (hy : y ∈ s) {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
  a • x + b • y ∈ interior s :=
hs.combo_interior_closure_mem_interior hx (subset_closure hy) ha hb hab

lemma convex.combo_closure_interior_mem_interior {s : set E} (hs : convex 𝕜 s) {x y : E}
  (hx : x ∈ closure s) (hy : y ∈ interior s) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) :
  a • x + b • y ∈ interior s :=
hs.combo_closure_interior_subset_interior ha hb hab $
  add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)

lemma convex.combo_self_interior_mem_interior {s : set E} (hs : convex 𝕜 s) {x y : E}
  (hx : x ∈ s) (hy : y ∈ interior s) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) :
  a • x + b • y ∈ interior s :=
hs.combo_closure_interior_mem_interior (subset_closure hx) hy ha hb hab

lemma convex.open_segment_interior_closure_subset_interior {s : set E} (hs : convex 𝕜 s) {x y : E}
  (hx : x ∈ interior s) (hy : y ∈ closure s) : open_segment 𝕜 x y ⊆ interior s :=
begin
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩,
  exact hs.combo_interior_closure_mem_interior hx hy ha hb.le hab
end

lemma convex.open_segment_interior_self_subset_interior {s : set E} (hs : convex 𝕜 s) {x y : E}
  (hx : x ∈ interior s) (hy : y ∈ s) : open_segment 𝕜 x y ⊆ interior s :=
hs.open_segment_interior_closure_subset_interior hx (subset_closure hy)

lemma convex.open_segment_closure_interior_subset_interior {s : set E} (hs : convex 𝕜 s) {x y : E}
  (hx : x ∈ closure s) (hy : y ∈ interior s) : open_segment 𝕜 x y ⊆ interior s :=
begin
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩,
  exact hs.combo_closure_interior_mem_interior hx hy ha.le hb hab
end

lemma convex.open_segment_self_interior_subset_interior {s : set E} (hs : convex 𝕜 s) {x y : E}
  (hx : x ∈ s) (hy : y ∈ interior s) : open_segment 𝕜 x y ⊆ interior s :=
hs.open_segment_closure_interior_subset_interior (subset_closure hx) hy

/-- If `x ∈ closure s` and `y ∈ interior s`, then the segment `(x, y]` is included in `interior s`.
-/
lemma convex.add_smul_sub_mem_interior' {s : set E} (hs : convex 𝕜 s)
  {x y : E} (hx : x ∈ closure s) (hy : y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) :
  x + t • (y - x) ∈ interior s :=
by simpa only [sub_smul, smul_sub, one_smul, add_sub, add_comm]
  using hs.combo_interior_closure_mem_interior hy hx ht.1 (sub_nonneg.mpr ht.2)
    (add_sub_cancel'_right _ _)

/-- If `x ∈ s` and `y ∈ interior s`, then the segment `(x, y]` is included in `interior s`. -/
lemma convex.add_smul_sub_mem_interior {s : set E} (hs : convex 𝕜 s)
  {x y : E} (hx : x ∈ s) (hy : y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) :
  x + t • (y - x) ∈ interior s :=
hs.add_smul_sub_mem_interior' (subset_closure hx) hy ht

/-- If `x ∈ closure s` and `x + y ∈ interior s`, then `x + t y ∈ interior s` for `t ∈ (0, 1]`. -/
lemma convex.add_smul_mem_interior' {s : set E} (hs : convex 𝕜 s)
  {x y : E} (hx : x ∈ closure s) (hy : x + y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) :
  x + t • y ∈ interior s :=
by simpa only [add_sub_cancel'] using hs.add_smul_sub_mem_interior' hx hy ht

/-- If `x ∈ s` and `x + y ∈ interior s`, then `x + t y ∈ interior s` for `t ∈ (0, 1]`. -/
lemma convex.add_smul_mem_interior {s : set E} (hs : convex 𝕜 s)
  {x y : E} (hx : x ∈ s) (hy : x + y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) :
  x + t • y ∈ interior s :=
hs.add_smul_mem_interior' (subset_closure hx) hy ht

/-- In a topological vector space, the interior of a convex set is convex. -/
protected lemma convex.interior {s : set E} (hs : convex 𝕜 s) : convex 𝕜 (interior s) :=
convex_iff_open_segment_subset.mpr $ λ x hx y hy,
  hs.open_segment_closure_interior_subset_interior (interior_subset_closure hx) hy

/-- In a topological vector space, the closure of a convex set is convex. -/
protected lemma convex.closure {s : set E} (hs : convex 𝕜 s) : convex 𝕜 (closure s) :=
λ x hx y hy a b ha hb hab,
let f : E → E → E := λ x' y', a • x' + b • y' in
have hf : continuous (function.uncurry f),
  from (continuous_fst.const_smul _).add (continuous_snd.const_smul _),
show f x y ∈ closure s,
  from map_mem_closure₂ hf hx hy (λ x' hx' y' hy', hs hx' hy' ha hb hab)

open affine_map

/-- A convex set `s` is strictly convex provided that for any two distinct points of
`s \ interior s`, the line passing through these points has nonempty intersection with
`interior s`. -/
protected lemma convex.strict_convex' {s : set E} (hs : convex 𝕜 s)
  (h : (s \ interior s).pairwise $ λ x y, ∃ c : 𝕜, line_map x y c ∈ interior s) :
  strict_convex 𝕜 s :=
begin
  refine strict_convex_iff_open_segment_subset.2 _,
  intros x hx y hy hne,
  by_cases hx' : x ∈ interior s, { exact hs.open_segment_interior_self_subset_interior hx' hy },
  by_cases hy' : y ∈ interior s, { exact hs.open_segment_self_interior_subset_interior hx hy' },
  rcases h ⟨hx, hx'⟩ ⟨hy, hy'⟩ hne with ⟨c, hc⟩,
  refine (open_segment_subset_union x y ⟨c, rfl⟩).trans (insert_subset.2 ⟨hc, union_subset _ _⟩),
  exacts [hs.open_segment_self_interior_subset_interior hx hc,
    hs.open_segment_interior_self_subset_interior hc hy]
end

/-- A convex set `s` is strictly convex provided that for any two distinct points `x`, `y` of
`s \ interior s`, the segment with endpoints `x`, `y` has nonempty intersection with
`interior s`. -/
protected lemma convex.strict_convex {s : set E} (hs : convex 𝕜 s)
  (h : (s \ interior s).pairwise $ λ x y, ([x -[𝕜] y] \ frontier s).nonempty) :
  strict_convex 𝕜 s :=
begin
  refine (hs.strict_convex' $ h.imp_on $ λ x hx y hy hne, _),
  simp only [segment_eq_image_line_map, ← self_diff_frontier],
  rintro ⟨_, ⟨⟨c, hc, rfl⟩, hcs⟩⟩,
  refine ⟨c, hs.segment_subset hx.1 hy.1 _, hcs⟩,
  exact (segment_eq_image_line_map 𝕜 x y).symm ▸ mem_image_of_mem _ hc
end

end has_continuous_const_smul

section has_continuous_smul

variables [add_comm_group E] [module ℝ E] [topological_space E]
  [topological_add_group E] [has_continuous_smul ℝ E]

/-- Convex hull of a finite set is compact. -/
lemma set.finite.compact_convex_hull {s : set E} (hs : s.finite) :
  is_compact (convex_hull ℝ s) :=
begin
  rw [hs.convex_hull_eq_image],
  apply (is_compact_std_simplex _).image,
  haveI := hs.fintype,
  apply linear_map.continuous_on_pi
end

/-- Convex hull of a finite set is closed. -/
lemma set.finite.is_closed_convex_hull [t2_space E] {s : set E} (hs : s.finite) :
  is_closed (convex_hull ℝ s) :=
hs.compact_convex_hull.is_closed

open affine_map

/-- If we dilate the interior of a convex set about a point in its interior by a scale `t > 1`,
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
lemma convex.closure_subset_image_homothety_interior_of_one_lt {s : set E} (hs : convex ℝ s)
  {x : E} (hx : x ∈ interior s) (t : ℝ) (ht : 1 < t) :
  closure s ⊆ homothety x t '' interior s :=
begin
  intros y hy,
  have hne : t ≠ 0, from (one_pos.trans ht).ne',
  refine ⟨homothety x t⁻¹ y, hs.open_segment_interior_closure_subset_interior hx hy _,
    (affine_equiv.homothety_units_mul_hom x (units.mk0 t hne)).apply_symm_apply y⟩,
  rw [open_segment_eq_image_line_map, ← inv_one, ← inv_Ioi (zero_lt_one' ℝ), ← image_inv,
    image_image, homothety_eq_line_map],
  exact mem_image_of_mem _ ht
end

/-- If we dilate a convex set about a point in its interior by a scale `t > 1`, the interior of
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
lemma convex.closure_subset_interior_image_homothety_of_one_lt {s : set E} (hs : convex ℝ s)
  {x : E} (hx : x ∈ interior s) (t : ℝ) (ht : 1 < t) :
  closure s ⊆ interior (homothety x t '' s) :=
(hs.closure_subset_image_homothety_interior_of_one_lt hx t ht).trans $
  (homothety_is_open_map x t (one_pos.trans ht).ne').image_interior_subset _

/-- If we dilate a convex set about a point in its interior by a scale `t > 1`, the interior of
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
lemma convex.subset_interior_image_homothety_of_one_lt {s : set E} (hs : convex ℝ s)
  {x : E} (hx : x ∈ interior s) (t : ℝ) (ht : 1 < t) :
  s ⊆ interior (homothety x t '' s) :=
subset_closure.trans $ hs.closure_subset_interior_image_homothety_of_one_lt hx t ht

/-- A nonempty convex set is path connected. -/
protected lemma convex.is_path_connected {s : set E} (hconv : convex ℝ s) (hne : s.nonempty) :
  is_path_connected s :=
begin
  refine is_path_connected_iff.mpr ⟨hne, _⟩,
  intros x x_in y y_in,
  have H := hconv.segment_subset x_in y_in,
  rw segment_eq_image_line_map at H,
  exact joined_in.of_line affine_map.line_map_continuous.continuous_on (line_map_apply_zero _ _)
    (line_map_apply_one _ _) H
end

/-- A nonempty convex set is connected. -/
protected lemma convex.is_connected {s : set E} (h : convex ℝ s) (hne : s.nonempty) :
  is_connected s :=
(h.is_path_connected hne).is_connected

/-- A convex set is preconnected. -/
protected lemma convex.is_preconnected {s : set E} (h : convex ℝ s) : is_preconnected s :=
s.eq_empty_or_nonempty.elim (λ h, h.symm ▸ is_preconnected_empty)
  (λ hne, (h.is_connected hne).is_preconnected)

/--
Every topological vector space over ℝ is path connected.

Not an instance, because it creates enormous TC subproblems (turn on `pp.all`).
-/
protected lemma topological_add_group.path_connected : path_connected_space E :=
path_connected_space_iff_univ.mpr $ convex_univ.is_path_connected ⟨(0 : E), trivial⟩

end has_continuous_smul
