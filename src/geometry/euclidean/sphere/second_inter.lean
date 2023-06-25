/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import geometry.euclidean.sphere.basic

/-!
# Second intersection of a sphere and a line

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines and proves basic results about the second intersection of a sphere with a line
through a point on that sphere.

## Main definitions

* `euclidean_geometry.sphere.second_inter` is the second intersection of a sphere with a line
  through a point on that sphere.

-/

noncomputable theory
open_locale real_inner_product_space

namespace euclidean_geometry

variables {V : Type*} {P : Type*}
  [normed_add_comm_group V] [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P]
include V

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
  have hv' : ⟪v, v⟫ ≠ 0 := inner_self_ne_zero.2 hv,
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

end euclidean_geometry
