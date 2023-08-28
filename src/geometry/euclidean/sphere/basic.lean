/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import analysis.convex.strict_convex_between
import geometry.euclidean.basic

/-!
# Spheres

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines and proves basic results about spheres and cospherical sets of points in
Euclidean affine spaces.

## Main definitions

* `euclidean_geometry.sphere` bundles a `center` and a `radius`.

* `euclidean_geometry.cospherical` is the property of a set of points being equidistant from some
  point.

* `euclidean_geometry.concyclic` is the property of a set of points being cospherical and
  coplanar.

-/

noncomputable theory
open_locale real_inner_product_space

namespace euclidean_geometry

variables {V : Type*} (P : Type*)

open finite_dimensional

/-- A `sphere P` bundles a `center` and `radius`. This definition does not require the radius to
be positive; that should be given as a hypothesis to lemmas that require it. -/
@[ext] structure sphere [metric_space P] :=
(center : P)
(radius : ℝ)

variables {P}

section metric_space
variables [metric_space P]

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

/-- The empty set is cospherical. -/
lemma cospherical_empty [nonempty P] : cospherical (∅ : set P) :=
let ⟨p⟩ := ‹nonempty P› in ⟨p, 0, λ p, false.elim⟩

/-- A single point is cospherical. -/
lemma cospherical_singleton (p : P) : cospherical ({p} : set P) :=
begin
  use p,
  simp
end

end metric_space

section normed_space
variables [normed_add_comm_group V] [normed_space ℝ V] [metric_space P] [normed_add_torsor V P]
include V

/-- Two points are cospherical. -/
lemma cospherical_pair (p₁ p₂ : P) : cospherical ({p₁, p₂} : set P) :=
⟨midpoint ℝ p₁ p₂, ‖(2 : ℝ)‖⁻¹ * dist p₁ p₂, begin
  rintros p (rfl | rfl | _),
  { rw [dist_comm, dist_midpoint_left] },
  { rw [dist_comm, dist_midpoint_right] }
end⟩

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

end normed_space

section euclidean_space
variables
  [normed_add_comm_group V] [inner_product_space ℝ V] [metric_space P] [normed_add_torsor V P]
include V

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

end euclidean_space

end euclidean_geometry
