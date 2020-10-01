/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import geometry.euclidean.circumcenter

noncomputable theory
open_locale big_operators
open_locale classical
open_locale real
open_locale real_inner_product_space

/-!
# Monge point and orthocenter

This file defines the orthocenter of a triangle, via its n-dimensional
generalization, the Monge point of a simplex.

## Main definitions

* `monge_point` is the Monge point of a simplex, defined in terms of
  its position on the Euler line and then shown to be the point of
  concurrence of the Monge planes.

* `monge_plane` is a Monge plane of an (n+2)-simplex, which is the
  (n+1)-dimensional affine subspace of the subspace spanned by the
  simplex that passes through the centroid of an n-dimensional face
  and is orthogonal to the opposite edge (in 2 dimensions, this is the
  same as an altitude).

* `altitude` is the line that passes through a vertex of a simplex and
  is orthogonal to the opposite face.

* `orthocenter` is defined, for the case of a triangle, to be the same
  as its Monge point, then shown to be the point of concurrence of the
  altitudes.

## References

* https://en.wikipedia.org/wiki/Altitude_(triangle)
* https://en.wikipedia.org/wiki/Monge_point
* Małgorzata Buba-Brzozowa, [The Monge Point and the 3(n+1) Point
  Sphere of an
  n-Simplex](https://pdfs.semanticscholar.org/6f8b/0f623459c76dac2e49255737f8f0f4725d16.pdf)

-/

namespace affine

namespace simplex

open finset affine_subspace euclidean_geometry points_with_circumcenter_index

variables {V : Type*} {P : Type*} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P]
include V

/-- The Monge point of a simplex (in 2 or more dimensions) is a
generalization of the orthocenter of a triangle.  It is defined to be
the intersection of the Monge planes, where a Monge plane is the
(n-1)-dimensional affine subspace of the subspace spanned by the
simplex that passes through the centroid of an (n-2)-dimensional face
and is orthogonal to the opposite edge (in 2 dimensions, this is the
same as an altitude).  The circumcenter O, centroid G and Monge point
M are collinear in that order on the Euler line, with OG : GM = (n-1)
: 2.  Here, we use that ratio to define the Monge point (so resulting
in a point that equals the centroid in 0 or 1 dimensions), and then
show in subsequent lemmas that the point so defined lies in the Monge
planes and is their unique point of intersection. -/
def monge_point {n : ℕ} (s : simplex ℝ P n) : P :=
(((n + 1 : ℕ) : ℝ) / (((n - 1) : ℕ) : ℝ)) •
  ((univ : finset (fin (n + 1))).centroid ℝ s.points -ᵥ s.circumcenter) +ᵥ
  s.circumcenter

/-- The position of the Monge point in relation to the circumcenter
and centroid. -/
lemma monge_point_eq_smul_vsub_vadd_circumcenter {n : ℕ} (s : simplex ℝ P n) :
  s.monge_point = (((n + 1 : ℕ) : ℝ) / (((n - 1) : ℕ) : ℝ)) •
    ((univ : finset (fin (n + 1))).centroid ℝ s.points -ᵥ s.circumcenter) +ᵥ
    s.circumcenter :=
rfl

/-- The Monge point lies in the affine span. -/
lemma monge_point_mem_affine_span {n : ℕ} (s : simplex ℝ P n) :
  s.monge_point ∈ affine_span ℝ (set.range s.points) :=
smul_vsub_vadd_mem _ _
  (centroid_mem_affine_span_of_card_eq_add_one ℝ _ (card_fin (n + 1)))
  s.circumcenter_mem_affine_span
  s.circumcenter_mem_affine_span

/-- Two simplices with the same points have the same Monge point. -/
lemma monge_point_eq_of_range_eq {n : ℕ} {s₁ s₂ : simplex ℝ P n}
  (h : set.range s₁.points = set.range s₂.points) : s₁.monge_point = s₂.monge_point :=
by simp_rw [monge_point_eq_smul_vsub_vadd_circumcenter, centroid_eq_of_range_eq h,
            circumcenter_eq_of_range_eq h]

omit V

/-- The weights for the Monge point of an (n+2)-simplex, in terms of
`points_with_circumcenter`. -/
def monge_point_weights_with_circumcenter (n : ℕ) : points_with_circumcenter_index (n + 2) → ℝ
| (point_index i) := (((n + 1) : ℕ) : ℝ)⁻¹
| circumcenter_index := (-2 / (((n + 1) : ℕ) : ℝ))

/-- `monge_point_weights_with_circumcenter` sums to 1. -/
@[simp] lemma sum_monge_point_weights_with_circumcenter (n : ℕ) :
  ∑ i, monge_point_weights_with_circumcenter n i = 1 :=
begin
  simp_rw [sum_points_with_circumcenter, monge_point_weights_with_circumcenter, sum_const,
           card_fin, nsmul_eq_mul],
  have hn1 : (n + 1 : ℝ) ≠ 0,
  { exact_mod_cast nat.succ_ne_zero _ },
  field_simp [hn1],
  ring
end

include V

/-- The Monge point of an (n+2)-simplex, in terms of
`points_with_circumcenter`. -/
lemma monge_point_eq_affine_combination_of_points_with_circumcenter {n : ℕ}
  (s : simplex ℝ P (n + 2)) :
  s.monge_point = (univ : finset (points_with_circumcenter_index (n + 2))).affine_combination
    s.points_with_circumcenter (monge_point_weights_with_circumcenter n) :=
begin
  rw [monge_point_eq_smul_vsub_vadd_circumcenter,
      centroid_eq_affine_combination_of_points_with_circumcenter,
      circumcenter_eq_affine_combination_of_points_with_circumcenter,
      affine_combination_vsub, ←linear_map.map_smul,
      weighted_vsub_vadd_affine_combination],
  congr' with i,
  rw [pi.add_apply, pi.smul_apply, smul_eq_mul, pi.sub_apply],
  have hn1 : (n + 1 : ℝ) ≠ 0,
  { exact_mod_cast nat.succ_ne_zero _ },
  cases i;
    simp_rw [centroid_weights_with_circumcenter, circumcenter_weights_with_circumcenter,
             monge_point_weights_with_circumcenter];
    rw [nat.add_sub_assoc (dec_trivial : 1 ≤ 2), (dec_trivial : 2 - 1 = 1)],
  { rw [if_pos (mem_univ _), sub_zero, add_zero, card_fin],
    have hn3 : (n + 2 + 1 : ℝ) ≠ 0,
    { exact_mod_cast nat.succ_ne_zero _ },
    field_simp [hn1, hn3] },
  { field_simp [hn1],
    ring }
end

omit V

/-- The weights for the Monge point of an (n+2)-simplex, minus the
centroid of an n-dimensional face, in terms of
`points_with_circumcenter`.  This definition is only valid when `i₁ ≠ i₂`. -/
def monge_point_vsub_face_centroid_weights_with_circumcenter {n : ℕ} (i₁ i₂ : fin (n + 3)) :
  points_with_circumcenter_index (n + 2) → ℝ
| (point_index i) := if i = i₁ ∨ i = i₂ then (((n + 1) : ℕ) : ℝ)⁻¹ else 0
| circumcenter_index := (-2 / (((n + 1) : ℕ) : ℝ))

/-- `monge_point_vsub_face_centroid_weights_with_circumcenter` is the
result of subtracting `centroid_weights_with_circumcenter` from
`monge_point_weights_with_circumcenter`. -/
lemma monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub {n : ℕ}
  {i₁ i₂ : fin (n + 3)} (h : i₁ ≠ i₂) :
  monge_point_vsub_face_centroid_weights_with_circumcenter i₁ i₂ =
    monge_point_weights_with_circumcenter n -
      centroid_weights_with_circumcenter ({i₁, i₂}ᶜ) :=
begin
  ext i,
  cases i,
  { rw [pi.sub_apply, monge_point_weights_with_circumcenter, centroid_weights_with_circumcenter,
        monge_point_vsub_face_centroid_weights_with_circumcenter],
    have hu : card ({i₁, i₂}ᶜ : finset (fin (n + 3))) = n + 1,
    { simp [card_compl, fintype.card_fin, h] },
    rw hu,
    by_cases hi : i = i₁ ∨ i = i₂;
      simp [compl_eq_univ_sdiff, hi] },
  { simp [monge_point_weights_with_circumcenter, centroid_weights_with_circumcenter,
          monge_point_vsub_face_centroid_weights_with_circumcenter] }
end

/-- `monge_point_vsub_face_centroid_weights_with_circumcenter` sums to 0. -/
@[simp] lemma sum_monge_point_vsub_face_centroid_weights_with_circumcenter {n : ℕ}
  {i₁ i₂ : fin (n + 3)} (h : i₁ ≠ i₂) :
  ∑ i, monge_point_vsub_face_centroid_weights_with_circumcenter i₁ i₂ i = 0 :=
begin
  rw monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub h,
  simp_rw [pi.sub_apply, sum_sub_distrib, sum_monge_point_weights_with_circumcenter],
  rw [sum_centroid_weights_with_circumcenter, sub_self],
  simp [←card_pos, card_compl, h]
end

include V

/-- The Monge point of an (n+2)-simplex, minus the centroid of an
n-dimensional face, in terms of `points_with_circumcenter`. -/
lemma monge_point_vsub_face_centroid_eq_weighted_vsub_of_points_with_circumcenter {n : ℕ}
  (s : simplex ℝ P (n + 2)) {i₁ i₂ : fin (n + 3)} (h : i₁ ≠ i₂) :
  s.monge_point -ᵥ ({i₁, i₂}ᶜ : finset (fin (n + 3))).centroid ℝ s.points =
    (univ : finset (points_with_circumcenter_index (n + 2))).weighted_vsub
      s.points_with_circumcenter (monge_point_vsub_face_centroid_weights_with_circumcenter i₁ i₂) :=
by simp_rw [monge_point_eq_affine_combination_of_points_with_circumcenter,
            centroid_eq_affine_combination_of_points_with_circumcenter,
            affine_combination_vsub,
            monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub h]

/-- The Monge point of an (n+2)-simplex, minus the centroid of an
n-dimensional face, is orthogonal to the difference of the two
vertices not in that face. -/
lemma inner_monge_point_vsub_face_centroid_vsub {n : ℕ} (s : simplex ℝ P (n + 2))
  {i₁ i₂ : fin (n + 3)} (h : i₁ ≠ i₂) :
  ⟪s.monge_point -ᵥ ({i₁, i₂}ᶜ : finset (fin (n + 3))).centroid ℝ s.points,
        s.points i₁ -ᵥ s.points i₂⟫ = 0 :=
begin
  simp_rw [monge_point_vsub_face_centroid_eq_weighted_vsub_of_points_with_circumcenter s h,
           point_eq_affine_combination_of_points_with_circumcenter,
           affine_combination_vsub],
  have hs : ∑ i, (point_weights_with_circumcenter i₁ - point_weights_with_circumcenter i₂) i = 0,
  { simp },
  rw [inner_weighted_vsub _ (sum_monge_point_vsub_face_centroid_weights_with_circumcenter h) _ hs,
      sum_points_with_circumcenter, points_with_circumcenter_eq_circumcenter],
  simp only [monge_point_vsub_face_centroid_weights_with_circumcenter,
             points_with_circumcenter_point],
  let fs : finset (fin (n + 3)) := {i₁, i₂},
  have hfs : ∀ i : fin (n + 3),
    i ∉ fs → (i ≠ i₁ ∧ i ≠ i₂),
  { intros i hi,
    split ; { intro hj, simpa [←hj] using hi } },
  rw ←sum_subset fs.subset_univ _,
  { simp_rw [sum_points_with_circumcenter, points_with_circumcenter_eq_circumcenter,
             points_with_circumcenter_point, pi.sub_apply, point_weights_with_circumcenter],
    rw [←sum_subset fs.subset_univ _],
    { simp_rw [sum_insert (not_mem_singleton.2 h), sum_singleton],
      repeat { rw ←sum_subset fs.subset_univ _ },
      { simp_rw [sum_insert (not_mem_singleton.2 h), sum_singleton],
        simp [h, h.symm, dist_comm (s.points i₁)] },
      all_goals { intros i hu hi, simp [hfs i hi] } },
    { intros i hu hi,
      simp [hfs i hi, point_weights_with_circumcenter] } },
  { intros i hu hi,
    simp [hfs i hi] }
end

/-- A Monge plane of an (n+2)-simplex is the (n+1)-dimensional affine
subspace of the subspace spanned by the simplex that passes through
the centroid of an n-dimensional face and is orthogonal to the
opposite edge (in 2 dimensions, this is the same as an altitude).
This definition is only intended to be used when `i₁ ≠ i₂`. -/
def monge_plane {n : ℕ} (s : simplex ℝ P (n + 2)) (i₁ i₂ : fin (n + 3)) :
  affine_subspace ℝ P :=
mk' (({i₁, i₂}ᶜ : finset (fin (n + 3))).centroid ℝ s.points) (submodule.span ℝ {s.points i₁ -ᵥ s.points i₂}).orthogonal ⊓
  affine_span ℝ (set.range s.points)

/-- The definition of a Monge plane. -/
lemma monge_plane_def {n : ℕ} (s : simplex ℝ P (n + 2)) (i₁ i₂ : fin (n + 3)) :
  s.monge_plane i₁ i₂ = mk' (({i₁, i₂}ᶜ : finset (fin (n + 3))).centroid ℝ s.points)
                            (submodule.span ℝ {s.points i₁ -ᵥ s.points i₂}).orthogonal ⊓
                          affine_span ℝ (set.range s.points) :=
rfl

/-- The Monge plane associated with vertices `i₁` and `i₂` equals that
associated with `i₂` and `i₁`. -/
lemma monge_plane_comm {n : ℕ} (s : simplex ℝ P (n + 2)) (i₁ i₂ : fin (n + 3)) :
  s.monge_plane i₁ i₂ = s.monge_plane i₂ i₁ :=
begin
  simp_rw monge_plane_def,
  congr' 3,
  { congr' 1,
    exact insert_singleton_comm _ _ },
  { ext,
    simp_rw submodule.mem_span_singleton,
    split,
    all_goals { rintros ⟨r, rfl⟩, use -r, rw [neg_smul, ←smul_neg, neg_vsub_eq_vsub_rev] } }
end

/-- The Monge point lies in the Monge planes. -/
lemma monge_point_mem_monge_plane {n : ℕ} (s : simplex ℝ P (n + 2)) {i₁ i₂ : fin (n + 3)}
    (h : i₁ ≠ i₂) : s.monge_point ∈ s.monge_plane i₁ i₂ :=
begin
  rw [monge_plane_def, mem_inf_iff, ←vsub_right_mem_direction_iff_mem (self_mem_mk' _ _),
      direction_mk', submodule.mem_orthogonal'],
  refine ⟨_, s.monge_point_mem_affine_span⟩,
  intros v hv,
  rcases submodule.mem_span_singleton.mp hv with ⟨r, rfl⟩,
  rw [inner_smul_right, s.inner_monge_point_vsub_face_centroid_vsub h, mul_zero]
end

-- This doesn't actually need the `i₁ ≠ i₂` hypothesis, but it's
-- convenient for the proof and `monge_plane` isn't intended to be
-- useful without that hypothesis.
/-- The direction of a Monge plane. -/
lemma direction_monge_plane {n : ℕ} (s : simplex ℝ P (n + 2)) {i₁ i₂ : fin (n + 3)} (h : i₁ ≠ i₂) :
  (s.monge_plane i₁ i₂).direction = (submodule.span ℝ {s.points i₁ -ᵥ s.points i₂}).orthogonal ⊓
    vector_span ℝ (set.range s.points) :=
by rw [monge_plane_def, direction_inf_of_mem_inf (s.monge_point_mem_monge_plane h), direction_mk',
       direction_affine_span]

/-- The Monge point is the only point in all the Monge planes from any
one vertex. -/
lemma eq_monge_point_of_forall_mem_monge_plane {n : ℕ} {s : simplex ℝ P (n + 2)}
  {i₁ : fin (n + 3)} {p : P} (h : ∀ i₂, i₁ ≠ i₂ → p ∈ s.monge_plane i₁ i₂) :
  p = s.monge_point :=
begin
  rw ←@vsub_eq_zero_iff_eq V,
  have h' : ∀ i₂, i₁ ≠ i₂ → p -ᵥ s.monge_point ∈
    (submodule.span ℝ {s.points i₁ -ᵥ s.points i₂}).orthogonal ⊓ vector_span ℝ (set.range s.points),
  { intros i₂ hne,
    rw [←s.direction_monge_plane hne,
        vsub_right_mem_direction_iff_mem (s.monge_point_mem_monge_plane hne)],
    exact h i₂ hne },
  have hi : p -ᵥ s.monge_point ∈ ⨅ (i₂ : {i // i₁ ≠ i}),
    (submodule.span ℝ ({s.points i₁ -ᵥ s.points i₂}: set V)).orthogonal,
  { rw submodule.mem_infi,
    exact λ i, (submodule.mem_inf.1 (h' i i.property)).1 },
  rw [submodule.infi_orthogonal, ←submodule.span_Union] at hi,
  have hu : (⋃ (i : {i // i₁ ≠ i}), ({s.points i₁ -ᵥ s.points i} : set V)) =
    (-ᵥ) (s.points i₁) '' (s.points '' (set.univ \ {i₁})),
  { rw [set.image_image],
    ext x,
    simp_rw [set.mem_Union, set.mem_image, set.mem_singleton_iff, set.mem_diff_singleton],
    split,
    { rintros ⟨i, rfl⟩,
      use [i, ⟨set.mem_univ _, i.property.symm⟩] },
    { rintros ⟨i, ⟨hiu, hi⟩, rfl⟩,
      use [⟨i, hi.symm⟩, rfl] } },
  rw [hu, ←vector_span_image_eq_span_vsub_set_left_ne ℝ _ (set.mem_univ _),
      set.image_univ] at hi,
  have hv : p -ᵥ s.monge_point ∈ vector_span ℝ (set.range s.points),
  { let s₁ : finset (fin (n + 3)) := univ.erase i₁,
    obtain ⟨i₂, h₂⟩ :=
      card_pos.1 (show 0 < card s₁, by simp [card_erase_of_mem]),
    have h₁₂ : i₁ ≠ i₂ := (ne_of_mem_erase h₂).symm,
    exact (submodule.mem_inf.1 (h' i₂ h₁₂)).2 },
  exact submodule.disjoint_def.1 ((vector_span ℝ (set.range s.points)).orthogonal_disjoint)
    _ hv hi,
end

/-- An altitude of a simplex is the line that passes through a vertex
and is orthogonal to the opposite face. -/
def altitude {n : ℕ} (s : simplex ℝ P (n + 1)) (i : fin (n + 2)) : affine_subspace ℝ P :=
mk' (s.points i) (affine_span ℝ (s.points '' ↑(univ.erase i))).direction.orthogonal ⊓
  affine_span ℝ (set.range s.points)

/-- The definition of an altitude. -/
lemma altitude_def {n : ℕ} (s : simplex ℝ P (n + 1)) (i : fin (n + 2)) :
  s.altitude i = mk' (s.points i)
                     (affine_span ℝ (s.points '' ↑(univ.erase i))).direction.orthogonal ⊓
    affine_span ℝ (set.range s.points) :=
rfl

/-- A vertex lies in the corresponding altitude. -/
lemma mem_altitude {n : ℕ} (s : simplex ℝ P (n + 1)) (i : fin (n + 2)) :
  s.points i ∈ s.altitude i :=
(mem_inf_iff _ _ _).2 ⟨self_mem_mk' _ _, mem_affine_span ℝ (set.mem_range_self _)⟩

/-- The direction of an altitude. -/
lemma direction_altitude {n : ℕ} (s : simplex ℝ P (n + 1)) (i : fin (n + 2)) :
  (s.altitude i).direction = (vector_span ℝ (s.points '' ↑(finset.univ.erase i))).orthogonal ⊓
    vector_span ℝ (set.range s.points) :=
by rw [altitude_def,
       direction_inf_of_mem (self_mem_mk' (s.points i) _)
         (mem_affine_span ℝ (set.mem_range_self _)), direction_mk', direction_affine_span,
       direction_affine_span]

/-- The vector span of the opposite face lies in the direction
orthogonal to an altitude. -/
lemma vector_span_le_altitude_direction_orthogonal  {n : ℕ} (s : simplex ℝ P (n + 1))
    (i : fin (n + 2)) :
  vector_span ℝ (s.points '' ↑(finset.univ.erase i)) ≤ (s.altitude i).direction.orthogonal :=
begin
  rw direction_altitude,
  exact le_trans
    (vector_span ℝ (s.points '' ↑(finset.univ.erase i))).le_orthogonal_orthogonal
    (submodule.orthogonal_le inf_le_left)
end

open finite_dimensional

/-- An altitude is finite-dimensional. -/
instance finite_dimensional_direction_altitude {n : ℕ} (s : simplex ℝ P (n + 1))
  (i : fin (n + 2)) : finite_dimensional ℝ ((s.altitude i).direction) :=
begin
  rw direction_altitude,
  apply_instance
end

/-- An altitude is one-dimensional (i.e., a line). -/
@[simp] lemma findim_direction_altitude {n : ℕ} (s : simplex ℝ P (n + 1)) (i : fin (n + 2)) :
  findim ℝ ((s.altitude i).direction) = 1 :=
begin
  rw direction_altitude,
  have h := submodule.findim_add_inf_findim_orthogonal
    (vector_span_mono ℝ (set.image_subset_range s.points ↑(univ.erase i))),
  have hc : card (univ.erase i) = n + 1, { rw card_erase_of_mem (mem_univ _), simp },
  rw [findim_vector_span_of_affine_independent s.independent (fintype.card_fin _),
      findim_vector_span_image_finset_of_affine_independent s.independent hc] at h,
  simpa using h
end

/-- A line through a vertex is the altitude through that vertex if and
only if it is orthogonal to the opposite face. -/
lemma affine_span_insert_singleton_eq_altitude_iff {n : ℕ} (s : simplex ℝ P (n + 1))
    (i : fin (n + 2)) (p : P) :
  affine_span ℝ {p, s.points i} = s.altitude i ↔ (p ≠ s.points i ∧
    p ∈ affine_span ℝ (set.range s.points) ∧
    p -ᵥ s.points i ∈ (affine_span ℝ (s.points '' ↑(finset.univ.erase i))).direction.orthogonal) :=
begin
  rw [eq_iff_direction_eq_of_mem
        (mem_affine_span ℝ (set.mem_insert_of_mem _ (set.mem_singleton _))) (s.mem_altitude _),
      ←vsub_right_mem_direction_iff_mem (mem_affine_span ℝ (set.mem_range_self i)) p,
      direction_affine_span, direction_affine_span, direction_affine_span],
  split,
  { intro h,
    split,
    { intro heq,
      rw [heq, set.pair_eq_singleton, vector_span_singleton] at h,
      have hd : findim ℝ (s.altitude i).direction = 0,
      { rw [←h, findim_bot] },
      simpa using hd },
    { rw [←submodule.mem_inf, inf_comm, ←direction_altitude, ←h],
      exact vsub_mem_vector_span ℝ (set.mem_insert _ _)
                                   (set.mem_insert_of_mem _ (set.mem_singleton _)) } },
  { rintro ⟨hne, h⟩,
    rw [←submodule.mem_inf, inf_comm, ←direction_altitude] at h,
    rw [vector_span_eq_span_vsub_set_left_ne ℝ (set.mem_insert _ _),
        set.insert_diff_of_mem _ (set.mem_singleton _),
        set.diff_singleton_eq_self (λ h, hne (set.mem_singleton_iff.1 h)), set.image_singleton],
    refine eq_of_le_of_findim_eq _ _,
    { rw submodule.span_le,
      simpa using h },
    { rw [findim_direction_altitude, findim_span_set_eq_card],
      { simp },
      { refine linear_independent_singleton _,
        simpa using hne } } }
end

end simplex

namespace triangle

open euclidean_geometry finset simplex affine_subspace finite_dimensional

variables {V : Type*} {P : Type*} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P]
include V

/-- The orthocenter of a triangle is the intersection of its
altitudes.  It is defined here as the 2-dimensional case of the
Monge point. -/
def orthocenter (t : triangle ℝ P) : P := t.monge_point

/-- The orthocenter equals the Monge point. -/
lemma orthocenter_eq_monge_point (t : triangle ℝ P) : t.orthocenter = t.monge_point := rfl

/-- The position of the orthocenter in relation to the circumcenter
and centroid. -/
lemma orthocenter_eq_smul_vsub_vadd_circumcenter (t : triangle ℝ P) :
  t.orthocenter = (3 : ℝ) •
    ((univ : finset (fin 3)).centroid ℝ t.points -ᵥ t.circumcenter : V) +ᵥ t.circumcenter :=
begin
  rw [orthocenter_eq_monge_point, monge_point_eq_smul_vsub_vadd_circumcenter],
  norm_num
end

/-- The orthocenter lies in the affine span. -/
lemma orthocenter_mem_affine_span (t : triangle ℝ P) :
  t.orthocenter ∈ affine_span ℝ (set.range t.points) :=
t.monge_point_mem_affine_span

/-- Two triangles with the same points have the same orthocenter. -/
lemma orthocenter_eq_of_range_eq {t₁ t₂ : triangle ℝ P}
  (h : set.range t₁.points = set.range t₂.points) : t₁.orthocenter = t₂.orthocenter :=
monge_point_eq_of_range_eq h

/-- In the case of a triangle, altitudes are the same thing as Monge
planes. -/
lemma altitude_eq_monge_plane (t : triangle ℝ P) {i₁ i₂ i₃ : fin 3} (h₁₂ : i₁ ≠ i₂)
  (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) : t.altitude i₁ = t.monge_plane i₂ i₃ :=
begin
  have hs : ({i₂, i₃}ᶜ : finset (fin 3)) = {i₁}, by dec_trivial!,
  have he : univ.erase i₁ = {i₂, i₃}, by dec_trivial!,
  rw [monge_plane_def, altitude_def, direction_affine_span, hs, he, centroid_singleton,
      coe_insert, coe_singleton,
      vector_span_image_eq_span_vsub_set_left_ne ℝ _ (set.mem_insert i₂ _)],
  simp [h₂₃, submodule.span_insert_eq_span]
end

/-- The orthocenter lies in the altitudes. -/
lemma orthocenter_mem_altitude (t : triangle ℝ P) {i₁ : fin 3} :
  t.orthocenter ∈ t.altitude i₁ :=
begin
  obtain ⟨i₂, i₃, h₁₂, h₂₃, h₁₃⟩ : ∃ i₂ i₃, i₁ ≠ i₂ ∧ i₂ ≠ i₃ ∧ i₁ ≠ i₃, by dec_trivial!,
  rw [orthocenter_eq_monge_point, t.altitude_eq_monge_plane h₁₂ h₁₃ h₂₃],
  exact t.monge_point_mem_monge_plane h₂₃
end

/-- The orthocenter is the only point lying in any two of the
altitudes. -/
lemma eq_orthocenter_of_forall_mem_altitude {t : triangle ℝ P} {i₁ i₂ : fin 3} {p : P}
  (h₁₂ : i₁ ≠ i₂) (h₁ : p ∈ t.altitude i₁) (h₂ : p ∈ t.altitude i₂) : p = t.orthocenter :=
begin
  obtain ⟨i₃, h₂₃, h₁₃⟩ : ∃ i₃, i₂ ≠ i₃ ∧ i₁ ≠ i₃, { clear h₁ h₂, dec_trivial! },
  rw t.altitude_eq_monge_plane h₁₃ h₁₂ h₂₃.symm at h₁,
  rw t.altitude_eq_monge_plane h₂₃ h₁₂.symm h₁₃.symm at h₂,
  rw orthocenter_eq_monge_point,
  have ha : ∀ i, i₃ ≠ i → p ∈ t.monge_plane i₃ i,
  { intros i hi,
    have hi₁₂ : i₁ = i ∨ i₂ = i, { clear h₁ h₂, dec_trivial! },
    cases hi₁₂,
    { exact hi₁₂ ▸ h₂ },
    { exact hi₁₂ ▸ h₁ } },
  exact eq_monge_point_of_forall_mem_monge_plane ha
end

/-- The distance from the orthocenter to the reflection of the
circumcenter in a side equals the circumradius. -/
lemma dist_orthocenter_reflection_circumcenter (t : triangle ℝ P) {i₁ i₂ : fin 3} (h : i₁ ≠ i₂) :
  dist t.orthocenter (reflection (affine_span ℝ (t.points '' {i₁, i₂})) t.circumcenter) =
    t.circumradius :=
begin
  rw [←mul_self_inj_of_nonneg dist_nonneg t.circumradius_nonneg,
      t.reflection_circumcenter_eq_affine_combination_of_points_with_circumcenter h,
      t.orthocenter_eq_monge_point,
      monge_point_eq_affine_combination_of_points_with_circumcenter,
      dist_affine_combination t.points_with_circumcenter
        (sum_monge_point_weights_with_circumcenter _)
        (sum_reflection_circumcenter_weights_with_circumcenter h)],
  simp_rw [sum_points_with_circumcenter, pi.sub_apply, monge_point_weights_with_circumcenter,
           reflection_circumcenter_weights_with_circumcenter],
  have hu : ({i₁, i₂} : finset (fin 3)) ⊆ univ := subset_univ _,
  obtain ⟨i₃, hi₃, hi₃₁, hi₃₂⟩ :
    ∃ i₃, univ \ ({i₁, i₂} : finset (fin 3)) = {i₃} ∧ i₃ ≠ i₁ ∧ i₃ ≠ i₂, by dec_trivial!,
  simp_rw [←sum_sdiff hu, hi₃],
  simp [hi₃₁, hi₃₂],
  norm_num
end

/-- The distance from the orthocenter to the reflection of the
circumcenter in a side equals the circumradius, variant using a
`finset`. -/
lemma dist_orthocenter_reflection_circumcenter_finset (t : triangle ℝ P) {i₁ i₂ : fin 3}
    (h : i₁ ≠ i₂) :
  dist t.orthocenter (reflection (affine_span ℝ (t.points '' ↑({i₁, i₂} : finset (fin 3))))
                                 t.circumcenter) =
    t.circumradius :=
begin
  convert dist_orthocenter_reflection_circumcenter t h,
  simp
end

/-- The affine span of the orthocenter and a vertex is contained in
the altitude. -/
lemma affine_span_orthocenter_point_le_altitude (t : triangle ℝ P) (i : fin 3) :
  affine_span ℝ {t.orthocenter, t.points i} ≤ t.altitude i :=
begin
  refine span_points_subset_coe_of_subset_coe _,
  rw [set.insert_subset, set.singleton_subset_iff],
  exact ⟨t.orthocenter_mem_altitude, t.mem_altitude i⟩
end

/-- Suppose we are given a triangle `t₁`, and replace one of its
vertices by its orthocenter, yielding triangle `t₂` (with vertices not
necessarily listed in the same order).  Then an altitude of `t₂` from
a vertex that was not replaced is the corresponding side of `t₁`. -/
lemma altitude_replace_orthocenter_eq_affine_span {t₁ t₂ : triangle ℝ P} {i₁ i₂ i₃ j₁ j₂ j₃ : fin 3}
    (hi₁₂ : i₁ ≠ i₂) (hi₁₃ : i₁ ≠ i₃) (hi₂₃ : i₂ ≠ i₃) (hj₁₂ : j₁ ≠ j₂) (hj₁₃ : j₁ ≠ j₃)
    (hj₂₃ : j₂ ≠ j₃) (h₁ : t₂.points j₁ = t₁.orthocenter) (h₂ : t₂.points j₂ = t₁.points i₂)
    (h₃ : t₂.points j₃ = t₁.points i₃) :
  t₂.altitude j₂ = affine_span ℝ {t₁.points i₁, t₁.points i₂} :=
begin
  symmetry,
  rw [←h₂, t₂.affine_span_insert_singleton_eq_altitude_iff],
  rw [h₂],
  use (injective_of_affine_independent t₁.independent).ne hi₁₂,
  have he : affine_span ℝ (set.range t₂.points) = affine_span ℝ (set.range t₁.points),
  { refine ext_of_direction_eq _
      ⟨t₁.points i₃, mem_affine_span ℝ ⟨j₃, h₃⟩, mem_affine_span ℝ (set.mem_range_self _)⟩,
    refine eq_of_le_of_findim_eq (direction_le (span_points_subset_coe_of_subset_coe _)) _,
    { have hu : (finset.univ : finset (fin 3)) = {j₁, j₂, j₃}, { clear h₁ h₂ h₃, dec_trivial! },
      rw [←set.image_univ, ←finset.coe_univ, hu, finset.coe_insert, finset.coe_insert,
          finset.coe_singleton, set.image_insert_eq, set.image_insert_eq, set.image_singleton,
          h₁, h₂, h₃, set.insert_subset, set.insert_subset, set.singleton_subset_iff],
      exact ⟨t₁.orthocenter_mem_affine_span,
             mem_affine_span ℝ (set.mem_range_self _),
             mem_affine_span ℝ (set.mem_range_self _)⟩ },
    { rw [direction_affine_span, direction_affine_span,
          findim_vector_span_of_affine_independent t₁.independent (fintype.card_fin _),
          findim_vector_span_of_affine_independent t₂.independent (fintype.card_fin _)] } },
  rw he,
  use mem_affine_span ℝ (set.mem_range_self _),
  have hu : finset.univ.erase j₂ = {j₁, j₃}, { clear h₁ h₂ h₃, dec_trivial! },
  rw [hu, finset.coe_insert, finset.coe_singleton, set.image_insert_eq, set.image_singleton,
      h₁, h₃],
  have hle : (t₁.altitude i₃).direction.orthogonal ≤
    (affine_span ℝ ({t₁.orthocenter, t₁.points i₃} : set P)).direction.orthogonal :=
      submodule.orthogonal_le (direction_le (affine_span_orthocenter_point_le_altitude _ _)),
  refine hle ((t₁.vector_span_le_altitude_direction_orthogonal i₃) _),
  have hui : finset.univ.erase i₃ = {i₁, i₂}, { clear hle h₂ h₃, dec_trivial! },
  rw [hui, finset.coe_insert, finset.coe_singleton, set.image_insert_eq, set.image_singleton],
  refine vsub_mem_vector_span ℝ (set.mem_insert _ _)
    (set.mem_insert_of_mem _ (set.mem_singleton _))
end

/-- Suppose we are given a triangle `t₁`, and replace one of its
vertices by its orthocenter, yielding triangle `t₂` (with vertices not
necessarily listed in the same order).  Then the orthocenter of `t₂`
is the vertex of `t₁` that was replaced. -/
lemma orthocenter_replace_orthocenter_eq_point {t₁ t₂ : triangle ℝ P} {i₁ i₂ i₃ j₁ j₂ j₃ : fin 3}
    (hi₁₂ : i₁ ≠ i₂) (hi₁₃ : i₁ ≠ i₃) (hi₂₃ : i₂ ≠ i₃) (hj₁₂ : j₁ ≠ j₂) (hj₁₃ : j₁ ≠ j₃)
    (hj₂₃ : j₂ ≠ j₃) (h₁ : t₂.points j₁ = t₁.orthocenter) (h₂ : t₂.points j₂ = t₁.points i₂)
    (h₃ : t₂.points j₃ = t₁.points i₃) :
  t₂.orthocenter = t₁.points i₁ :=
begin
  refine (triangle.eq_orthocenter_of_forall_mem_altitude hj₂₃ _ _).symm,
  { rw altitude_replace_orthocenter_eq_affine_span hi₁₂ hi₁₃ hi₂₃ hj₁₂ hj₁₃ hj₂₃ h₁ h₂ h₃,
    exact mem_affine_span ℝ (set.mem_insert _ _) },
  { rw altitude_replace_orthocenter_eq_affine_span hi₁₃ hi₁₂ hi₂₃.symm hj₁₃ hj₁₂ hj₂₃.symm h₁ h₃ h₂,
    exact mem_affine_span ℝ (set.mem_insert _ _) }
end

end triangle

end affine
