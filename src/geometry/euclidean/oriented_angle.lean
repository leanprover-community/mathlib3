/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import analysis.inner_product_space.orientation
import analysis.inner_product_space.pi_L2
import analysis.special_functions.complex.circle

/-!
# Oriented angles.

This file defines oriented angles in real inner product spaces.

## Main definitions

* `orientation.oangle` is the oriented angle between two vectors with respect to an orientation.

* `orientation.rotation` is the rotation by an oriented angle with respect to an orientation.

## Implementation notes

The definitions here use the `real.angle` type, angles modulo `2 * π`. For some purposes,
angles modulo `π` are more convenient, because results are true for such angles with less
configuration dependence. Results that are only equalities modulo `π` can be represented
modulo `2 * π` as equalities of `(2 : ℤ) • θ`.

Definitions and results in the `orthonormal` namespace, with respect to a particular choice
of orthonormal basis, are mainly for use in setting up the API and proving that certain
definitions do not depend on the choice of basis for a given orientation. Applications should
generally use the definitions and results in the `orientation` namespace instead.

## References

* Evan Chen, Euclidean Geometry in Mathematical Olympiads.

-/

noncomputable theory

open_locale real

namespace orthonormal

variables {V : Type*} [inner_product_space ℝ V]
variables {b : basis (fin 2) ℝ V} (hb : orthonormal ℝ b)
include hb

/-- The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. -/
def oangle (x y : V) : real.angle :=
complex.arg ((complex.isometry_of_orthonormal hb).symm y /
  (complex.isometry_of_orthonormal hb).symm x)

/-- If the first vector passed to `oangle` is 0, the result is 0. -/
@[simp] lemma oangle_zero_left (x : V) : hb.oangle 0 x = 0 :=
by simp [oangle]

/-- If the second vector passed to `oangle` is 0, the result is 0. -/
@[simp] lemma oangle_zero_right (x : V) : hb.oangle x 0 = 0 :=
by simp [oangle]

/-- If the two vectors passed to `oangle` are the same, the result is 0. -/
@[simp] lemma oangle_self (x : V) : hb.oangle x x = 0 :=
begin
  by_cases h : x = 0;
    simp [oangle, h]
end

/-- Swapping the two vectors passed to `oangle` negates the angle. -/
lemma oangle_rev (x y : V) : hb.oangle y x = -hb.oangle x y :=
begin
  simp only [oangle],
  convert complex.arg_inv_coe_angle _,
  exact (inv_div _ _).symm
end

/-- Adding the angles between two vectors in each order results in 0. -/
@[simp] lemma oangle_add_oangle_rev (x y : V) : hb.oangle x y + hb.oangle y x = 0 :=
by simp [hb.oangle_rev y x]

/-- Negating the first vector passed to `oangle` adds `π` to the angle. -/
lemma oangle_neg_left {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  hb.oangle (-x) y = hb.oangle x y + π :=
begin
  simp only [oangle, div_neg_eq_neg_div, map_neg],
  refine complex.arg_neg_coe_angle _,
  simp [hx, hy]
end

/-- Negating the second vector passed to `oangle` adds `π` to the angle. -/
lemma oangle_neg_right {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  hb.oangle x (-y) = hb.oangle x y + π :=
begin
  simp only [oangle, neg_div, map_neg],
  refine complex.arg_neg_coe_angle _,
  simp [hx, hy]
end

/-- Negating the first vector passed to `oangle` does not change twice the angle. -/
@[simp] lemma two_zsmul_oangle_neg_left (x y : V) :
  (2 : ℤ) • hb.oangle (-x) y = (2 : ℤ) • hb.oangle x y :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  { by_cases hy : y = 0,
    { simp [hy] },
    { simp [hb.oangle_neg_left hx hy] } }
end

/-- Negating the second vector passed to `oangle` does not change twice the angle. -/
@[simp] lemma two_zsmul_oangle_neg_right (x y : V) :
  (2 : ℤ) • hb.oangle x (-y) = (2 : ℤ) • hb.oangle x y :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  { by_cases hy : y = 0,
    { simp [hy] },
    { simp [hb.oangle_neg_right hx hy] } }
end

/-- Negating both vectors passed to `oangle` does not change the angle. -/
@[simp] lemma oangle_neg_neg (x y : V) : hb.oangle (-x) (-y) = hb.oangle x y :=
by simp [oangle, neg_div_neg_eq]

/-- Negating the first vector produces the same angle as negating the second vector. -/
lemma oangle_neg_left_eq_neg_right (x y : V) : hb.oangle (-x) y = hb.oangle x (-y) :=
by rw [←neg_neg y, oangle_neg_neg, neg_neg]

/-- The angle between the negation of a nonzero vector and that vector is `π`. -/
@[simp] lemma oangle_neg_self_left {x : V} (hx : x ≠ 0) : hb.oangle (-x) x = π :=
by simp [oangle_neg_left, hx]

/-- The angle between a nonzero vector and its negation is `π`. -/
@[simp] lemma oangle_neg_self_right {x : V} (hx : x ≠ 0) : hb.oangle x (-x) = π :=
by simp [oangle_neg_right, hx]

/-- Twice the angle between the negation of a vector and that vector is 0. -/
@[simp] lemma two_zsmul_oangle_neg_self_left (x : V) : (2 : ℤ) • hb.oangle (-x) x = 0 :=
begin
  by_cases hx : x = 0;
    simp [hx]
end

/-- Twice the angle between a vector and its negation is 0. -/
@[simp] lemma two_zsmul_oangle_neg_self_right (x : V) : (2 : ℤ) • hb.oangle x (-x) = 0 :=
begin
  by_cases hx : x = 0;
    simp [hx]
end

/-- Adding the angles between two vectors in each order, with the first vector in each angle
negated, results in 0. -/
@[simp] lemma oangle_add_oangle_rev_neg_left (x y : V) :
  hb.oangle (-x) y + hb.oangle (-y) x = 0 :=
by rw [oangle_neg_left_eq_neg_right, oangle_rev, add_left_neg]

/-- Adding the angles between two vectors in each order, with the second vector in each angle
negated, results in 0. -/
@[simp] lemma oangle_add_oangle_rev_neg_right (x y : V) :
  hb.oangle x (-y) + hb.oangle y (-x) = 0 :=
by rw [hb.oangle_rev (-x), oangle_neg_left_eq_neg_right, add_neg_self]

/-- Multiplying the first vector passed to `oangle` by a positive real does not change the
angle. -/
@[simp] lemma oangle_smul_left_of_pos (x y : V) {r : ℝ} (hr : 0 < r) :
  hb.oangle (r • x) y = hb.oangle x y :=
begin
  simp only [oangle, linear_isometry_equiv.map_smul, complex.real_smul],
  rw [mul_comm, div_mul_eq_div_mul_one_div, one_div, mul_comm, ←complex.of_real_inv],
  congr' 1,
  exact complex.arg_real_mul _ (inv_pos.2 hr)
end

/-- Multiplying the second vector passed to `oangle` by a positive real does not change the
angle. -/
@[simp] lemma oangle_smul_right_of_pos (x y : V) {r : ℝ} (hr : 0 < r) :
  hb.oangle x (r • y) = hb.oangle x y :=
begin
  simp only [oangle, linear_isometry_equiv.map_smul, complex.real_smul],
  congr' 1,
  rw mul_div_assoc,
  exact complex.arg_real_mul _ hr
end

/-- Multiplying the first vector passed to `oangle` by a negative real produces the same angle
as negating that vector. -/
@[simp] lemma oangle_smul_left_of_neg (x y : V) {r : ℝ} (hr : r < 0) :
  hb.oangle (r • x) y = hb.oangle (-x) y :=
by rw [←neg_neg r, neg_smul, ←smul_neg, hb.oangle_smul_left_of_pos _ _ (neg_pos_of_neg hr)]

/-- Multiplying the second vector passed to `oangle` by a negative real produces the same angle
as negating that vector. -/
@[simp] lemma oangle_smul_right_of_neg (x y : V) {r : ℝ} (hr : r < 0) :
  hb.oangle x (r • y) = hb.oangle x (-y) :=
by rw [←neg_neg r, neg_smul, ←smul_neg, hb.oangle_smul_right_of_pos _ _ (neg_pos_of_neg hr)]

/-- The angle between a nonnegative multiple of a vector and that vector is 0. -/
@[simp] lemma oangle_smul_left_self_of_nonneg (x : V) {r : ℝ} (hr : 0 ≤ r) :
  hb.oangle (r • x) x = 0 :=
begin
  rcases hr.lt_or_eq with (h|h),
  { simp [h] },
  { simp [h.symm] }
end

/-- The angle between a vector and a nonnegative multiple of that vector is 0. -/
@[simp] lemma oangle_smul_right_self_of_nonneg (x : V) {r : ℝ} (hr : 0 ≤ r) :
  hb.oangle x (r • x) = 0 :=
begin
  rcases hr.lt_or_eq with (h|h),
  { simp [h] },
  { simp [h.symm] }
end

/-- The angle between two nonnegative multiples of the same vector is 0. -/
@[simp] lemma oangle_smul_smul_self_of_nonneg (x : V) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
  hb.oangle (r₁ • x) (r₂ • x) = 0 :=
begin
  rcases hr₁.lt_or_eq with (h|h),
  { simp [h, hr₂] },
  { simp [h.symm] }
end

/-- Multiplying the first vector passed to `oangle` by a nonzero real does not change twice the
angle. -/
@[simp] lemma two_zsmul_oangle_smul_left_of_ne_zero (x y : V) {r : ℝ} (hr : r ≠ 0) :
  (2 : ℤ) • hb.oangle (r • x) y = (2 : ℤ) • hb.oangle x y :=
begin
  rcases hr.lt_or_lt with (h|h);
    simp [h]
end

/-- Multiplying the second vector passed to `oangle` by a nonzero real does not change twice the
angle. -/
@[simp] lemma two_zsmul_oangle_smul_right_of_ne_zero (x y : V) {r : ℝ} (hr : r ≠ 0) :
  (2 : ℤ) • hb.oangle x (r • y) = (2 : ℤ) • hb.oangle x y :=
begin
  rcases hr.lt_or_lt with (h|h);
    simp [h]
end

/-- Twice the angle between a multiple of a vector and that vector is 0. -/
@[simp] lemma two_zsmul_oangle_smul_left_self (x : V) {r : ℝ} :
  (2 : ℤ) • hb.oangle (r • x) x = 0 :=
begin
  rcases lt_or_le r 0 with (h|h);
    simp [h]
end

/-- Twice the angle between a vector and a multiple of that vector is 0. -/
@[simp] lemma two_zsmul_oangle_smul_right_self (x : V) {r : ℝ} :
  (2 : ℤ) • hb.oangle x (r • x) = 0 :=
begin
  rcases lt_or_le r 0 with (h|h);
    simp [h]
end

/-- Twice the angle between two multiples of a vector is 0. -/
@[simp] lemma two_zsmul_oangle_smul_smul_self (x : V) {r₁ r₂ : ℝ} :
  (2 : ℤ) • hb.oangle (r₁ • x) (r₂ • x) = 0 :=
begin
  by_cases h : r₁ = 0;
    simp [h]
end

/-- Two vectors are equal if and only if they have equal norms and zero angle between them. -/
lemma eq_iff_norm_eq_and_oangle_eq_zero (x y : V) : x = y ↔ ∥x∥ = ∥y∥ ∧ hb.oangle x y = 0 :=
begin
  split,
  { intro h,
    simp [h] },
  { rintro ⟨hn, ha⟩,
    rw [oangle] at ha,
    by_cases hy0 : y = 0,
    { simpa [hy0] using hn },
    { have hx0 : x ≠ 0 := norm_ne_zero_iff.1 (hn.symm ▸ norm_ne_zero_iff.2 hy0),
      have hx0' : (complex.isometry_of_orthonormal hb).symm x ≠ 0,
      { simp [hx0] },
      have hy0' : (complex.isometry_of_orthonormal hb).symm y ≠ 0,
      { simp [hy0] },
      rw [complex.arg_div_coe_angle hy0' hx0', sub_eq_zero, complex.arg_coe_angle_eq_iff,
          complex.arg_eq_arg_iff hy0' hx0', ←complex.norm_eq_abs, ←complex.norm_eq_abs,
          linear_isometry_equiv.norm_map, linear_isometry_equiv.norm_map, hn,
          ←complex.of_real_div, div_self (norm_ne_zero_iff.2 hy0), complex.of_real_one,
          one_mul, linear_isometry_equiv.map_eq_iff] at ha,
      exact ha.symm } }
end

/-- Two vectors with equal norms are equal if and only if they have zero angle between them. -/
lemma eq_iff_oangle_eq_zero_of_norm_eq {x y : V} (h : ∥x∥ = ∥y∥) : x = y ↔ hb.oangle x y = 0 :=
⟨λ he, ((hb.eq_iff_norm_eq_and_oangle_eq_zero x y).1 he).2,
 λ ha, (hb.eq_iff_norm_eq_and_oangle_eq_zero x y).2 ⟨h, ha⟩⟩

/-- Two vectors with zero angle between them are equal if and only if they have equal norms. -/
lemma eq_iff_norm_eq_of_oangle_eq_zero {x y : V} (h : hb.oangle x y = 0) : x = y ↔ ∥x∥ = ∥y∥ :=
⟨λ he, ((hb.eq_iff_norm_eq_and_oangle_eq_zero x y).1 he).1,
 λ hn, (hb.eq_iff_norm_eq_and_oangle_eq_zero x y).2 ⟨hn, h⟩⟩

/-- Given three nonzero vectors, the angle between the first and the second plus the angle
between the second and the third equals the angle between the first and the third. -/
@[simp] lemma oangle_add {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  hb.oangle x y + hb.oangle y z = hb.oangle x z :=
begin
  simp_rw [oangle],
  rw ←complex.arg_mul_coe_angle,
  { rw [mul_comm, div_mul_div_cancel],
    simp [hy] },
  { simp [hx, hy] },
  { simp [hy, hz] }
end

/-- Given three nonzero vectors, the angle between the second and the third plus the angle
between the first and the second equals the angle between the first and the third. -/
@[simp] lemma oangle_add_swap {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
   hb.oangle y z + hb.oangle x y = hb.oangle x z :=
by rw [add_comm, hb.oangle_add hx hy hz]

/-- Given three nonzero vectors, the angle between the first and the third minus the angle
between the first and the second equals the angle between the second and the third. -/
@[simp] lemma oangle_sub_left {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  hb.oangle x z - hb.oangle x y = hb.oangle y z :=
by rw [sub_eq_iff_eq_add, hb.oangle_add_swap hx hy hz]

/-- Given three nonzero vectors, the angle between the first and the third minus the angle
between the second and the third equals the angle between the first and the second. -/
@[simp] lemma oangle_sub_right {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  hb.oangle x z - hb.oangle y z = hb.oangle x y :=
by rw [sub_eq_iff_eq_add, hb.oangle_add hx hy hz]

/-- Given three nonzero vectors, adding the angles between them in cyclic order results in 0. -/
@[simp] lemma oangle_add_cyc3 {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  hb.oangle x y + hb.oangle y z + hb.oangle z x = 0 :=
by simp [hx, hy, hz]

/-- Given three nonzero vectors, adding the angles between them in cyclic order, with the first
vector in each angle negated, results in π. If the vectors add to 0, this is a version of the
sum of the angles of a triangle. -/
@[simp] lemma oangle_add_cyc3_neg_left {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  hb.oangle (-x) y + hb.oangle (-y) z + hb.oangle (-z) x = π :=
by rw [hb.oangle_neg_left hx hy, hb.oangle_neg_left hy hz, hb.oangle_neg_left hz hx,
       (show hb.oangle x y + π + (hb.oangle y z + π) + (hb.oangle z x + π) =
         hb.oangle x y + hb.oangle y z + hb.oangle z x + (π + π + π : real.angle), by abel),
       hb.oangle_add_cyc3 hx hy hz, real.angle.coe_pi_add_coe_pi, zero_add, zero_add]

/-- Given three nonzero vectors, adding the angles between them in cyclic order, with the second
vector in each angle negated, results in π. If the vectors add to 0, this is a version of the
sum of the angles of a triangle. -/
@[simp] lemma oangle_add_cyc3_neg_right {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  hb.oangle x (-y) + hb.oangle y (-z) + hb.oangle z (-x) = π :=
by simp_rw [←oangle_neg_left_eq_neg_right, hb.oangle_add_cyc3_neg_left hx hy hz]

/-- Pons asinorum, oriented vector angle form. -/
lemma oangle_sub_eq_oangle_sub_rev_of_norm_eq {x y : V} (h : ∥x∥ = ∥y∥) :
  hb.oangle x (x - y) = hb.oangle (y - x) y :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  { have hy : y ≠ 0 := norm_ne_zero_iff.1 (h ▸ norm_ne_zero_iff.2 hx),
    simp_rw [hb.oangle_rev y, oangle, linear_isometry_equiv.map_sub,
             ←complex.arg_conj_coe_angle, sub_div,
             div_self (((complex.isometry_of_orthonormal hb).symm.map_eq_zero_iff).not.2 hx),
             div_self (((complex.isometry_of_orthonormal hb).symm.map_eq_zero_iff).not.2 hy),
             map_sub, map_one],
    rw ←inv_div,
    simp_rw [complex.inv_def, complex.norm_sq_div, ←complex.sq_abs, ←complex.norm_eq_abs,
             linear_isometry_equiv.norm_map, h],
    simp [hy] }
end

/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
vector angle form. -/
lemma oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq {x y : V} (hn : x ≠ y) (h : ∥x∥ = ∥y∥) :
  hb.oangle y x = π - (2 : ℤ) • hb.oangle (y - x) y :=
begin
  rw two_zsmul,
  rw [←hb.oangle_sub_eq_oangle_sub_rev_of_norm_eq h] { occs := occurrences.pos [1] },
  rw [eq_sub_iff_add_eq, ←oangle_neg_neg, ←add_assoc],
  have hy : y ≠ 0,
  { rintro rfl,
    rw [norm_zero, norm_eq_zero] at h,
    exact hn h },
  have hx : x ≠ 0 := norm_ne_zero_iff.1 (h.symm ▸ norm_ne_zero_iff.2 hy),
  convert hb.oangle_add_cyc3_neg_right (neg_ne_zero.2 hy) hx (sub_ne_zero_of_ne hn.symm);
    simp
end

/-- Angle at center of a circle equals twice angle at circumference, oriented vector angle
form. -/
lemma oangle_eq_two_zsmul_oangle_sub_of_norm_eq {x y z : V} (hxyne : x ≠ y) (hxzne : x ≠ z)
  (hxy : ∥x∥ = ∥y∥) (hxz : ∥x∥ = ∥z∥) : hb.oangle y z = (2 : ℤ) • hb.oangle (y - x) (z - x) :=
begin
  have hy : y ≠ 0,
  { rintro rfl,
    rw [norm_zero, norm_eq_zero] at hxy,
    exact hxyne hxy },
  have hx : x ≠ 0 := norm_ne_zero_iff.1 (hxy.symm ▸ norm_ne_zero_iff.2 hy),
  have hz : z ≠ 0 := norm_ne_zero_iff.1 (hxz ▸ norm_ne_zero_iff.2 hx),
  calc hb.oangle y z = hb.oangle x z - hb.oangle x y : (hb.oangle_sub_left hx hy hz).symm
       ...           = (π - (2 : ℤ) • hb.oangle (x - z) x) -
                       (π - (2 : ℤ) • hb.oangle (x - y) x) :
         by rw [hb.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hxzne.symm hxz.symm,
                hb.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hxyne.symm hxy.symm]
       ...           = (2 : ℤ) • (hb.oangle (x - y) x - hb.oangle (x - z) x) : by abel
       ...           = (2 : ℤ) • hb.oangle (x - y) (x - z) :
         by rw hb.oangle_sub_right (sub_ne_zero_of_ne hxyne) (sub_ne_zero_of_ne hxzne) hx
       ...           = (2 : ℤ) • hb.oangle (y - x) (z - x) :
         by rw [←oangle_neg_neg, neg_sub, neg_sub]
end

/-- Angle at center of a circle equals twice angle at circumference, oriented vector angle
form with radius specified. -/
lemma oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real {x y z : V} (hxyne : x ≠ y) (hxzne : x ≠ z)
  {r : ℝ} (hx : ∥x∥ = r) (hy : ∥y∥ = r) (hz : ∥z∥ = r) :
  hb.oangle y z = (2 : ℤ) • hb.oangle (y - x) (z - x) :=
hb.oangle_eq_two_zsmul_oangle_sub_of_norm_eq hxyne hxzne (hy.symm ▸ hx) (hz.symm ▸ hx)

/-- Oriented vector angle version of "angles in same segment are equal" and "opposite angles of
a cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same
result), represented here as equality of twice the angles. -/
lemma two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq {x₁ x₂ y z : V} (hx₁yne : x₁ ≠ y)
  (hx₁zne : x₁ ≠ z) (hx₂yne : x₂ ≠ y) (hx₂zne : x₂ ≠ z) {r : ℝ} (hx₁ : ∥x₁∥ = r) (hx₂ : ∥x₂∥ = r)
  (hy : ∥y∥ = r) (hz : ∥z∥ = r) :
  (2 : ℤ) • hb.oangle (y - x₁) (z - x₁) = (2 : ℤ) • hb.oangle (y - x₂) (z - x₂) :=
hb.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₁yne hx₁zne hx₁ hy hz ▸
  hb.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₂yne hx₂zne hx₂ hy hz

/-- A rotation by the oriented angle `θ`. -/
def rotation (θ : real.angle) : V ≃ₗᵢ[ℝ] V :=
((complex.isometry_of_orthonormal hb).symm.trans (rotation (real.angle.exp_map_circle θ))).trans
  (complex.isometry_of_orthonormal hb)

/-- The determinant of `rotation` (as a linear map) is equal to `1`. -/
@[simp] lemma det_rotation (θ : real.angle) :
  ((hb.rotation θ).to_linear_equiv : V →ₗ[ℝ] V).det = 1 :=
by simp [rotation, ←linear_isometry_equiv.to_linear_equiv_symm, ←linear_equiv.comp_coe]

/-- The determinant of `rotation` (as a linear equiv) is equal to `1`. -/
@[simp] lemma linear_equiv_det_rotation (θ : real.angle) :
  (hb.rotation θ).to_linear_equiv.det = 1 :=
by simp [rotation, ←linear_isometry_equiv.to_linear_equiv_symm]

/-- The inverse of `rotation` is rotation by the negation of the angle. -/
@[simp] lemma rotation_symm (θ : real.angle) : (hb.rotation θ).symm = hb.rotation (-θ) :=
by simp [rotation, linear_isometry_equiv.trans_assoc]

/-- Rotation by 0 is the identity. -/
@[simp] lemma rotation_zero : hb.rotation 0 = linear_isometry_equiv.refl ℝ V :=
by simp [rotation]

/-- Rotation by π is negation. -/
lemma rotation_pi : hb.rotation π = linear_isometry_equiv.neg ℝ :=
begin
  ext x,
  simp [rotation]
end

/-- Rotating twice is equivalent to rotating by the sum of the angles. -/
@[simp] lemma rotation_trans (θ₁ θ₂ : real.angle) :
  (hb.rotation θ₁).trans (hb.rotation θ₂) = hb.rotation (θ₂ + θ₁) :=
begin
  simp only [rotation, ←linear_isometry_equiv.trans_assoc],
  ext1 x,
  simp
end

/-- Rotating the first vector by `θ` subtracts `θ` from the angle between two vectors. -/
@[simp] lemma oangle_rotation_left {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : real.angle) :
  hb.oangle (hb.rotation θ x) y = hb.oangle x y - θ :=
begin
  simp [oangle, rotation, complex.arg_div_coe_angle, complex.arg_mul_coe_angle, hx, hy,
        ne_zero_of_mem_circle],
  abel
end

/-- Rotating the second vector by `θ` adds `θ` to the angle between two vectors. -/
@[simp] lemma oangle_rotation_right {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : real.angle) :
  hb.oangle x (hb.rotation θ y) = hb.oangle x y + θ :=
begin
  simp [oangle, rotation, complex.arg_div_coe_angle, complex.arg_mul_coe_angle, hx, hy,
        ne_zero_of_mem_circle],
  abel
end

/-- The rotation of a vector by `θ` has an angle of `-θ` from that vector. -/
@[simp] lemma oangle_rotation_self_left {x : V} (hx : x ≠ 0) (θ : real.angle) :
  hb.oangle (hb.rotation θ x) x = -θ :=
by simp [hx]

/-- A vector has an angle of `θ` from the rotation of that vector by `θ`. -/
@[simp] lemma oangle_rotation_self_right {x : V} (hx : x ≠ 0) (θ : real.angle) :
  hb.oangle x (hb.rotation θ x) = θ :=
by simp [hx]

/-- Rotating the first vector by the angle between the two vectors results an an angle of 0. -/
@[simp] lemma oangle_rotation_oangle_left (x y : V) :
  hb.oangle (hb.rotation (hb.oangle x y) x) y = 0 :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  { by_cases hy : y = 0,
    { simp [hy] },
    { simp [hx, hy] } }
end

/-- Rotating the first vector by the angle between the two vectors and swapping the vectors
results an an angle of 0. -/
@[simp] lemma oangle_rotation_oangle_right (x y : V) :
  hb.oangle y (hb.rotation (hb.oangle x y) x) = 0 :=
begin
  rw [oangle_rev],
  simp
end

/-- Rotating both vectors by the same angle does not change the angle between those vectors. -/
@[simp] lemma oangle_rotation (x y : V) (θ : real.angle) :
  hb.oangle (hb.rotation θ x) (hb.rotation θ y) = hb.oangle x y :=
begin
  by_cases hx : x = 0; by_cases hy : y = 0;
    simp [hx, hy]
end

/-- A rotation of a nonzero vector equals that vector if and only if the angle is zero. -/
@[simp] lemma rotation_eq_self_iff_angle_eq_zero {x : V} (hx : x ≠ 0) (θ : real.angle) :
  hb.rotation θ x = x ↔ θ = 0 :=
begin
  split,
  { intro h,
    rw eq_comm,
    simpa [hx, h] using hb.oangle_rotation_right hx hx θ },
  { intro h,
    simp [h] }
end

/-- A nonzero vector equals a rotation of that vector if and only if the angle is zero. -/
@[simp] lemma eq_rotation_self_iff_angle_eq_zero {x : V} (hx : x ≠ 0) (θ : real.angle) :
  x = hb.rotation θ x ↔ θ = 0 :=
by rw [←hb.rotation_eq_self_iff_angle_eq_zero hx, eq_comm]

/-- A rotation of a vector equals that vector if and only if the vector or the angle is zero. -/
lemma rotation_eq_self_iff (x : V) (θ : real.angle) :
  hb.rotation θ x = x ↔ x = 0 ∨ θ = 0 :=
begin
  by_cases h : x = 0;
    simp [h]
end

/-- A vector equals a rotation of that vector if and only if the vector or the angle is zero. -/
lemma eq_rotation_self_iff (x : V) (θ : real.angle) :
  x = hb.rotation θ x ↔ x = 0 ∨ θ = 0 :=
by rw [←rotation_eq_self_iff, eq_comm]

/-- Rotating a vector by the angle to another vector gives the second vector if and only if the
norms are equal. -/
@[simp] lemma rotation_oangle_eq_iff_norm_eq (x y : V) :
  hb.rotation (hb.oangle x y) x = y ↔ ∥x∥ = ∥y∥ :=
begin
  split,
  { intro h,
    rw [←h, linear_isometry_equiv.norm_map] },
  { intro h,
    rw hb.eq_iff_oangle_eq_zero_of_norm_eq;
      simp [h] }
end

/-- The angle between two nonzero vectors is `θ` if and only if the second vector is the first
rotated by `θ` and scaled by the ratio of the norms. -/
lemma oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
  (θ : real.angle) : hb.oangle x y = θ ↔ y = (∥y∥ / ∥x∥) • hb.rotation θ x :=
begin
  have hp := div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx),
  split,
  { rintro rfl,
    rw [←linear_isometry_equiv.map_smul, ←hb.oangle_smul_left_of_pos x y hp,
        eq_comm, rotation_oangle_eq_iff_norm_eq, norm_smul, real.norm_of_nonneg hp.le,
        div_mul_cancel _ (norm_ne_zero_iff.2 hx)] },
  { intro hye,
    rw [hye, hb.oangle_smul_right_of_pos _ _ hp, hb.oangle_rotation_self_right hx] }
end

/-- The angle between two nonzero vectors is `θ` if and only if the second vector is the first
rotated by `θ` and scaled by a positive real. -/
lemma oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
  (θ : real.angle) : hb.oangle x y = θ ↔ ∃ r : ℝ, 0 < r ∧ y = r • hb.rotation θ x :=
begin
  split,
  { intro h,
    rw hb.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy at h,
    exact ⟨∥y∥ / ∥x∥, div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx), h⟩ },
  { rintro ⟨r, hr, rfl⟩,
    rw [hb.oangle_smul_right_of_pos _ _ hr, hb.oangle_rotation_self_right hx] }
end

/-- The angle between two vectors is `θ` if and only if they are nonzero and the second vector
is the first rotated by `θ` and scaled by the ratio of the norms, or `θ` and at least one of the
vectors are zero. -/
lemma oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero {x y : V} (θ : real.angle) :
  hb.oangle x y = θ ↔
    (x ≠ 0 ∧ y ≠ 0 ∧ y = (∥y∥ / ∥x∥) • hb.rotation θ x) ∨ (θ = 0 ∧ (x = 0 ∨ y = 0)) :=
begin
  by_cases hx : x = 0,
  { simp [hx, eq_comm] },
  { by_cases hy : y = 0,
    { simp [hy, eq_comm] },
    { rw hb.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy,
      simp [hx, hy] } }
end

/-- The angle between two vectors is `θ` if and only if they are nonzero and the second vector
is the first rotated by `θ` and scaled by a positive real, or `θ` and at least one of the
vectors are zero. -/
lemma oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero {x y : V} (θ : real.angle) :
  hb.oangle x y = θ ↔
    (x ≠ 0 ∧ y ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • hb.rotation θ x) ∨ (θ = 0 ∧ (x = 0 ∨ y = 0)) :=
begin
  by_cases hx : x = 0,
  { simp [hx, eq_comm] },
  { by_cases hy : y = 0,
    { simp [hy, eq_comm] },
    { rw hb.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero hx hy,
      simp [hx, hy] } }
end

/-- Complex conjugation as a linear isometric equivalence in `V`. Note that this definition
depends on the choice of basis, not just on its orientation; for most geometrical purposes,
the `reflection` definitions should be preferred instead. -/
def conj_lie : V ≃ₗᵢ[ℝ] V :=
((complex.isometry_of_orthonormal hb).symm.trans complex.conj_lie).trans
  (complex.isometry_of_orthonormal hb)

/-- The determinant of `conj_lie` (as a linear map) is equal to `-1`. -/
@[simp] lemma det_conj_lie : (hb.conj_lie.to_linear_equiv : V →ₗ[ℝ] V).det = -1 :=
by simp [conj_lie, ←linear_isometry_equiv.to_linear_equiv_symm, ←linear_equiv.comp_coe]

/-- The determinant of `conj_lie` (as a linear equiv) is equal to `-1`. -/
@[simp] lemma linear_equiv_det_conj_lie : hb.conj_lie.to_linear_equiv.det = -1 :=
by simp [conj_lie, ←linear_isometry_equiv.to_linear_equiv_symm]

/-- `conj_lie` is its own inverse. -/
@[simp] lemma conj_lie_symm : hb.conj_lie.symm = hb.conj_lie :=
rfl

/-- Applying `conj_lie` to both vectors negates the angle between those vectors. -/
@[simp] lemma oangle_conj_lie (x y : V) :
  hb.oangle (hb.conj_lie x) (hb.conj_lie y) = -hb.oangle x y :=
by simp only [orthonormal.conj_lie, linear_isometry_equiv.symm_apply_apply, orthonormal.oangle,
  eq_self_iff_true, function.comp_app, complex.arg_coe_angle_eq_iff,
  linear_isometry_equiv.coe_trans, neg_inj, complex.conj_lie_apply, complex.arg_conj_coe_angle,
  ←(star_ring_end ℂ).map_div]

/-- Any linear isometric equivalence in `V` is `rotation` or `conj_lie` composed with
`rotation`. -/
lemma exists_linear_isometry_equiv_eq (f : V ≃ₗᵢ[ℝ] V) :
  ∃ θ : real.angle, f = hb.rotation θ ∨ f = hb.conj_lie.trans (hb.rotation θ) :=
begin
  cases linear_isometry_complex (((complex.isometry_of_orthonormal hb).trans f).trans
    (complex.isometry_of_orthonormal hb).symm) with a ha,
  use complex.arg a,
  rcases ha with (ha|ha),
  { left,
    simp only [rotation, ←ha, linear_isometry_equiv.trans_assoc, linear_isometry_equiv.refl_trans,
               linear_isometry_equiv.symm_trans_self, real.angle.exp_map_circle_coe,
               exp_map_circle_arg],
    simp [←linear_isometry_equiv.trans_assoc] },
  { right,
    simp only [rotation, conj_lie, linear_isometry_equiv.trans_assoc,
               real.angle.exp_map_circle_coe, exp_map_circle_arg],
    simp only [←linear_isometry_equiv.trans_assoc, linear_isometry_equiv.self_trans_symm,
               linear_isometry_equiv.trans_refl],
    simp_rw [linear_isometry_equiv.trans_assoc complex.conj_lie, ←ha],
    simp only [linear_isometry_equiv.trans_assoc, linear_isometry_equiv.refl_trans,
               linear_isometry_equiv.symm_trans_self],
    simp [←linear_isometry_equiv.trans_assoc] }
end

/-- Any linear isometric equivalence in `V` with positive determinant is `rotation`. -/
lemma exists_linear_isometry_equiv_eq_of_det_pos {f : V ≃ₗᵢ[ℝ] V}
  (hd : 0 < (f.to_linear_equiv : V →ₗ[ℝ] V).det) : ∃ θ : real.angle, f = hb.rotation θ :=
begin
  rcases hb.exists_linear_isometry_equiv_eq f with ⟨θ, (hf|hf)⟩,
  { exact ⟨θ, hf⟩ },
  { simp [hf, ←linear_equiv.coe_det] at hd,
    norm_num at hd }
end

/-- Any linear isometric equivalence in `V` with negative determinant is `conj_lie` composed
with `rotation`. -/
lemma exists_linear_isometry_equiv_eq_of_det_neg {f : V ≃ₗᵢ[ℝ] V}
  (hd : (f.to_linear_equiv : V →ₗ[ℝ] V).det < 0) :
  ∃ θ : real.angle, f = hb.conj_lie.trans (hb.rotation θ) :=
begin
  rcases hb.exists_linear_isometry_equiv_eq f with ⟨θ, (hf|hf)⟩,
  { simp [hf, ←linear_equiv.coe_det] at hd,
    norm_num at hd },
  { exact ⟨θ, hf⟩ }
end

/-- Two bases with the same orientation are related by a `rotation`. -/
lemma exists_linear_isometry_equiv_map_eq_of_orientation_eq {b₂ : basis (fin 2) ℝ V}
  (hb₂ : orthonormal ℝ b₂) (ho : b.orientation = b₂.orientation) :
  ∃ θ : real.angle, b₂ = b.map (hb.rotation θ).to_linear_equiv :=
begin
  have h : b₂ = b.map (hb.equiv hb₂ (equiv.refl _)).to_linear_equiv,
  { rw hb.map_equiv, simp },
  rw [eq_comm, h, b.orientation_comp_linear_equiv_eq_iff_det_pos] at ho,
  cases hb.exists_linear_isometry_equiv_eq_of_det_pos ho with θ hθ,
  rw hθ at h,
  exact ⟨θ, h⟩
end

/-- Two bases with opposite orientations are related by `conj_lie` composed with a `rotation`. -/
lemma exists_linear_isometry_equiv_map_eq_of_orientation_eq_neg {b₂ : basis (fin 2) ℝ V}
  (hb₂ : orthonormal ℝ b₂) (ho : b.orientation = -b₂.orientation) :
  ∃ θ : real.angle, b₂ = b.map (hb.conj_lie.trans (hb.rotation θ)).to_linear_equiv :=
begin
  have h : b₂ = b.map (hb.equiv hb₂ (equiv.refl _)).to_linear_equiv,
  { rw hb.map_equiv, simp },
  rw [eq_neg_iff_eq_neg, h, b.orientation_comp_linear_equiv_eq_neg_iff_det_neg] at ho,
  cases hb.exists_linear_isometry_equiv_eq_of_det_neg ho with θ hθ,
  rw hθ at h,
  exact ⟨θ, h⟩
end

/-- The angle between two vectors, with respect to a basis given by `basis.map` with a linear
isometric equivalence, equals the angle between those two vectors, transformed by the inverse of
that equivalence, with respect to the original basis. -/
@[simp] lemma oangle_map (x y : V) (f : V ≃ₗᵢ[ℝ] V) :
  (hb.map_linear_isometry_equiv f).oangle x y = hb.oangle (f.symm x) (f.symm y) :=
by simp [oangle]

/-- The value of `oangle` does not depend on the choice of basis for a given orientation. -/
lemma oangle_eq_of_orientation_eq {b₂ : basis (fin 2) ℝ V} (hb₂ : orthonormal ℝ b₂)
  (ho : b.orientation = b₂.orientation) (x y : V) : hb.oangle x y = hb₂.oangle x y :=
begin
  obtain ⟨θ, rfl⟩ := hb.exists_linear_isometry_equiv_map_eq_of_orientation_eq hb₂ ho,
  simp [hb]
end

/-- Negating the orientation negates the value of `oangle`. -/
lemma oangle_eq_neg_of_orientation_eq_neg {b₂ : basis (fin 2) ℝ V} (hb₂ : orthonormal ℝ b₂)
  (ho : b.orientation = -b₂.orientation) (x y : V) : hb.oangle x y = -hb₂.oangle x y :=
begin
  obtain ⟨θ, rfl⟩ := hb.exists_linear_isometry_equiv_map_eq_of_orientation_eq_neg hb₂ ho,
  rw hb.oangle_map,
  simp [hb]
end

/-- `rotation` does not depend on the choice of basis for a given orientation. -/
lemma rotation_eq_of_orientation_eq {b₂ : basis (fin 2) ℝ V} (hb₂ : orthonormal ℝ b₂)
  (ho : b.orientation = b₂.orientation) (θ : real.angle) : hb.rotation θ = hb₂.rotation θ :=
begin
  obtain ⟨θ₂, rfl⟩ := hb.exists_linear_isometry_equiv_map_eq_of_orientation_eq hb₂ ho,
  simp_rw [rotation, complex.map_isometry_of_orthonormal hb],
  simp only [linear_isometry_equiv.trans_assoc, linear_isometry_equiv.self_trans_symm,
             linear_isometry_equiv.refl_trans, linear_isometry_equiv.symm_trans],
  simp only [←linear_isometry_equiv.trans_assoc, _root_.rotation_symm, _root_.rotation_trans,
             mul_comm (real.angle.exp_map_circle θ), ←mul_assoc, mul_right_inv, one_mul]
end

/-- Negating the orientation negates the angle in `rotation`. -/
lemma rotation_eq_rotation_neg_of_orientation_eq_neg {b₂ : basis (fin 2) ℝ V}
  (hb₂ : orthonormal ℝ b₂) (ho : b.orientation = -b₂.orientation) (θ : real.angle) :
  hb.rotation θ = hb₂.rotation (-θ) :=
begin
  obtain ⟨θ₂, rfl⟩ := hb.exists_linear_isometry_equiv_map_eq_of_orientation_eq_neg hb₂ ho,
  simp_rw [rotation, complex.map_isometry_of_orthonormal hb, conj_lie],
  simp only [linear_isometry_equiv.trans_assoc, linear_isometry_equiv.self_trans_symm,
             linear_isometry_equiv.refl_trans, linear_isometry_equiv.symm_trans],
  congr' 1,
  simp only [←linear_isometry_equiv.trans_assoc, _root_.rotation_symm,
             linear_isometry_equiv.symm_symm, linear_isometry_equiv.self_trans_symm,
             linear_isometry_equiv.trans_refl, complex.conj_lie_symm],
  congr' 1,
  ext1 x,
  simp only [linear_isometry_equiv.coe_trans, function.comp_app, rotation_apply,
             complex.conj_lie_apply, map_mul, star_ring_end_self_apply, ←coe_inv_circle_eq_conj,
             inv_inv, real.angle.exp_map_circle_neg, ←mul_assoc],
  congr' 1,
  simp only [mul_comm (real.angle.exp_map_circle θ₂ : ℂ), mul_assoc],
  rw [←submonoid.coe_mul, mul_left_inv, submonoid.coe_one, mul_one]
end

end orthonormal

namespace orientation

open finite_dimensional

variables {V : Type*} [inner_product_space ℝ V]
variables [hd2 : fact (finrank ℝ V = 2)] (o : orientation ℝ V (fin 2))
include hd2 o

local notation `ob` := o.fin_orthonormal_basis_orthonormal dec_trivial hd2.out

/-- The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0.
See `inner_product_geometry.angle` for the corresponding unoriented angle definition. -/
def oangle (x y : V) : real.angle :=
(ob).oangle x y

/-- If the first vector passed to `oangle` is 0, the result is 0. -/
@[simp] lemma oangle_zero_left (x : V) : o.oangle 0 x = 0 :=
(ob).oangle_zero_left x

/-- If the second vector passed to `oangle` is 0, the result is 0. -/
@[simp] lemma oangle_zero_right (x : V) : o.oangle x 0 = 0 :=
(ob).oangle_zero_right x

/-- If the two vectors passed to `oangle` are the same, the result is 0. -/
@[simp] lemma oangle_self (x : V) : o.oangle x x = 0 :=
(ob).oangle_self x

/-- Swapping the two vectors passed to `oangle` negates the angle. -/
lemma oangle_rev (x y : V) : o.oangle y x = -o.oangle x y :=
(ob).oangle_rev x y

/-- Adding the angles between two vectors in each order results in 0. -/
@[simp] lemma oangle_add_oangle_rev (x y : V) : o.oangle x y + o.oangle y x = 0 :=
(ob).oangle_add_oangle_rev x y

/-- Negating the first vector passed to `oangle` adds `π` to the angle. -/
lemma oangle_neg_left {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  o.oangle (-x) y = o.oangle x y + π :=
(ob).oangle_neg_left hx hy

/-- Negating the second vector passed to `oangle` adds `π` to the angle. -/
lemma oangle_neg_right {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  o.oangle x (-y) = o.oangle x y + π :=
(ob).oangle_neg_right hx hy

/-- Negating the first vector passed to `oangle` does not change twice the angle. -/
@[simp] lemma two_zsmul_oangle_neg_left (x y : V) :
  (2 : ℤ) • o.oangle (-x) y = (2 : ℤ) • o.oangle x y :=
(ob).two_zsmul_oangle_neg_left x y

/-- Negating the second vector passed to `oangle` does not change twice the angle. -/
@[simp] lemma two_zsmul_oangle_neg_right (x y : V) :
  (2 : ℤ) • o.oangle x (-y) = (2 : ℤ) • o.oangle x y :=
(ob).two_zsmul_oangle_neg_right x y

/-- Negating both vectors passed to `oangle` does not change the angle. -/
@[simp] lemma oangle_neg_neg (x y : V) : o.oangle (-x) (-y) = o.oangle x y :=
(ob).oangle_neg_neg x y

/-- Negating the first vector produces the same angle as negating the second vector. -/
lemma oangle_neg_left_eq_neg_right (x y : V) : o.oangle (-x) y = o.oangle x (-y) :=
(ob).oangle_neg_left_eq_neg_right x y

/-- The angle between the negation of a nonzero vector and that vector is `π`. -/
@[simp] lemma oangle_neg_self_left {x : V} (hx : x ≠ 0) : o.oangle (-x) x = π :=
(ob).oangle_neg_self_left hx

/-- The angle between a nonzero vector and its negation is `π`. -/
@[simp] lemma oangle_neg_self_right {x : V} (hx : x ≠ 0) : o.oangle x (-x) = π :=
(ob).oangle_neg_self_right hx

/-- Twice the angle between the negation of a vector and that vector is 0. -/
@[simp] lemma two_zsmul_oangle_neg_self_left (x : V) : (2 : ℤ) • o.oangle (-x) x = 0 :=
(ob).two_zsmul_oangle_neg_self_left x

/-- Twice the angle between a vector and its negation is 0. -/
@[simp] lemma two_zsmul_oangle_neg_self_right (x : V) : (2 : ℤ) • o.oangle x (-x) = 0 :=
(ob).two_zsmul_oangle_neg_self_right x

/-- Adding the angles between two vectors in each order, with the first vector in each angle
negated, results in 0. -/
@[simp] lemma oangle_add_oangle_rev_neg_left (x y : V) :
  o.oangle (-x) y + o.oangle (-y) x = 0 :=
(ob).oangle_add_oangle_rev_neg_left x y

/-- Adding the angles between two vectors in each order, with the second vector in each angle
negated, results in 0. -/
@[simp] lemma oangle_add_oangle_rev_neg_right (x y : V) :
  o.oangle x (-y) + o.oangle y (-x) = 0 :=
(ob).oangle_add_oangle_rev_neg_right x y

/-- Multiplying the first vector passed to `oangle` by a positive real does not change the
angle. -/
@[simp] lemma oangle_smul_left_of_pos (x y : V) {r : ℝ} (hr : 0 < r) :
  o.oangle (r • x) y = o.oangle x y :=
(ob).oangle_smul_left_of_pos x y hr

/-- Multiplying the second vector passed to `oangle` by a positive real does not change the
angle. -/
@[simp] lemma oangle_smul_right_of_pos (x y : V) {r : ℝ} (hr : 0 < r) :
  o.oangle x (r • y) = o.oangle x y :=
(ob).oangle_smul_right_of_pos x y hr

/-- Multiplying the first vector passed to `oangle` by a negative real produces the same angle
as negating that vector. -/
@[simp] lemma oangle_smul_left_of_neg (x y : V) {r : ℝ} (hr : r < 0) :
  o.oangle (r • x) y = o.oangle (-x) y :=
(ob).oangle_smul_left_of_neg x y hr

/-- Multiplying the second vector passed to `oangle` by a negative real produces the same angle
as negating that vector. -/
@[simp] lemma oangle_smul_right_of_neg (x y : V) {r : ℝ} (hr : r < 0) :
  o.oangle x (r • y) = o.oangle x (-y) :=
(ob).oangle_smul_right_of_neg x y hr

/-- The angle between a nonnegative multiple of a vector and that vector is 0. -/
@[simp] lemma oangle_smul_left_self_of_nonneg (x : V) {r : ℝ} (hr : 0 ≤ r) :
  o.oangle (r • x) x = 0 :=
(ob).oangle_smul_left_self_of_nonneg x hr

/-- The angle between a vector and a nonnegative multiple of that vector is 0. -/
@[simp] lemma oangle_smul_right_self_of_nonneg (x : V) {r : ℝ} (hr : 0 ≤ r) :
  o.oangle x (r • x) = 0 :=
(ob).oangle_smul_right_self_of_nonneg x hr

/-- The angle between two nonnegative multiples of the same vector is 0. -/
@[simp] lemma oangle_smul_smul_self_of_nonneg (x : V) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
  o.oangle (r₁ • x) (r₂ • x) = 0 :=
(ob).oangle_smul_smul_self_of_nonneg x hr₁ hr₂

/-- Multiplying the first vector passed to `oangle` by a nonzero real does not change twice the
angle. -/
@[simp] lemma two_zsmul_oangle_smul_left_of_ne_zero (x y : V) {r : ℝ} (hr : r ≠ 0) :
  (2 : ℤ) • o.oangle (r • x) y = (2 : ℤ) • o.oangle x y :=
(ob).two_zsmul_oangle_smul_left_of_ne_zero x y hr

/-- Multiplying the second vector passed to `oangle` by a nonzero real does not change twice the
angle. -/
@[simp] lemma two_zsmul_oangle_smul_right_of_ne_zero (x y : V) {r : ℝ} (hr : r ≠ 0) :
  (2 : ℤ) • o.oangle x (r • y) = (2 : ℤ) • o.oangle x y :=
(ob).two_zsmul_oangle_smul_right_of_ne_zero x y hr

/-- Twice the angle between a multiple of a vector and that vector is 0. -/
@[simp] lemma two_zsmul_oangle_smul_left_self (x : V) {r : ℝ} :
  (2 : ℤ) • o.oangle (r • x) x = 0 :=
(ob).two_zsmul_oangle_smul_left_self x

/-- Twice the angle between a vector and a multiple of that vector is 0. -/
@[simp] lemma two_zsmul_oangle_smul_right_self (x : V) {r : ℝ} :
  (2 : ℤ) • o.oangle x (r • x) = 0 :=
(ob).two_zsmul_oangle_smul_right_self x

/-- Twice the angle between two multiples of a vector is 0. -/
@[simp] lemma two_zsmul_oangle_smul_smul_self (x : V) {r₁ r₂ : ℝ} :
  (2 : ℤ) • o.oangle (r₁ • x) (r₂ • x) = 0 :=
(ob).two_zsmul_oangle_smul_smul_self x

/-- Two vectors are equal if and only if they have equal norms and zero angle between them. -/
lemma eq_iff_norm_eq_and_oangle_eq_zero (x y : V) : x = y ↔ ∥x∥ = ∥y∥ ∧ o.oangle x y = 0 :=
(ob).eq_iff_norm_eq_and_oangle_eq_zero x y

/-- Two vectors with equal norms are equal if and only if they have zero angle between them. -/
lemma eq_iff_oangle_eq_zero_of_norm_eq {x y : V} (h : ∥x∥ = ∥y∥) : x = y ↔ o.oangle x y = 0 :=
(ob).eq_iff_oangle_eq_zero_of_norm_eq h

/-- Two vectors with zero angle between them are equal if and only if they have equal norms. -/
lemma eq_iff_norm_eq_of_oangle_eq_zero {x y : V} (h : o.oangle x y = 0) : x = y ↔ ∥x∥ = ∥y∥ :=
(ob).eq_iff_norm_eq_of_oangle_eq_zero h

/-- Given three nonzero vectors, the angle between the first and the second plus the angle
between the second and the third equals the angle between the first and the third. -/
@[simp] lemma oangle_add {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  o.oangle x y + o.oangle y z = o.oangle x z :=
(ob).oangle_add hx hy hz

/-- Given three nonzero vectors, the angle between the second and the third plus the angle
between the first and the second equals the angle between the first and the third. -/
@[simp] lemma oangle_add_swap {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
   o.oangle y z + o.oangle x y = o.oangle x z :=
(ob).oangle_add_swap hx hy hz

/-- Given three nonzero vectors, the angle between the first and the third minus the angle
between the first and the second equals the angle between the second and the third. -/
@[simp] lemma oangle_sub_left {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  o.oangle x z - o.oangle x y = o.oangle y z :=
(ob).oangle_sub_left hx hy hz

/-- Given three nonzero vectors, the angle between the first and the third minus the angle
between the second and the third equals the angle between the first and the second. -/
@[simp] lemma oangle_sub_right {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  o.oangle x z - o.oangle y z = o.oangle x y :=
(ob).oangle_sub_right hx hy hz

/-- Given three nonzero vectors, adding the angles between them in cyclic order results in 0. -/
@[simp] lemma oangle_add_cyc3 {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  o.oangle x y + o.oangle y z + o.oangle z x = 0 :=
(ob).oangle_add_cyc3 hx hy hz

/-- Given three nonzero vectors, adding the angles between them in cyclic order, with the first
vector in each angle negated, results in π. If the vectors add to 0, this is a version of the
sum of the angles of a triangle. -/
@[simp] lemma oangle_add_cyc3_neg_left {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  o.oangle (-x) y + o.oangle (-y) z + o.oangle (-z) x = π :=
(ob).oangle_add_cyc3_neg_left hx hy hz

/-- Given three nonzero vectors, adding the angles between them in cyclic order, with the second
vector in each angle negated, results in π. If the vectors add to 0, this is a version of the
sum of the angles of a triangle. -/
@[simp] lemma oangle_add_cyc3_neg_right {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  o.oangle x (-y) + o.oangle y (-z) + o.oangle z (-x) = π :=
(ob).oangle_add_cyc3_neg_right hx hy hz

/-- Pons asinorum, oriented vector angle form. -/
lemma oangle_sub_eq_oangle_sub_rev_of_norm_eq {x y : V} (h : ∥x∥ = ∥y∥) :
  o.oangle x (x - y) = o.oangle (y - x) y :=
(ob).oangle_sub_eq_oangle_sub_rev_of_norm_eq h

/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
vector angle form. -/
lemma oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq {x y : V} (hn : x ≠ y) (h : ∥x∥ = ∥y∥) :
  o.oangle y x = π - (2 : ℤ) • o.oangle (y - x) y :=
(ob).oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hn h

/-- Angle at center of a circle equals twice angle at circumference, oriented vector angle
form. -/
lemma oangle_eq_two_zsmul_oangle_sub_of_norm_eq {x y z : V} (hxyne : x ≠ y) (hxzne : x ≠ z)
  (hxy : ∥x∥ = ∥y∥) (hxz : ∥x∥ = ∥z∥) : o.oangle y z = (2 : ℤ) • o.oangle (y - x) (z - x) :=
(ob).oangle_eq_two_zsmul_oangle_sub_of_norm_eq hxyne hxzne hxy hxz

/-- Angle at center of a circle equals twice angle at circumference, oriented vector angle
form with radius specified. -/
lemma oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real {x y z : V} (hxyne : x ≠ y) (hxzne : x ≠ z)
  {r : ℝ} (hx : ∥x∥ = r) (hy : ∥y∥ = r) (hz : ∥z∥ = r) :
  o.oangle y z = (2 : ℤ) • o.oangle (y - x) (z - x) :=
(ob).oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hxyne hxzne hx hy hz

/-- Oriented vector angle version of "angles in same segment are equal" and "opposite angles of
a cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same
result), represented here as equality of twice the angles. -/
lemma two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq {x₁ x₂ y z : V} (hx₁yne : x₁ ≠ y)
  (hx₁zne : x₁ ≠ z) (hx₂yne : x₂ ≠ y) (hx₂zne : x₂ ≠ z) {r : ℝ} (hx₁ : ∥x₁∥ = r) (hx₂ : ∥x₂∥ = r)
  (hy : ∥y∥ = r) (hz : ∥z∥ = r) :
  (2 : ℤ) • o.oangle (y - x₁) (z - x₁) = (2 : ℤ) • o.oangle (y - x₂) (z - x₂) :=
(ob).two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq hx₁yne hx₁zne hx₂yne hx₂zne hx₁ hx₂
  hy hz

/-- A rotation by the oriented angle `θ`. -/
def rotation (θ : real.angle) : V ≃ₗᵢ[ℝ] V :=
(ob).rotation θ

/-- The determinant of `rotation` (as a linear map) is equal to `1`. -/
@[simp] lemma det_rotation (θ : real.angle) :
  ((o.rotation θ).to_linear_equiv : V →ₗ[ℝ] V).det = 1 :=
(ob).det_rotation θ

/-- The determinant of `rotation` (as a linear equiv) is equal to `1`. -/
@[simp] lemma linear_equiv_det_rotation (θ : real.angle) :
  (o.rotation θ).to_linear_equiv.det = 1 :=
(ob).linear_equiv_det_rotation θ

/-- The inverse of `rotation` is rotation by the negation of the angle. -/
@[simp] lemma rotation_symm (θ : real.angle) : (o.rotation θ).symm = o.rotation (-θ) :=
(ob).rotation_symm θ

/-- Rotation by 0 is the identity. -/
@[simp] lemma rotation_zero : o.rotation 0 = linear_isometry_equiv.refl ℝ V :=
(ob).rotation_zero

/-- Rotation by π is negation. -/
lemma rotation_pi : o.rotation π = linear_isometry_equiv.neg ℝ :=
(ob).rotation_pi

/-- Rotating twice is equivalent to rotating by the sum of the angles. -/
@[simp] lemma rotation_trans (θ₁ θ₂ : real.angle) :
  (o.rotation θ₁).trans (o.rotation θ₂) = o.rotation (θ₂ + θ₁) :=
(ob).rotation_trans θ₁ θ₂

/-- Rotating the first vector by `θ` subtracts `θ` from the angle between two vectors. -/
@[simp] lemma oangle_rotation_left {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : real.angle) :
  o.oangle (o.rotation θ x) y = o.oangle x y - θ :=
(ob).oangle_rotation_left hx hy θ

/-- Rotating the second vector by `θ` adds `θ` to the angle between two vectors. -/
@[simp] lemma oangle_rotation_right {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : real.angle) :
  o.oangle x (o.rotation θ y) = o.oangle x y + θ :=
(ob).oangle_rotation_right hx hy θ

/-- The rotation of a vector by `θ` has an angle of `-θ` from that vector. -/
@[simp] lemma oangle_rotation_self_left {x : V} (hx : x ≠ 0) (θ : real.angle) :
  o.oangle (o.rotation θ x) x = -θ :=
(ob).oangle_rotation_self_left hx θ

/-- A vector has an angle of `θ` from the rotation of that vector by `θ`. -/
@[simp] lemma oangle_rotation_self_right {x : V} (hx : x ≠ 0) (θ : real.angle) :
  o.oangle x (o.rotation θ x) = θ :=
(ob).oangle_rotation_self_right hx θ

/-- Rotating the first vector by the angle between the two vectors results an an angle of 0. -/
@[simp] lemma oangle_rotation_oangle_left (x y : V) :
  o.oangle (o.rotation (o.oangle x y) x) y = 0 :=
(ob).oangle_rotation_oangle_left x y

/-- Rotating the first vector by the angle between the two vectors and swapping the vectors
results an an angle of 0. -/
@[simp] lemma oangle_rotation_oangle_right (x y : V) :
  o.oangle y (o.rotation (o.oangle x y) x) = 0 :=
(ob).oangle_rotation_oangle_right x y

/-- Rotating both vectors by the same angle does not change the angle between those vectors. -/
@[simp] lemma oangle_rotation (x y : V) (θ : real.angle) :
  o.oangle (o.rotation θ x) (o.rotation θ y) = o.oangle x y :=
(ob).oangle_rotation x y θ

/-- A rotation of a nonzero vector equals that vector if and only if the angle is zero. -/
@[simp] lemma rotation_eq_self_iff_angle_eq_zero {x : V} (hx : x ≠ 0) (θ : real.angle) :
  o.rotation θ x = x ↔ θ = 0 :=
(ob).rotation_eq_self_iff_angle_eq_zero hx θ

/-- A nonzero vector equals a rotation of that vector if and only if the angle is zero. -/
@[simp] lemma eq_rotation_self_iff_angle_eq_zero {x : V} (hx : x ≠ 0) (θ : real.angle) :
  x = o.rotation θ x ↔ θ = 0 :=
(ob).eq_rotation_self_iff_angle_eq_zero hx θ

/-- A rotation of a vector equals that vector if and only if the vector or the angle is zero. -/
lemma rotation_eq_self_iff (x : V) (θ : real.angle) :
  o.rotation θ x = x ↔ x = 0 ∨ θ = 0 :=
(ob).rotation_eq_self_iff x θ

/-- A vector equals a rotation of that vector if and only if the vector or the angle is zero. -/
lemma eq_rotation_self_iff (x : V) (θ : real.angle) :
  x = o.rotation θ x ↔ x = 0 ∨ θ = 0 :=
(ob).eq_rotation_self_iff x θ

/-- Rotating a vector by the angle to another vector gives the second vector if and only if the
norms are equal. -/
@[simp] lemma rotation_oangle_eq_iff_norm_eq (x y : V) :
  o.rotation (o.oangle x y) x = y ↔ ∥x∥ = ∥y∥ :=
(ob).rotation_oangle_eq_iff_norm_eq x y

/-- The angle between two nonzero vectors is `θ` if and only if the second vector is the first
rotated by `θ` and scaled by the ratio of the norms. -/
lemma oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
  (θ : real.angle) : o.oangle x y = θ ↔ y = (∥y∥ / ∥x∥) • o.rotation θ x :=
(ob).oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy θ

/-- The angle between two nonzero vectors is `θ` if and only if the second vector is the first
rotated by `θ` and scaled by a positive real. -/
lemma oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
  (θ : real.angle) : o.oangle x y = θ ↔ ∃ r : ℝ, 0 < r ∧ y = r • o.rotation θ x :=
(ob).oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero hx hy θ

/-- The angle between two vectors is `θ` if and only if they are nonzero and the second vector
is the first rotated by `θ` and scaled by the ratio of the norms, or `θ` and at least one of the
vectors are zero. -/
lemma oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero {x y : V} (θ : real.angle) :
  o.oangle x y = θ ↔
    (x ≠ 0 ∧ y ≠ 0 ∧ y = (∥y∥ / ∥x∥) • o.rotation θ x) ∨ (θ = 0 ∧ (x = 0 ∨ y = 0)) :=
(ob).oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero θ

/-- The angle between two vectors is `θ` if and only if they are nonzero and the second vector
is the first rotated by `θ` and scaled by a positive real, or `θ` and at least one of the
vectors are zero. -/
lemma oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero {x y : V} (θ : real.angle) :
  o.oangle x y = θ ↔
    (x ≠ 0 ∧ y ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • o.rotation θ x) ∨ (θ = 0 ∧ (x = 0 ∨ y = 0)) :=
(ob).oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero θ

/-- Any linear isometric equivalence in `V` with positive determinant is `rotation`. -/
lemma exists_linear_isometry_equiv_eq_of_det_pos {f : V ≃ₗᵢ[ℝ] V}
  (hd : 0 < (f.to_linear_equiv : V →ₗ[ℝ] V).det) : ∃ θ : real.angle, f = o.rotation θ :=
(ob).exists_linear_isometry_equiv_eq_of_det_pos hd

/-- The angle between two vectors, with respect to an orientation given by `orientation.map`
with a linear isometric equivalence, equals the angle between those two vectors, transformed by
the inverse of that equivalence, with respect to the original orientation. -/
@[simp] lemma oangle_map (x y : V) (f : V ≃ₗᵢ[ℝ] V) :
  (orientation.map (fin 2) f.to_linear_equiv o).oangle x y = o.oangle (f.symm x) (f.symm y) :=
begin
  convert (ob).oangle_map x y f using 1,
  refine orthonormal.oangle_eq_of_orientation_eq _ _ _ _ _,
  simp_rw [basis.orientation_map, orientation.fin_orthonormal_basis_orientation]
end

/-- `orientation.oangle` equals `orthonormal.oangle` for any orthonormal basis with that
orientation. -/
lemma oangle_eq_basis_oangle {b : basis (fin 2) ℝ V} (hb : orthonormal ℝ b)
  (h : b.orientation = o) (x y : V) : o.oangle x y = hb.oangle x y :=
begin
  rw oangle,
  refine orthonormal.oangle_eq_of_orientation_eq _ _ _ _ _,
  simp [h]
end

/-- Negating the orientation negates the value of `oangle`. -/
lemma oangle_neg_orientation_eq_neg (x y : V) : (-o).oangle x y = -(o.oangle x y) :=
begin
  simp_rw oangle,
  refine orthonormal.oangle_eq_neg_of_orientation_eq_neg _ _ _ _ _,
  simp_rw orientation.fin_orthonormal_basis_orientation
end

/-- `orientation.rotation` equals `orthonormal.rotation` for any orthonormal basis with that
orientation. -/
lemma rotation_eq_basis_rotation {b : basis (fin 2) ℝ V} (hb : orthonormal ℝ b)
  (h : b.orientation = o) (θ : ℝ) : o.rotation θ = hb.rotation θ :=
begin
  rw rotation,
  refine orthonormal.rotation_eq_of_orientation_eq _ _ _ _,
  simp [h]
end

/-- Negating the orientation negates the angle in `rotation`. -/
lemma rotation_neg_orientation_eq_neg (θ : real.angle) :
  (-o).rotation θ = o.rotation (-θ) :=
begin
  simp_rw rotation,
  refine orthonormal.rotation_eq_rotation_neg_of_orientation_eq_neg _ _ _ _,
  simp_rw orientation.fin_orthonormal_basis_orientation
end

end orientation
