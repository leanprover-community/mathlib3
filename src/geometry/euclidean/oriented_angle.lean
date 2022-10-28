/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Heather Macbeth
-/
import analysis.complex.arg
import analysis.inner_product_space.two_dim
import analysis.special_functions.complex.circle
import geometry.euclidean.angle.unoriented.affine

/-!
# Oriented angles.

This file defines oriented angles in real inner product spaces and Euclidean affine spaces.

## Main definitions

* `orientation.oangle` is the oriented angle between two vectors with respect to an orientation.

* `orientation.rotation` is the rotation by an oriented angle with respect to an orientation.

* `euclidean_geometry.oangle`, with notation `∡`, is the oriented angle determined by three
  points.

## Implementation notes

The definitions here use the `real.angle` type, angles modulo `2 * π`. For some purposes,
angles modulo `π` are more convenient, because results are true for such angles with less
configuration dependence. Results that are only equalities modulo `π` can be represented
modulo `2 * π` as equalities of `(2 : ℤ) • θ`.

## References

* Evan Chen, Euclidean Geometry in Mathematical Olympiads.

-/

noncomputable theory

open finite_dimensional complex
open_locale euclidean_geometry real real_inner_product_space complex_conjugate

namespace orientation

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ
local attribute [instance] complex.finrank_real_complex_fact

variables {V V' : Type*} [inner_product_space ℝ V] [inner_product_space ℝ V']
variables [fact (finrank ℝ V = 2)] [fact (finrank ℝ V' = 2)] (o : orientation ℝ V (fin 2))

local notation `ω` := o.area_form
local notation `J` := o.right_angle_rotation

/-- The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0.
See `inner_product_geometry.angle` for the corresponding unoriented angle definition. -/
def oangle (x y : V) : real.angle :=
complex.arg (o.kahler x y)

/-- Oriented angles are continuous when the vectors involved are nonzero. -/
lemma continuous_at_oangle {x : V × V} (hx1 : x.1 ≠ 0) (hx2 : x.2 ≠ 0) :
  continuous_at (λ y : V × V, o.oangle y.1 y.2) x :=
begin
  refine (complex.continuous_at_arg_coe_angle _).comp _,
  { exact o.kahler_ne_zero hx1 hx2 },
  exact ((continuous_of_real.comp continuous_inner).add
    ((continuous_of_real.comp o.area_form'.continuous₂).mul continuous_const)).continuous_at,
end

/-- If the first vector passed to `oangle` is 0, the result is 0. -/
@[simp] lemma oangle_zero_left (x : V) : o.oangle 0 x = 0 :=
by simp [oangle]

/-- If the second vector passed to `oangle` is 0, the result is 0. -/
@[simp] lemma oangle_zero_right (x : V) : o.oangle x 0 = 0 :=
by simp [oangle]

/-- If the two vectors passed to `oangle` are the same, the result is 0. -/
@[simp] lemma oangle_self (x : V) : o.oangle x x = 0 :=
begin
  simp only [oangle, kahler_apply_self, ← complex.of_real_pow],
  convert quotient_add_group.coe_zero _,
  apply arg_of_real_of_nonneg,
  positivity,
end

/-- Swapping the two vectors passed to `oangle` negates the angle. -/
lemma oangle_rev (x y : V) : o.oangle y x = -o.oangle x y :=
by simp only [oangle, o.kahler_swap y x, complex.arg_conj_coe_angle]

/-- Adding the angles between two vectors in each order results in 0. -/
@[simp] lemma oangle_add_oangle_rev (x y : V) : o.oangle x y + o.oangle y x = 0 :=
by simp [o.oangle_rev y x]

/-- Negating the first vector passed to `oangle` adds `π` to the angle. -/
lemma oangle_neg_left {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  o.oangle (-x) y = o.oangle x y + π :=
begin
  simp only [oangle, map_neg],
  convert complex.arg_neg_coe_angle _,
  exact o.kahler_ne_zero hx hy,
end

/-- Negating the second vector passed to `oangle` adds `π` to the angle. -/
lemma oangle_neg_right {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  o.oangle x (-y) = o.oangle x y + π :=
begin
  simp only [oangle, map_neg],
  convert complex.arg_neg_coe_angle _,
  exact o.kahler_ne_zero hx hy,
end

/-- Negating the first vector passed to `oangle` does not change twice the angle. -/
@[simp] lemma two_zsmul_oangle_neg_left (x y : V) :
  (2 : ℤ) • o.oangle (-x) y = (2 : ℤ) • o.oangle x y :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  { by_cases hy : y = 0,
    { simp [hy] },
    { simp [o.oangle_neg_left hx hy] } }
end

/-- Negating the second vector passed to `oangle` does not change twice the angle. -/
@[simp] lemma two_zsmul_oangle_neg_right (x y : V) :
  (2 : ℤ) • o.oangle x (-y) = (2 : ℤ) • o.oangle x y :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  { by_cases hy : y = 0,
    { simp [hy] },
    { simp [o.oangle_neg_right hx hy] } }
end

/-- Negating both vectors passed to `oangle` does not change the angle. -/
@[simp] lemma oangle_neg_neg (x y : V) : o.oangle (-x) (-y) = o.oangle x y :=
by simp [oangle]

/-- Negating the first vector produces the same angle as negating the second vector. -/
lemma oangle_neg_left_eq_neg_right (x y : V) : o.oangle (-x) y = o.oangle x (-y) :=
by rw [←neg_neg y, oangle_neg_neg, neg_neg]

/-- The angle between the negation of a nonzero vector and that vector is `π`. -/
@[simp] lemma oangle_neg_self_left {x : V} (hx : x ≠ 0) : o.oangle (-x) x = π :=
by simp [oangle_neg_left, hx]

/-- The angle between a nonzero vector and its negation is `π`. -/
@[simp] lemma oangle_neg_self_right {x : V} (hx : x ≠ 0) : o.oangle x (-x) = π :=
by simp [oangle_neg_right, hx]

/-- Twice the angle between the negation of a vector and that vector is 0. -/
@[simp] lemma two_zsmul_oangle_neg_self_left (x : V) : (2 : ℤ) • o.oangle (-x) x = 0 :=
begin
  by_cases hx : x = 0;
    simp [hx]
end

/-- Twice the angle between a vector and its negation is 0. -/
@[simp] lemma two_zsmul_oangle_neg_self_right (x : V) : (2 : ℤ) • o.oangle x (-x) = 0 :=
begin
  by_cases hx : x = 0;
    simp [hx]
end

/-- Adding the angles between two vectors in each order, with the first vector in each angle
negated, results in 0. -/
@[simp] lemma oangle_add_oangle_rev_neg_left (x y : V) :
  o.oangle (-x) y + o.oangle (-y) x = 0 :=
by rw [oangle_neg_left_eq_neg_right, oangle_rev, add_left_neg]

/-- Adding the angles between two vectors in each order, with the second vector in each angle
negated, results in 0. -/
@[simp] lemma oangle_add_oangle_rev_neg_right (x y : V) :
  o.oangle x (-y) + o.oangle y (-x) = 0 :=
by rw [o.oangle_rev (-x), oangle_neg_left_eq_neg_right, add_neg_self]

/-- Multiplying the first vector passed to `oangle` by a positive real does not change the
angle. -/
@[simp] lemma oangle_smul_left_of_pos (x y : V) {r : ℝ} (hr : 0 < r) :
  o.oangle (r • x) y = o.oangle x y :=
by simp [oangle, complex.arg_real_mul _ hr]

/-- Multiplying the second vector passed to `oangle` by a positive real does not change the
angle. -/
@[simp] lemma oangle_smul_right_of_pos (x y : V) {r : ℝ} (hr : 0 < r) :
  o.oangle x (r • y) = o.oangle x y :=
by simp [oangle, complex.arg_real_mul _ hr]

/-- Multiplying the first vector passed to `oangle` by a negative real produces the same angle
as negating that vector. -/
@[simp] lemma oangle_smul_left_of_neg (x y : V) {r : ℝ} (hr : r < 0) :
  o.oangle (r • x) y = o.oangle (-x) y :=
by rw [←neg_neg r, neg_smul, ←smul_neg, o.oangle_smul_left_of_pos _ _ (neg_pos_of_neg hr)]

/-- Multiplying the second vector passed to `oangle` by a negative real produces the same angle
as negating that vector. -/
@[simp] lemma oangle_smul_right_of_neg (x y : V) {r : ℝ} (hr : r < 0) :
  o.oangle x (r • y) = o.oangle x (-y) :=
by rw [←neg_neg r, neg_smul, ←smul_neg, o.oangle_smul_right_of_pos _ _ (neg_pos_of_neg hr)]

/-- The angle between a nonnegative multiple of a vector and that vector is 0. -/
@[simp] lemma oangle_smul_left_self_of_nonneg (x : V) {r : ℝ} (hr : 0 ≤ r) :
  o.oangle (r • x) x = 0 :=
begin
  rcases hr.lt_or_eq with (h|h),
  { simp [h] },
  { simp [h.symm] }
end

/-- The angle between a vector and a nonnegative multiple of that vector is 0. -/
@[simp] lemma oangle_smul_right_self_of_nonneg (x : V) {r : ℝ} (hr : 0 ≤ r) :
  o.oangle x (r • x) = 0 :=
begin
  rcases hr.lt_or_eq with (h|h),
  { simp [h] },
  { simp [h.symm] }
end

/-- The angle between two nonnegative multiples of the same vector is 0. -/
@[simp] lemma oangle_smul_smul_self_of_nonneg (x : V) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
  o.oangle (r₁ • x) (r₂ • x) = 0 :=
begin
  rcases hr₁.lt_or_eq with (h|h),
  { simp [h, hr₂] },
  { simp [h.symm] }
end

/-- Multiplying the first vector passed to `oangle` by a nonzero real does not change twice the
angle. -/
@[simp] lemma two_zsmul_oangle_smul_left_of_ne_zero (x y : V) {r : ℝ} (hr : r ≠ 0) :
  (2 : ℤ) • o.oangle (r • x) y = (2 : ℤ) • o.oangle x y :=
begin
  rcases hr.lt_or_lt with (h|h);
    simp [h]
end

/-- Multiplying the second vector passed to `oangle` by a nonzero real does not change twice the
angle. -/
@[simp] lemma two_zsmul_oangle_smul_right_of_ne_zero (x y : V) {r : ℝ} (hr : r ≠ 0) :
  (2 : ℤ) • o.oangle x (r • y) = (2 : ℤ) • o.oangle x y :=
begin
  rcases hr.lt_or_lt with (h|h);
    simp [h]
end

/-- Twice the angle between a multiple of a vector and that vector is 0. -/
@[simp] lemma two_zsmul_oangle_smul_left_self (x : V) {r : ℝ} :
  (2 : ℤ) • o.oangle (r • x) x = 0 :=
begin
  rcases lt_or_le r 0 with (h|h);
    simp [h]
end

/-- Twice the angle between a vector and a multiple of that vector is 0. -/
@[simp] lemma two_zsmul_oangle_smul_right_self (x : V) {r : ℝ} :
  (2 : ℤ) • o.oangle x (r • x) = 0 :=
begin
  rcases lt_or_le r 0 with (h|h);
    simp [h]
end

/-- Twice the angle between two multiples of a vector is 0. -/
@[simp] lemma two_zsmul_oangle_smul_smul_self (x : V) {r₁ r₂ : ℝ} :
  (2 : ℤ) • o.oangle (r₁ • x) (r₂ • x) = 0 :=
begin
  by_cases h : r₁ = 0;
    simp [h]
end

/-- The oriented angle between two vectors is zero if and only if the angle with the vectors
swapped is zero. -/
lemma oangle_eq_zero_iff_oangle_rev_eq_zero {x y : V} : o.oangle x y = 0 ↔ o.oangle y x = 0 :=
by rw [oangle_rev, neg_eq_zero]

/-- The oriented angle between two vectors is zero if and only if they are on the same ray. -/
lemma oangle_eq_zero_iff_same_ray {x y : V} : o.oangle x y = 0 ↔ same_ray ℝ x y :=
begin
  rw [oangle, kahler_apply_apply, complex.arg_coe_angle_eq_iff_eq_to_real, real.angle.to_real_zero,
    complex.arg_eq_zero_iff],
  simpa using o.nonneg_inner_and_area_form_eq_zero_iff_same_ray x y,
end

/-- The oriented angle between two vectors is `π` if and only if the angle with the vectors
swapped is `π`. -/
lemma oangle_eq_pi_iff_oangle_rev_eq_pi {x y : V} : o.oangle x y = π ↔ o.oangle y x = π :=
by rw [oangle_rev, neg_eq_iff_neg_eq, eq_comm, real.angle.neg_coe_pi]

/-- The oriented angle between two vectors is `π` if and only they are nonzero and the first is
on the same ray as the negation of the second. -/
lemma oangle_eq_pi_iff_same_ray_neg {x y : V} :
  o.oangle x y = π ↔ x ≠ 0 ∧ y ≠ 0 ∧ same_ray ℝ x (-y) :=
begin
  rw [←o.oangle_eq_zero_iff_same_ray],
  split,
  { intro h,
    by_cases hx : x = 0, { simpa [hx, real.angle.pi_ne_zero.symm] using h },
    by_cases hy : y = 0, { simpa [hy, real.angle.pi_ne_zero.symm] using h },
    refine ⟨hx, hy, _⟩,
    rw [o.oangle_neg_right hx hy, h, real.angle.coe_pi_add_coe_pi] },
  { rintro ⟨hx, hy, h⟩,
    rwa [o.oangle_neg_right hx hy, ←real.angle.sub_coe_pi_eq_add_coe_pi, sub_eq_zero] at h }
end

/-- The oriented angle between two vectors is zero or `π` if and only if those two vectors are
not linearly independent. -/
lemma oangle_eq_zero_or_eq_pi_iff_not_linear_independent {x y : V} :
  (o.oangle x y = 0 ∨ o.oangle x y = π) ↔ ¬ linear_independent ℝ ![x, y] :=
by rw [oangle_eq_zero_iff_same_ray, oangle_eq_pi_iff_same_ray_neg,
       same_ray_or_ne_zero_and_same_ray_neg_iff_not_linear_independent]

/-- The oriented angle between two vectors is zero or `π` if and only if the first vector is zero
or the second is a multiple of the first. -/
lemma oangle_eq_zero_or_eq_pi_iff_right_eq_smul {x y : V} :
  (o.oangle x y = 0 ∨ o.oangle x y = π) ↔ (x = 0 ∨ ∃ r : ℝ, y = r • x) :=
begin
  rw [oangle_eq_zero_iff_same_ray, oangle_eq_pi_iff_same_ray_neg],
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with h|⟨-, -, h⟩,
    { by_cases hx : x = 0, { simp [hx] },
      obtain ⟨r, -, rfl⟩ := h.exists_nonneg_left hx,
      exact or.inr ⟨r, rfl⟩ },
    { by_cases hx : x = 0, { simp [hx] },
      obtain ⟨r, -, hy⟩ := h.exists_nonneg_left hx,
      refine or.inr ⟨-r, _⟩,
      simp [hy] } },
  { rcases h with rfl|⟨r, rfl⟩, { simp },
    by_cases hx : x = 0, { simp [hx] },
    rcases lt_trichotomy r 0 with hr|hr|hr,
    { rw ←neg_smul,
      exact or.inr ⟨hx, smul_ne_zero hr.ne hx,
                    same_ray_pos_smul_right x (left.neg_pos_iff.2 hr)⟩ },
    { simp [hr] },
    { exact or.inl (same_ray_pos_smul_right x hr) } }
end

/-- The oriented angle between two vectors is not zero or `π` if and only if those two vectors
are linearly independent. -/
lemma oangle_ne_zero_and_ne_pi_iff_linear_independent {x y : V} :
  (o.oangle x y ≠ 0 ∧ o.oangle x y ≠ π) ↔ linear_independent ℝ ![x, y] :=
by rw [←not_or_distrib, ←not_iff_not, not_not, oangle_eq_zero_or_eq_pi_iff_not_linear_independent]

/-- Two vectors are equal if and only if they have equal norms and zero angle between them. -/
lemma eq_iff_norm_eq_and_oangle_eq_zero (x y : V) : x = y ↔ ∥x∥ = ∥y∥ ∧ o.oangle x y = 0 :=
begin
  rw oangle_eq_zero_iff_same_ray,
  split,
  { rintros rfl,
    simp },
  { rcases eq_or_ne y 0 with rfl | hy,
    { simp },
    rintros ⟨h₁, h₂⟩,
    obtain ⟨r, hr, rfl⟩ := h₂.exists_nonneg_right hy,
    have : ∥y∥ ≠ 0 := by simpa using hy,
    obtain rfl : r = 1,
    { apply mul_right_cancel₀ this,
      simpa [norm_smul, _root_.abs_of_nonneg hr] using h₁ },
    simp },
end

/-- Two vectors with equal norms are equal if and only if they have zero angle between them. -/
lemma eq_iff_oangle_eq_zero_of_norm_eq {x y : V} (h : ∥x∥ = ∥y∥) : x = y ↔ o.oangle x y = 0 :=
⟨λ he, ((o.eq_iff_norm_eq_and_oangle_eq_zero x y).1 he).2,
 λ ha, (o.eq_iff_norm_eq_and_oangle_eq_zero x y).2 ⟨h, ha⟩⟩

/-- Two vectors with zero angle between them are equal if and only if they have equal norms. -/
lemma eq_iff_norm_eq_of_oangle_eq_zero {x y : V} (h : o.oangle x y = 0) : x = y ↔ ∥x∥ = ∥y∥ :=
⟨λ he, ((o.eq_iff_norm_eq_and_oangle_eq_zero x y).1 he).1,
 λ hn, (o.eq_iff_norm_eq_and_oangle_eq_zero x y).2 ⟨hn, h⟩⟩

/-- Given three nonzero vectors, the angle between the first and the second plus the angle
between the second and the third equals the angle between the first and the third. -/
@[simp] lemma oangle_add {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  o.oangle x y + o.oangle y z = o.oangle x z :=
begin
  simp_rw [oangle],
  rw [←complex.arg_mul_coe_angle, o.kahler_mul y x z],
  congr' 1,
  convert complex.arg_real_mul _ (_ : 0 < ∥y∥ ^ 2) using 2,
  { norm_cast },
  { have : 0 < ∥y∥ := by simpa using hy,
    positivity },
  { exact o.kahler_ne_zero hx hy, },
  { exact o.kahler_ne_zero hy hz }
end

/-- Given three nonzero vectors, the angle between the second and the third plus the angle
between the first and the second equals the angle between the first and the third. -/
@[simp] lemma oangle_add_swap {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
   o.oangle y z + o.oangle x y = o.oangle x z :=
by rw [add_comm, o.oangle_add hx hy hz]

/-- Given three nonzero vectors, the angle between the first and the third minus the angle
between the first and the second equals the angle between the second and the third. -/
@[simp] lemma oangle_sub_left {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  o.oangle x z - o.oangle x y = o.oangle y z :=
by rw [sub_eq_iff_eq_add, o.oangle_add_swap hx hy hz]

/-- Given three nonzero vectors, the angle between the first and the third minus the angle
between the second and the third equals the angle between the first and the second. -/
@[simp] lemma oangle_sub_right {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  o.oangle x z - o.oangle y z = o.oangle x y :=
by rw [sub_eq_iff_eq_add, o.oangle_add hx hy hz]

/-- Given three nonzero vectors, adding the angles between them in cyclic order results in 0. -/
@[simp] lemma oangle_add_cyc3 {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  o.oangle x y + o.oangle y z + o.oangle z x = 0 :=
by simp [hx, hy, hz]

/-- Given three nonzero vectors, adding the angles between them in cyclic order, with the first
vector in each angle negated, results in π. If the vectors add to 0, this is a version of the
sum of the angles of a triangle. -/
@[simp] lemma oangle_add_cyc3_neg_left {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  o.oangle (-x) y + o.oangle (-y) z + o.oangle (-z) x = π :=
by rw [o.oangle_neg_left hx hy, o.oangle_neg_left hy hz, o.oangle_neg_left hz hx,
       (show o.oangle x y + π + (o.oangle y z + π) + (o.oangle z x + π) =
         o.oangle x y + o.oangle y z + o.oangle z x + (π + π + π : real.angle), by abel),
       o.oangle_add_cyc3 hx hy hz, real.angle.coe_pi_add_coe_pi, zero_add, zero_add]

/-- Given three nonzero vectors, adding the angles between them in cyclic order, with the second
vector in each angle negated, results in π. If the vectors add to 0, this is a version of the
sum of the angles of a triangle. -/
@[simp] lemma oangle_add_cyc3_neg_right {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  o.oangle x (-y) + o.oangle y (-z) + o.oangle z (-x) = π :=
by simp_rw [←oangle_neg_left_eq_neg_right, o.oangle_add_cyc3_neg_left hx hy hz]

/-- Pons asinorum, oriented vector angle form. -/
lemma oangle_sub_eq_oangle_sub_rev_of_norm_eq {x y : V} (h : ∥x∥ = ∥y∥) :
  o.oangle x (x - y) = o.oangle (y - x) y :=
by simp [oangle, h]

/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
vector angle form. -/
lemma oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq {x y : V} (hn : x ≠ y) (h : ∥x∥ = ∥y∥) :
  o.oangle y x = π - (2 : ℤ) • o.oangle (y - x) y :=
begin
  rw two_zsmul,
  rw [←o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h] { occs := occurrences.pos [1] },
  rw [eq_sub_iff_add_eq, ←oangle_neg_neg, ←add_assoc],
  have hy : y ≠ 0,
  { rintro rfl,
    rw [norm_zero, norm_eq_zero] at h,
    exact hn h },
  have hx : x ≠ 0 := norm_ne_zero_iff.1 (h.symm ▸ norm_ne_zero_iff.2 hy),
  convert o.oangle_add_cyc3_neg_right (neg_ne_zero.2 hy) hx (sub_ne_zero_of_ne hn.symm);
    simp
end

/-- Angle at center of a circle equals twice angle at circumference, oriented vector angle
form. -/
lemma oangle_eq_two_zsmul_oangle_sub_of_norm_eq {x y z : V} (hxyne : x ≠ y) (hxzne : x ≠ z)
  (hxy : ∥x∥ = ∥y∥) (hxz : ∥x∥ = ∥z∥) : o.oangle y z = (2 : ℤ) • o.oangle (y - x) (z - x) :=
begin
  have hy : y ≠ 0,
  { rintro rfl,
    rw [norm_zero, norm_eq_zero] at hxy,
    exact hxyne hxy },
  have hx : x ≠ 0 := norm_ne_zero_iff.1 (hxy.symm ▸ norm_ne_zero_iff.2 hy),
  have hz : z ≠ 0 := norm_ne_zero_iff.1 (hxz ▸ norm_ne_zero_iff.2 hx),
  calc o.oangle y z = o.oangle x z - o.oangle x y : (o.oangle_sub_left hx hy hz).symm
       ...           = (π - (2 : ℤ) • o.oangle (x - z) x) -
                       (π - (2 : ℤ) • o.oangle (x - y) x) :
         by rw [o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hxzne.symm hxz.symm,
                o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hxyne.symm hxy.symm]
       ...           = (2 : ℤ) • (o.oangle (x - y) x - o.oangle (x - z) x) : by abel
       ...           = (2 : ℤ) • o.oangle (x - y) (x - z) :
         by rw o.oangle_sub_right (sub_ne_zero_of_ne hxyne) (sub_ne_zero_of_ne hxzne) hx
       ...           = (2 : ℤ) • o.oangle (y - x) (z - x) :
         by rw [←oangle_neg_neg, neg_sub, neg_sub]
end

/-- Angle at center of a circle equals twice angle at circumference, oriented vector angle
form with radius specified. -/
lemma oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real {x y z : V} (hxyne : x ≠ y) (hxzne : x ≠ z)
  {r : ℝ} (hx : ∥x∥ = r) (hy : ∥y∥ = r) (hz : ∥z∥ = r) :
  o.oangle y z = (2 : ℤ) • o.oangle (y - x) (z - x) :=
o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq hxyne hxzne (hy.symm ▸ hx) (hz.symm ▸ hx)

/-- Oriented vector angle version of "angles in same segment are equal" and "opposite angles of
a cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same
result), represented here as equality of twice the angles. -/
lemma two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq {x₁ x₂ y z : V} (hx₁yne : x₁ ≠ y)
  (hx₁zne : x₁ ≠ z) (hx₂yne : x₂ ≠ y) (hx₂zne : x₂ ≠ z) {r : ℝ} (hx₁ : ∥x₁∥ = r) (hx₂ : ∥x₂∥ = r)
  (hy : ∥y∥ = r) (hz : ∥z∥ = r) :
  (2 : ℤ) • o.oangle (y - x₁) (z - x₁) = (2 : ℤ) • o.oangle (y - x₂) (z - x₂) :=
o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₁yne hx₁zne hx₁ hy hz ▸
  o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₂yne hx₂zne hx₂ hy hz

/-- Auxiliary construction to build a rotation by the oriented angle `θ`. -/
def rotation_aux (θ : real.angle) : V →ₗᵢ[ℝ] V :=
linear_map.isometry_of_inner
  (real.angle.cos θ • linear_map.id
        + real.angle.sin θ • ↑(linear_isometry_equiv.to_linear_equiv J))
  begin
    intros x y,
    simp only [is_R_or_C.conj_to_real, id.def, linear_map.smul_apply, linear_map.add_apply,
      linear_map.id_coe, linear_equiv.coe_coe, linear_isometry_equiv.coe_to_linear_equiv,
      orientation.area_form_right_angle_rotation_left,
      orientation.inner_right_angle_rotation_left,
      orientation.inner_right_angle_rotation_right,
      inner_add_left, inner_smul_left, inner_add_right, inner_smul_right],
    linear_combination inner x y * θ.cos_sq_add_sin_sq,
  end

@[simp] lemma rotation_aux_apply (θ : real.angle) (x : V) :
  o.rotation_aux θ x = real.angle.cos θ • x + real.angle.sin θ • J x :=
rfl

/-- A rotation by the oriented angle `θ`. -/
def rotation (θ : real.angle) : V ≃ₗᵢ[ℝ] V :=
linear_isometry_equiv.of_linear_isometry
  (o.rotation_aux θ)
  (real.angle.cos θ • linear_map.id - real.angle.sin θ • ↑(linear_isometry_equiv.to_linear_equiv J))
  begin
    ext x,
    convert congr_arg (λ t : ℝ, t • x) θ.cos_sq_add_sin_sq using 1,
    { simp only [o.right_angle_rotation_right_angle_rotation, o.rotation_aux_apply,
        function.comp_app, id.def, linear_equiv.coe_coe, linear_isometry.coe_to_linear_map,
        linear_isometry_equiv.coe_to_linear_equiv, map_smul, map_sub, linear_map.coe_comp,
        linear_map.id_coe, linear_map.smul_apply, linear_map.sub_apply, ← mul_smul, add_smul,
        smul_add, smul_neg, smul_sub, mul_comm, sq],
      abel },
    { simp },
  end
  begin
    ext x,
    convert congr_arg (λ t : ℝ, t • x) θ.cos_sq_add_sin_sq using 1,
    { simp only [o.right_angle_rotation_right_angle_rotation, o.rotation_aux_apply,
        function.comp_app, id.def, linear_equiv.coe_coe, linear_isometry.coe_to_linear_map,
        linear_isometry_equiv.coe_to_linear_equiv, map_add, map_smul, linear_map.coe_comp,
        linear_map.id_coe, linear_map.smul_apply, linear_map.sub_apply, add_smul, ← mul_smul,
        mul_comm, smul_add, smul_neg, sq],
      abel },
    { simp },
  end

lemma rotation_apply (θ : real.angle) (x : V) :
  o.rotation θ x = real.angle.cos θ • x + real.angle.sin θ • J x :=
rfl

lemma rotation_symm_apply (θ : real.angle) (x : V) :
  (o.rotation θ).symm x = real.angle.cos θ • x - real.angle.sin θ • J x :=
rfl

attribute [irreducible] rotation

lemma rotation_eq_matrix_to_lin (θ : real.angle) {x : V} (hx : x ≠ 0) :
  (o.rotation θ).to_linear_map
  = matrix.to_lin
      (o.basis_right_angle_rotation x hx) (o.basis_right_angle_rotation x hx)
      !![θ.cos, -θ.sin; θ.sin, θ.cos] :=
begin
  apply (o.basis_right_angle_rotation x hx).ext,
  intros i,
  fin_cases i,
  { rw matrix.to_lin_self,
    simp [rotation_apply, fin.sum_univ_succ] },
  { rw matrix.to_lin_self,
    simp [rotation_apply, fin.sum_univ_succ, add_comm] },
end

/-- The determinant of `rotation` (as a linear map) is equal to `1`. -/
@[simp] lemma det_rotation (θ : real.angle) :
  (o.rotation θ).to_linear_map.det = 1 :=
begin
  haveI : nontrivial V :=
    finite_dimensional.nontrivial_of_finrank_eq_succ (fact.out (finrank ℝ V = 2)),
  obtain ⟨x, hx⟩ : ∃ x, x ≠ (0:V) := exists_ne (0:V),
  rw o.rotation_eq_matrix_to_lin θ hx,
  simpa [sq] using θ.cos_sq_add_sin_sq,
end

/-- The determinant of `rotation` (as a linear equiv) is equal to `1`. -/
@[simp] lemma linear_equiv_det_rotation (θ : real.angle) :
  (o.rotation θ).to_linear_equiv.det = 1 :=
units.ext $ o.det_rotation θ

/-- The inverse of `rotation` is rotation by the negation of the angle. -/
@[simp] lemma rotation_symm (θ : real.angle) : (o.rotation θ).symm = o.rotation (-θ) :=
by ext; simp [o.rotation_apply, o.rotation_symm_apply, sub_eq_add_neg]

/-- Rotation by 0 is the identity. -/
@[simp] lemma rotation_zero : o.rotation 0 = linear_isometry_equiv.refl ℝ V :=
by ext; simp [rotation]

/-- Rotation by π is negation. -/
@[simp] lemma rotation_pi : o.rotation π = linear_isometry_equiv.neg ℝ :=
begin
  ext x,
  simp [rotation]
end

/-- Rotation by π / 2 is the "right-angle-rotation" map `J`. -/
lemma rotation_pi_div_two : o.rotation (π / 2 : ℝ) = J :=
begin
  ext x,
  simp [rotation],
end

/-- Rotating twice is equivalent to rotating by the sum of the angles. -/
@[simp] lemma rotation_trans (θ₁ θ₂ : real.angle) :
  (o.rotation θ₁).trans (o.rotation θ₂) = o.rotation (θ₂ + θ₁) :=
begin
  ext x,
  simp only [o.rotation_apply, ←mul_smul, real.angle.cos_add, real.angle.sin_add, add_smul,
    sub_smul, linear_isometry_equiv.trans_apply, smul_add, linear_isometry_equiv.map_add,
    linear_isometry_equiv.map_smul, right_angle_rotation_right_angle_rotation, smul_neg],
  ring_nf,
  abel,
end

/-- Rotating the first of two vectors by `θ` scales their Kahler form by `cos θ - sin θ * I`. -/
@[simp] lemma kahler_rotation_left (x y : V) (θ : real.angle) :
  o.kahler (o.rotation θ x) y = conj (θ.exp_map_circle : ℂ) * o.kahler x y :=
begin
  simp only [o.rotation_apply, map_add, map_mul, linear_map.map_smulₛₗ, ring_hom.id_apply,
    linear_map.add_apply, linear_map.smul_apply, real_smul, kahler_right_angle_rotation_left,
    real.angle.coe_exp_map_circle, is_R_or_C.conj_of_real, conj_I],
  ring,
end

/-- Rotating the first of two vectors by `θ` scales their Kahler form by `cos (-θ) + sin (-θ) * I`.
-/
lemma kahler_rotation_left' (x y : V) (θ : real.angle) :
  o.kahler (o.rotation θ x) y = (-θ).exp_map_circle * o.kahler x y :=
by simpa [coe_inv_circle_eq_conj, -kahler_rotation_left] using o.kahler_rotation_left x y θ

/-- Rotating the second of two vectors by `θ` scales their Kahler form by `cos θ + sin θ * I`. -/
@[simp] lemma kahler_rotation_right (x y : V) (θ : real.angle) :
  o.kahler x (o.rotation θ y) = θ.exp_map_circle * o.kahler x y :=
begin
  simp only [o.rotation_apply, map_add, linear_map.map_smulₛₗ, ring_hom.id_apply, real_smul,
    kahler_right_angle_rotation_right, real.angle.coe_exp_map_circle],
  ring,
end

/-- Rotating the first vector by `θ` subtracts `θ` from the angle between two vectors. -/
@[simp] lemma oangle_rotation_left {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : real.angle) :
  o.oangle (o.rotation θ x) y = o.oangle x y - θ :=
begin
  simp only [oangle, o.kahler_rotation_left'],
  rw [complex.arg_mul_coe_angle, real.angle.arg_exp_map_circle],
  { abel },
  { exact ne_zero_of_mem_circle _ },
  { exact o.kahler_ne_zero hx hy },
end

/-- Rotating the second vector by `θ` adds `θ` to the angle between two vectors. -/
@[simp] lemma oangle_rotation_right {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : real.angle) :
  o.oangle x (o.rotation θ y) = o.oangle x y + θ :=
begin
  simp only [oangle, o.kahler_rotation_right],
  rw [complex.arg_mul_coe_angle, real.angle.arg_exp_map_circle],
  { abel },
  { exact ne_zero_of_mem_circle _ },
  { exact o.kahler_ne_zero hx hy },
end

/-- The rotation of a vector by `θ` has an angle of `-θ` from that vector. -/
@[simp] lemma oangle_rotation_self_left {x : V} (hx : x ≠ 0) (θ : real.angle) :
  o.oangle (o.rotation θ x) x = -θ :=
by simp [hx]

/-- A vector has an angle of `θ` from the rotation of that vector by `θ`. -/
@[simp] lemma oangle_rotation_self_right {x : V} (hx : x ≠ 0) (θ : real.angle) :
  o.oangle x (o.rotation θ x) = θ :=
by simp [hx]

/-- Rotating the first vector by the angle between the two vectors results an an angle of 0. -/
@[simp] lemma oangle_rotation_oangle_left (x y : V) :
  o.oangle (o.rotation (o.oangle x y) x) y = 0 :=
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
  o.oangle y (o.rotation (o.oangle x y) x) = 0 :=
begin
  rw [oangle_rev],
  simp
end

/-- Rotating both vectors by the same angle does not change the angle between those vectors. -/
@[simp] lemma oangle_rotation (x y : V) (θ : real.angle) :
  o.oangle (o.rotation θ x) (o.rotation θ y) = o.oangle x y :=
begin
  by_cases hx : x = 0; by_cases hy : y = 0;
    simp [hx, hy]
end

/-- A rotation of a nonzero vector equals that vector if and only if the angle is zero. -/
@[simp] lemma rotation_eq_self_iff_angle_eq_zero {x : V} (hx : x ≠ 0) (θ : real.angle) :
  o.rotation θ x = x ↔ θ = 0 :=
begin
  split,
  { intro h,
    rw eq_comm,
    simpa [hx, h] using o.oangle_rotation_right hx hx θ },
  { intro h,
    simp [h] }
end

/-- A nonzero vector equals a rotation of that vector if and only if the angle is zero. -/
@[simp] lemma eq_rotation_self_iff_angle_eq_zero {x : V} (hx : x ≠ 0) (θ : real.angle) :
  x = o.rotation θ x ↔ θ = 0 :=
by rw [←o.rotation_eq_self_iff_angle_eq_zero hx, eq_comm]

/-- A rotation of a vector equals that vector if and only if the vector or the angle is zero. -/
lemma rotation_eq_self_iff (x : V) (θ : real.angle) :
  o.rotation θ x = x ↔ x = 0 ∨ θ = 0 :=
begin
  by_cases h : x = 0;
    simp [h]
end

/-- A vector equals a rotation of that vector if and only if the vector or the angle is zero. -/
lemma eq_rotation_self_iff (x : V) (θ : real.angle) :
  x = o.rotation θ x ↔ x = 0 ∨ θ = 0 :=
by rw [←rotation_eq_self_iff, eq_comm]

/-- Rotating a vector by the angle to another vector gives the second vector if and only if the
norms are equal. -/
@[simp] lemma rotation_oangle_eq_iff_norm_eq (x y : V) :
  o.rotation (o.oangle x y) x = y ↔ ∥x∥ = ∥y∥ :=
begin
  split,
  { intro h,
    rw [←h, linear_isometry_equiv.norm_map] },
  { intro h,
    rw o.eq_iff_oangle_eq_zero_of_norm_eq;
      simp [h] }
end

/-- The angle between two nonzero vectors is `θ` if and only if the second vector is the first
rotated by `θ` and scaled by the ratio of the norms. -/
lemma oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
  (θ : real.angle) : o.oangle x y = θ ↔ y = (∥y∥ / ∥x∥) • o.rotation θ x :=
begin
  have hp := div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx),
  split,
  { rintro rfl,
    rw [←linear_isometry_equiv.map_smul, ←o.oangle_smul_left_of_pos x y hp,
        eq_comm, rotation_oangle_eq_iff_norm_eq, norm_smul, real.norm_of_nonneg hp.le,
        div_mul_cancel _ (norm_ne_zero_iff.2 hx)] },
  { intro hye,
    rw [hye, o.oangle_smul_right_of_pos _ _ hp, o.oangle_rotation_self_right hx] }
end

/-- The angle between two nonzero vectors is `θ` if and only if the second vector is the first
rotated by `θ` and scaled by a positive real. -/
lemma oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
  (θ : real.angle) : o.oangle x y = θ ↔ ∃ r : ℝ, 0 < r ∧ y = r • o.rotation θ x :=
begin
  split,
  { intro h,
    rw o.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy at h,
    exact ⟨∥y∥ / ∥x∥, div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx), h⟩ },
  { rintro ⟨r, hr, rfl⟩,
    rw [o.oangle_smul_right_of_pos _ _ hr, o.oangle_rotation_self_right hx] }
end

/-- The angle between two vectors is `θ` if and only if they are nonzero and the second vector
is the first rotated by `θ` and scaled by the ratio of the norms, or `θ` and at least one of the
vectors are zero. -/
lemma oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero {x y : V} (θ : real.angle) :
  o.oangle x y = θ ↔
    (x ≠ 0 ∧ y ≠ 0 ∧ y = (∥y∥ / ∥x∥) • o.rotation θ x) ∨ (θ = 0 ∧ (x = 0 ∨ y = 0)) :=
begin
  by_cases hx : x = 0,
  { simp [hx, eq_comm] },
  { by_cases hy : y = 0,
    { simp [hy, eq_comm] },
    { rw o.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy,
      simp [hx, hy] } }
end

/-- The angle between two vectors is `θ` if and only if they are nonzero and the second vector
is the first rotated by `θ` and scaled by a positive real, or `θ` and at least one of the
vectors are zero. -/
lemma oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero {x y : V} (θ : real.angle) :
  o.oangle x y = θ ↔
    (x ≠ 0 ∧ y ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • o.rotation θ x) ∨ (θ = 0 ∧ (x = 0 ∨ y = 0)) :=
begin
  by_cases hx : x = 0,
  { simp [hx, eq_comm] },
  { by_cases hy : y = 0,
    { simp [hy, eq_comm] },
    { rw o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero hx hy,
      simp [hx, hy] } }
end

/-- Any linear isometric equivalence in `V` with positive determinant is `rotation`. -/
lemma exists_linear_isometry_equiv_eq_of_det_pos {f : V ≃ₗᵢ[ℝ] V}
  (hd : 0 < (f.to_linear_equiv : V →ₗ[ℝ] V).det) : ∃ θ : real.angle, f = o.rotation θ :=
begin
  haveI : nontrivial V :=
    finite_dimensional.nontrivial_of_finrank_eq_succ (fact.out (finrank ℝ V = 2)),
  obtain ⟨x, hx⟩ : ∃ x, x ≠ (0:V) := exists_ne (0:V),
  use o.oangle x (f x),
  apply linear_isometry_equiv.to_linear_equiv_injective,
  apply linear_equiv.to_linear_map_injective,
  apply (o.basis_right_angle_rotation x hx).ext,
  intros i,
  symmetry,
  fin_cases i,
  { simp },
  have : o.oangle (J x) (f (J x)) = o.oangle x (f x),
  { simp only [oangle, o.linear_isometry_equiv_comp_right_angle_rotation f hd,
      o.kahler_comp_right_angle_rotation] },
  simp [← this],
end

/-- The angle between two vectors, with respect to an orientation given by `orientation.map`
with a linear isometric equivalence, equals the angle between those two vectors, transformed by
the inverse of that equivalence, with respect to the original orientation. -/
@[simp] lemma oangle_map (x y : V') (f : V ≃ₗᵢ[ℝ] V') :
  (orientation.map (fin 2) f.to_linear_equiv o).oangle x y = o.oangle (f.symm x) (f.symm y) :=
by simp [oangle, o.kahler_map]

@[simp] protected lemma _root_.complex.oangle (w z : ℂ) :
  complex.orientation.oangle w z = complex.arg (conj w * z) :=
by simp [oangle]

/-- The oriented angle on an oriented real inner product space of dimension 2 can be evaluated in
terms of a complex-number representation of the space. -/
lemma oangle_map_complex (f : V ≃ₗᵢ[ℝ] ℂ)
  (hf : (orientation.map (fin 2) f.to_linear_equiv o) = complex.orientation) (x y : V) :
  o.oangle x y = complex.arg (conj (f x) * f y) :=
begin
  rw [← complex.oangle, ← hf, o.oangle_map],
  simp,
end

/-- Negating the orientation negates the value of `oangle`. -/
lemma oangle_neg_orientation_eq_neg (x y : V) : (-o).oangle x y = -(o.oangle x y) :=
by simp [oangle]

lemma rotation_map (θ : real.angle) (f : V ≃ₗᵢ[ℝ] V') (x : V') :
  (orientation.map (fin 2) f.to_linear_equiv o).rotation θ x
  = f (o.rotation θ (f.symm x)) :=
by simp [rotation_apply, o.right_angle_rotation_map]

@[simp] protected lemma _root_.complex.rotation (θ : real.angle) (z : ℂ) :
  complex.orientation.rotation θ z = θ.exp_map_circle * z :=
begin
  simp only [rotation_apply, complex.right_angle_rotation, real.angle.coe_exp_map_circle,
    real_smul],
  ring
end

/-- Rotation in an oriented real inner product space of dimension 2 can be evaluated in terms of a
complex-number representation of the space. -/
lemma rotation_map_complex (θ : real.angle) (f : V ≃ₗᵢ[ℝ] ℂ)
  (hf : (orientation.map (fin 2) f.to_linear_equiv o) = complex.orientation) (x : V) :
  f (o.rotation θ x) = θ.exp_map_circle * f x :=
begin
  rw [← complex.rotation, ← hf, o.rotation_map],
  simp,
end

/-- Negating the orientation negates the angle in `rotation`. -/
lemma rotation_neg_orientation_eq_neg (θ : real.angle) :
  (-o).rotation θ = o.rotation (-θ) :=
linear_isometry_equiv.ext $ by simp [rotation_apply]

/-- The inner product of two vectors is the product of the norms and the cosine of the oriented
angle between the vectors. -/
lemma inner_eq_norm_mul_norm_mul_cos_oangle (x y : V) :
  ⟪x, y⟫ = ∥x∥ * ∥y∥ * real.angle.cos (o.oangle x y) :=
begin
  by_cases hx : x = 0, { simp [hx] },
  by_cases hy : y = 0, { simp [hy] },
  have : ∥x∥ ≠ 0 := by simpa using hx,
  have : ∥y∥ ≠ 0 := by simpa using hy,
  rw [oangle, real.angle.cos_coe, complex.cos_arg, o.abs_kahler],
  { simp only [kahler_apply_apply, real_smul, add_re, of_real_re, mul_re, I_re, of_real_im],
    field_simp,
    ring },
  { exact o.kahler_ne_zero hx hy }
end

/-- The cosine of the oriented angle between two nonzero vectors is the inner product divided by
the product of the norms. -/
lemma cos_oangle_eq_inner_div_norm_mul_norm {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  real.angle.cos (o.oangle x y) = ⟪x, y⟫ / (∥x∥ * ∥y∥) :=
begin
  rw o.inner_eq_norm_mul_norm_mul_cos_oangle,
  field_simp [norm_ne_zero_iff.2 hx, norm_ne_zero_iff.2 hy],
  ring
end

/-- The cosine of the oriented angle between two nonzero vectors equals that of the unoriented
angle. -/
lemma cos_oangle_eq_cos_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  real.angle.cos (o.oangle x y) = real.cos (inner_product_geometry.angle x y) :=
by rw [o.cos_oangle_eq_inner_div_norm_mul_norm hx hy, inner_product_geometry.cos_angle]

/-- The oriented angle between two nonzero vectors is plus or minus the unoriented angle. -/
lemma oangle_eq_angle_or_eq_neg_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  o.oangle x y = inner_product_geometry.angle x y ∨
    o.oangle x y = -inner_product_geometry.angle x y :=
real.angle.cos_eq_real_cos_iff_eq_or_eq_neg.1 $ o.cos_oangle_eq_cos_angle hx hy

/-- The unoriented angle between two nonzero vectors is the absolute value of the oriented angle,
converted to a real. -/
lemma angle_eq_abs_oangle_to_real {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  inner_product_geometry.angle x y = |(o.oangle x y).to_real| :=
begin
  have h0 := inner_product_geometry.angle_nonneg x y,
  have hpi := inner_product_geometry.angle_le_pi x y,
  rcases o.oangle_eq_angle_or_eq_neg_angle hx hy with (h|h),
  { rw [h, eq_comm, real.angle.abs_to_real_coe_eq_self_iff],
    exact ⟨h0, hpi⟩ },
  { rw [h, eq_comm, real.angle.abs_to_real_neg_coe_eq_self_iff],
    exact ⟨h0, hpi⟩ }
end

/-- If the sign of the oriented angle between two vectors is zero, either one of the vectors is
zero or the unoriented angle is 0 or π. -/
lemma eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero {x y : V}
  (h : (o.oangle x y).sign = 0) :
  x = 0 ∨ y = 0 ∨ inner_product_geometry.angle x y = 0 ∨ inner_product_geometry.angle x y = π :=
begin
  by_cases hx : x = 0, { simp [hx] },
  by_cases hy : y = 0, { simp [hy] },
  rw o.angle_eq_abs_oangle_to_real hx hy,
  rw real.angle.sign_eq_zero_iff at h,
  rcases h with h|h;
    simp [h, real.pi_pos.le]
end

/-- If two unoriented angles are equal, and the signs of the corresponding oriented angles are
equal, then the oriented angles are equal (even in degenerate cases). -/
lemma oangle_eq_of_angle_eq_of_sign_eq {w x y z : V}
  (h : inner_product_geometry.angle w x = inner_product_geometry.angle y z)
  (hs : (o.oangle w x).sign = (o.oangle y z).sign) : o.oangle w x = o.oangle y z :=
begin
  by_cases h0 : (w = 0 ∨ x = 0) ∨ (y = 0 ∨ z = 0),
  { have hs' : (o.oangle w x).sign = 0 ∧ (o.oangle y z).sign = 0,
    { rcases h0 with (rfl|rfl)|rfl|rfl,
      { simpa using hs.symm },
      { simpa using hs.symm },
      { simpa using hs },
      { simpa using hs } },
    rcases hs' with ⟨hswx, hsyz⟩,
    have h' : inner_product_geometry.angle w x = π / 2 ∧ inner_product_geometry.angle y z = π / 2,
    { rcases h0 with (rfl|rfl)|rfl|rfl,
      { simpa using h.symm },
      { simpa using h.symm },
      { simpa using h },
      { simpa using h } },
    rcases h' with ⟨hwx, hyz⟩,
    have hpi : π / 2 ≠ π,
    { intro hpi,
      rw [div_eq_iff, eq_comm, ←sub_eq_zero, mul_two, add_sub_cancel] at hpi,
      { exact real.pi_pos.ne.symm hpi },
      { exact two_ne_zero } },
    have h0wx : (w = 0 ∨ x = 0),
    { have h0' := o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero hswx,
      simpa [hwx, real.pi_pos.ne.symm, hpi] using h0' },
    have h0yz : (y = 0 ∨ z = 0),
    { have h0' := o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero hsyz,
      simpa [hyz, real.pi_pos.ne.symm, hpi] using h0' },
    rcases h0wx with h0wx|h0wx; rcases h0yz with h0yz|h0yz;
      simp [h0wx, h0yz] },
  { push_neg at h0,
    rw real.angle.eq_iff_abs_to_real_eq_of_sign_eq hs,
    rwa [o.angle_eq_abs_oangle_to_real h0.1.1 h0.1.2,
         o.angle_eq_abs_oangle_to_real h0.2.1 h0.2.2] at h }
end

/-- If the signs of two oriented angles between nonzero vectors are equal, the oriented angles are
equal if and only if the unoriented angles are equal. -/
lemma angle_eq_iff_oangle_eq_of_sign_eq {w x y z : V} (hw : w ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
  (hz : z ≠ 0) (hs : (o.oangle w x).sign = (o.oangle y z).sign) :
  inner_product_geometry.angle w x = inner_product_geometry.angle y z ↔
    o.oangle w x = o.oangle y z :=
begin
  refine ⟨λ h, o.oangle_eq_of_angle_eq_of_sign_eq h hs, λ h, _⟩,
  rw [o.angle_eq_abs_oangle_to_real hw hx, o.angle_eq_abs_oangle_to_real hy hz, h]
end

/-- The oriented angle between two nonzero vectors is zero if and only if the unoriented angle
is zero. -/
lemma oangle_eq_zero_iff_angle_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  o.oangle x y = 0 ↔ inner_product_geometry.angle x y = 0 :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { simpa [o.angle_eq_abs_oangle_to_real hx hy] },
  { have ha := o.oangle_eq_angle_or_eq_neg_angle hx hy,
    rw h at ha,
    simpa using ha }
end

/-- The oriented angle between two vectors is `π` if and only if the unoriented angle is `π`. -/
lemma oangle_eq_pi_iff_angle_eq_pi {x y : V} :
  o.oangle x y = π ↔ inner_product_geometry.angle x y = π :=
begin
  by_cases hx : x = 0, { simp [hx, real.angle.pi_ne_zero.symm, div_eq_mul_inv, mul_right_eq_self₀,
                               not_or_distrib, real.pi_ne_zero], norm_num },
  by_cases hy : y = 0, { simp [hy, real.angle.pi_ne_zero.symm, div_eq_mul_inv, mul_right_eq_self₀,
                               not_or_distrib, real.pi_ne_zero], norm_num },
  refine ⟨λ h, _, λ h, _⟩,
  { rw [o.angle_eq_abs_oangle_to_real hx hy, h],
    simp [real.pi_pos.le] },
  { have ha := o.oangle_eq_angle_or_eq_neg_angle hx hy,
    rw h at ha,
    simpa using ha }
end

/-- Negating the first vector passed to `oangle` negates the sign of the angle. -/
@[simp] lemma oangle_sign_neg_left (x y : V) :
  (o.oangle (-x) y).sign = -((o.oangle x y).sign) :=
begin
  by_cases hx : x = 0, { simp [hx] },
  by_cases hy : y = 0, { simp [hy] },
  rw [o.oangle_neg_left hx hy, real.angle.sign_add_pi]
end

/-- Negating the second vector passed to `oangle` negates the sign of the angle. -/
@[simp] lemma oangle_sign_neg_right (x y : V) :
  (o.oangle x (-y)).sign = -((o.oangle x y).sign) :=
begin
  by_cases hx : x = 0, { simp [hx] },
  by_cases hy : y = 0, { simp [hy] },
  rw [o.oangle_neg_right hx hy, real.angle.sign_add_pi]
end

/-- Multiplying the first vector passed to `oangle` by a real multiplies the sign of the angle by
the sign of the real. -/
@[simp] lemma oangle_sign_smul_left (x y : V) (r : ℝ) :
  (o.oangle (r • x) y).sign = sign r * (o.oangle x y).sign :=
begin
  rcases lt_trichotomy r 0 with h|h|h;
    simp [h]
end

/-- Multiplying the second vector passed to `oangle` by a real multiplies the sign of the angle by
the sign of the real. -/
@[simp] lemma oangle_sign_smul_right (x y : V) (r : ℝ) :
  (o.oangle x (r • y)).sign = sign r * (o.oangle x y).sign :=
begin
  rcases lt_trichotomy r 0 with h|h|h;
    simp [h]
end

/-- Auxiliary lemma for the proof of `oangle_sign_smul_add_right`; not intended to be used
outside of that proof. -/
lemma oangle_smul_add_right_eq_zero_or_eq_pi_iff {x y : V} (r : ℝ) :
  (o.oangle x (r • x + y) = 0 ∨ o.oangle x (r • x + y) = π) ↔
    (o.oangle x y = 0 ∨ o.oangle x y = π) :=
begin
  simp_rw [oangle_eq_zero_or_eq_pi_iff_not_linear_independent,
           fintype.not_linear_independent_iff, fin.sum_univ_two, fin.exists_fin_two],
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨m, h, hm⟩,
    change m 0 • x + m 1 • (r • x + y) = 0 at h,
    refine ⟨![m 0 + m 1 * r, m 1], _⟩,
    change (m 0 + m 1 * r) • x + m 1 • y = 0 ∧ (m 0 + m 1 * r ≠ 0 ∨ m 1 ≠ 0),
    rw [smul_add, smul_smul, ←add_assoc, ←add_smul] at h,
    refine ⟨h, not_and_distrib.1 (λ h0, _)⟩,
    obtain ⟨h0, h1⟩ := h0,
    rw h1 at h0 hm,
    rw [zero_mul, add_zero] at h0,
    simpa [h0] using hm },
  { rcases h with ⟨m, h, hm⟩,
    change m 0 • x + m 1 • y = 0 at h,
    refine ⟨![m 0 - m 1 * r, m 1], _⟩,
    change (m 0 - m 1 * r) • x + m 1 • (r • x + y) = 0 ∧ (m 0 - m 1 * r ≠ 0 ∨ m 1 ≠ 0),
    rw [sub_smul, smul_add, smul_smul, ←add_assoc, sub_add_cancel],
    refine ⟨h, not_and_distrib.1 (λ h0, _)⟩,
    obtain ⟨h0, h1⟩ := h0,
    rw h1 at h0 hm,
    rw [zero_mul, sub_zero] at h0,
    simpa [h0] using hm }
end

/-- Adding a multiple of the first vector passed to `oangle` to the second vector does not change
the sign of the angle. -/
@[simp] lemma oangle_sign_smul_add_right (x y : V) (r : ℝ) :
  (o.oangle x (r • x + y)).sign = (o.oangle x y).sign :=
begin
  by_cases h : o.oangle x y = 0 ∨ o.oangle x y = π,
  { rwa [real.angle.sign_eq_zero_iff.2 h, real.angle.sign_eq_zero_iff,
         oangle_smul_add_right_eq_zero_or_eq_pi_iff] },
  have h' : ∀ r' : ℝ, o.oangle x (r' • x + y) ≠ 0 ∧ o.oangle x (r' • x + y) ≠ π,
  { intro r',
    rwa [←o.oangle_smul_add_right_eq_zero_or_eq_pi_iff r', not_or_distrib] at h },
  let s : set (V × V) := (λ r' : ℝ, (x, r' • x + y)) '' set.univ,
  have hc : is_connected s := is_connected_univ.image _ ((continuous_const.prod_mk
    ((continuous_id.smul continuous_const).add continuous_const)).continuous_on),
  have hf : continuous_on (λ z : V × V, o.oangle z.1 z.2) s,
  { refine continuous_at.continuous_on (λ z hz, o.continuous_at_oangle _ _),
    all_goals { simp_rw [s, set.mem_image] at hz,
                obtain ⟨r', -, rfl⟩ := hz,
                simp only [prod.fst, prod.snd],
                intro hz },
    { simpa [hz] using (h' 0).1 },
    { simpa [hz] using (h' r').1 } },
  have hs : ∀ z : V × V, z ∈ s → o.oangle z.1 z.2 ≠ 0 ∧ o.oangle z.1 z.2 ≠ π,
  { intros z hz,
    simp_rw [s, set.mem_image] at hz,
    obtain ⟨r', -, rfl⟩ := hz,
    exact h' r' },
  have hx : (x, y) ∈ s,
  { convert set.mem_image_of_mem (λ r' : ℝ, (x, r' • x + y)) (set.mem_univ 0),
    simp },
  have hy : (x, r • x + y) ∈ s := set.mem_image_of_mem _ (set.mem_univ _),
  convert real.angle.sign_eq_of_continuous_on hc hf hs hx hy
end

/-- Adding a multiple of the second vector passed to `oangle` to the first vector does not change
the sign of the angle. -/
@[simp] lemma oangle_sign_add_smul_left (x y : V) (r : ℝ) :
  (o.oangle (x + r • y) y).sign = (o.oangle x y).sign :=
by simp_rw [o.oangle_rev y, real.angle.sign_neg, add_comm x, oangle_sign_smul_add_right]

/-- Subtracting a multiple of the first vector passed to `oangle` from the second vector does
not change the sign of the angle. -/
@[simp] lemma oangle_sign_sub_smul_right (x y : V) (r : ℝ) :
  (o.oangle x (y - r • x)).sign = (o.oangle x y).sign :=
by rw [sub_eq_add_neg, ←neg_smul, add_comm, oangle_sign_smul_add_right]

/-- Subtracting a multiple of the second vector passed to `oangle` from the first vector does
not change the sign of the angle. -/
@[simp] lemma oangle_sign_sub_smul_left (x y : V) (r : ℝ) :
  (o.oangle (x - r • y) y).sign = (o.oangle x y).sign :=
by rw [sub_eq_add_neg, ←neg_smul, oangle_sign_add_smul_left]

/-- The sign of the angle between a vector, and a linear combination of that vector with a second
vector, is the sign of the factor by which the second vector is multiplied in that combination
multiplied by the sign of the angle between the two vectors. -/
@[simp] lemma oangle_sign_smul_add_smul_right (x y : V) (r₁ r₂ : ℝ) :
  (o.oangle x (r₁ • x + r₂ • y)).sign = sign r₂ * (o.oangle x y).sign :=
begin
  rw ←o.oangle_sign_smul_add_right x (r₁ • x + r₂ • y) (-r₁),
  simp
end

/-- The sign of the angle between a linear combination of two vectors and the second vector is
the sign of the factor by which the first vector is multiplied in that combination multiplied by
the sign of the angle between the two vectors. -/
@[simp] lemma oangle_sign_smul_add_smul_left (x y : V) (r₁ r₂ : ℝ) :
  (o.oangle (r₁ • x + r₂ • y) y).sign = sign r₁ * (o.oangle x y).sign :=
by simp_rw [o.oangle_rev y, real.angle.sign_neg, add_comm (r₁ • x),
            oangle_sign_smul_add_smul_right, mul_neg]

/-- The sign of the angle between two linear combinations of two vectors is the sign of the
determinant of the factors in those combinations multiplied by the sign of the angle between the
two vectors. -/
lemma oangle_sign_smul_add_smul_smul_add_smul (x y : V) (r₁ r₂ r₃ r₄ : ℝ) :
  (o.oangle (r₁ • x + r₂ • y) (r₃ • x + r₄ • y)).sign =
    sign (r₁ * r₄ - r₂ * r₃) * (o.oangle x y).sign :=
begin
  by_cases hr₁ : r₁ = 0,
  { rw [hr₁, zero_smul, zero_mul, zero_add, zero_sub, left.sign_neg, oangle_sign_smul_left,
        add_comm, oangle_sign_smul_add_smul_right, oangle_rev, real.angle.sign_neg, sign_mul,
        mul_neg, mul_neg, neg_mul, mul_assoc] },
  { rw [←o.oangle_sign_smul_add_right (r₁ • x + r₂ • y) (r₃ • x + r₄ • y) (-r₃ / r₁),
        smul_add, smul_smul, smul_smul, div_mul_cancel _ hr₁, neg_smul, ←add_assoc,
        add_comm (-(r₃ • x)), ←sub_eq_add_neg, sub_add_cancel, ←add_smul,
        oangle_sign_smul_right, oangle_sign_smul_add_smul_left, ←mul_assoc, ←sign_mul,
        add_mul, mul_assoc, mul_comm r₂ r₁, ←mul_assoc, div_mul_cancel _ hr₁, add_comm,
        neg_mul, ←sub_eq_add_neg, mul_comm r₄, mul_comm r₃] }
end

end orientation

namespace euclidean_geometry

open finite_dimensional

variables {V : Type*} {P : Type*} [inner_product_space ℝ V] [metric_space P]
variables [normed_add_torsor V P] [hd2 : fact (finrank ℝ V = 2)] [module.oriented ℝ V (fin 2)]
include hd2

local notation `o` := module.oriented.positive_orientation

/-- The oriented angle at `p₂` between the line segments to `p₁` and `p₃`, modulo `2 * π`. If
either of those points equals `p₂`, this is 0. See `euclidean_geometry.angle` for the
corresponding unoriented angle definition. -/
def oangle (p₁ p₂ p₃ : P) : real.angle := (o).oangle (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)

localized "notation (name := oangle) `∡` := euclidean_geometry.oangle" in euclidean_geometry

/-- Oriented angles are continuous when neither end point equals the middle point. -/
lemma continuous_at_oangle {x : P × P × P} (hx12 : x.1 ≠ x.2.1) (hx32 : x.2.2 ≠ x.2.1) :
  continuous_at (λ y : P × P × P, ∡ y.1 y.2.1 y.2.2) x :=
begin
  let f : P × P × P → V × V := λ y, (y.1 -ᵥ y.2.1, y.2.2 -ᵥ y.2.1),
  have hf1 : (f x).1 ≠ 0, by simp [hx12],
  have hf2 : (f x).2 ≠ 0, by simp [hx32],
  exact ((o).continuous_at_oangle hf1 hf2).comp
    ((continuous_fst.vsub continuous_snd.fst).prod_mk
      (continuous_snd.snd.vsub continuous_snd.fst)).continuous_at
end

/-- The angle ∡AAB at a point. -/
@[simp] lemma oangle_self_left (p₁ p₂ : P) : ∡ p₁ p₁ p₂ = 0 :=
by simp [oangle]

/-- The angle ∡ABB at a point. -/
@[simp] lemma oangle_self_right (p₁ p₂ : P) : ∡ p₁ p₂ p₂ = 0 :=
by simp [oangle]

/-- The angle ∡ABA at a point. -/
@[simp] lemma oangle_self_left_right (p₁ p₂ : P) : ∡ p₁ p₂ p₁ = 0 :=
(o).oangle_self _

/-- Reversing the order of the points passed to `oangle` negates the angle. -/
lemma oangle_rev (p₁ p₂ p₃ : P) : ∡ p₃ p₂ p₁ = -∡ p₁ p₂ p₃ :=
(o).oangle_rev _ _

/-- Adding an angle to that with the order of the points reversed results in 0. -/
@[simp] lemma oangle_add_oangle_rev (p₁ p₂ p₃ : P) : ∡ p₁ p₂ p₃ + ∡ p₃ p₂ p₁ = 0 :=
(o).oangle_add_oangle_rev _ _

/-- An oriented angle is zero if and only if the angle with the order of the points reversed is
zero. -/
lemma oangle_eq_zero_iff_oangle_rev_eq_zero {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = 0 ↔ ∡ p₃ p₂ p₁ = 0 :=
(o).oangle_eq_zero_iff_oangle_rev_eq_zero

/-- An oriented angle is `π` if and only if the angle with the order of the points reversed is
`π`. -/
lemma oangle_eq_pi_iff_oangle_rev_eq_pi {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ ∡ p₃ p₂ p₁ = π :=
(o).oangle_eq_pi_iff_oangle_rev_eq_pi

/-- An oriented angle is not zero or `π` if and only if the three points are affinely
independent. -/
lemma oangle_ne_zero_and_ne_pi_iff_affine_independent {p₁ p₂ p₃ : P} :
  (∡ p₁ p₂ p₃ ≠ 0 ∧ ∡ p₁ p₂ p₃ ≠ π) ↔ affine_independent ℝ ![p₁, p₂, p₃] :=
begin
  rw [oangle, (o).oangle_ne_zero_and_ne_pi_iff_linear_independent,
      affine_independent_iff_linear_independent_vsub ℝ _ (1 : fin 3),
      ←linear_independent_equiv (fin_succ_above_equiv (1 : fin 3)).to_equiv],
  convert iff.rfl,
  ext i,
  fin_cases i;
    refl
end

/-- An oriented angle is zero or `π` if and only if the three points are collinear. -/
lemma oangle_eq_zero_or_eq_pi_iff_collinear {p₁ p₂ p₃ : P} :
  (∡ p₁ p₂ p₃ = 0 ∨ ∡ p₁ p₂ p₃ = π) ↔ collinear ℝ ({p₁, p₂, p₃} : set P) :=
begin
  rw [←not_iff_not, not_or_distrib, oangle_ne_zero_and_ne_pi_iff_affine_independent,
      affine_independent_iff_not_collinear],
  simp [-set.union_singleton]
end

/-- Given three points not equal to `p`, the angle between the first and the second at `p` plus
the angle between the second and the third equals the angle between the first and the third. -/
@[simp] lemma oangle_add {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
  ∡ p₁ p p₂ + ∡ p₂ p p₃ = ∡ p₁ p p₃ :=
(o).oangle_add (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

/-- Given three points not equal to `p`, the angle between the second and the third at `p` plus
the angle between the first and the second equals the angle between the first and the third. -/
@[simp] lemma oangle_add_swap {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
  ∡ p₂ p p₃ + ∡ p₁ p p₂ = ∡ p₁ p p₃ :=
(o).oangle_add_swap (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

/-- Given three points not equal to `p`, the angle between the first and the third at `p` minus
the angle between the first and the second equals the angle between the second and the third. -/
@[simp] lemma oangle_sub_left {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
  ∡ p₁ p p₃ - ∡ p₁ p p₂ = ∡ p₂ p p₃ :=
(o).oangle_sub_left (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

/-- Given three points not equal to `p`, the angle between the first and the third at `p` minus
the angle between the second and the third equals the angle between the first and the second. -/
@[simp] lemma oangle_sub_right {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
  ∡ p₁ p p₃ - ∡ p₂ p p₃ = ∡ p₁ p p₂ :=
(o).oangle_sub_right (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

/-- Given three points not equal to `p`, adding the angles between them at `p` in cyclic order
results in 0. -/
@[simp] lemma oangle_add_cyc3 {p p₁ p₂ p₃ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) (hp₃ : p₃ ≠ p) :
  ∡ p₁ p p₂ + ∡ p₂ p p₃ + ∡ p₃ p p₁ = 0 :=
(o).oangle_add_cyc3 (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂) (vsub_ne_zero.2 hp₃)

/-- Pons asinorum, oriented angle-at-point form. -/
lemma oangle_eq_oangle_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃) :
  ∡ p₁ p₂ p₃ = ∡ p₂ p₃ p₁ :=
begin
  simp_rw dist_eq_norm_vsub at h,
  rw [oangle, oangle, ←vsub_sub_vsub_cancel_left p₃ p₂ p₁, ←vsub_sub_vsub_cancel_left p₂ p₃ p₁,
      (o).oangle_sub_eq_oangle_sub_rev_of_norm_eq h]
end

/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
angle-at-point form. -/
lemma oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq {p₁ p₂ p₃ : P} (hn : p₂ ≠ p₃)
  (h : dist p₁ p₂ = dist p₁ p₃) : ∡ p₃ p₁ p₂ = π - (2 : ℤ) • ∡ p₁ p₂ p₃ :=
begin
  simp_rw dist_eq_norm_vsub at h,
  rw [oangle, oangle],
  convert (o).oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq _ h using 1,
  { rw [←neg_vsub_eq_vsub_rev p₁ p₃, ←neg_vsub_eq_vsub_rev p₁ p₂, (o).oangle_neg_neg] },
  { rw [←(o).oangle_sub_eq_oangle_sub_rev_of_norm_eq h], simp },
  { simpa using hn }
end

/-- The cosine of the oriented angle at `p` between two points not equal to `p` equals that of the
unoriented angle. -/
lemma cos_oangle_eq_cos_angle {p p₁ p₂ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) :
  real.angle.cos (∡ p₁ p p₂) = real.cos (∠ p₁ p p₂) :=
(o).cos_oangle_eq_cos_angle (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

/-- The oriented angle at `p` between two points not equal to `p` is plus or minus the unoriented
angle. -/
lemma oangle_eq_angle_or_eq_neg_angle {p p₁ p₂ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) :
  ∡ p₁ p p₂ = ∠ p₁ p p₂ ∨ ∡ p₁ p p₂ = -∠ p₁ p p₂ :=
(o).oangle_eq_angle_or_eq_neg_angle (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

/-- The unoriented angle at `p` between two points not equal to `p` is the absolute value of the
oriented angle. -/
lemma angle_eq_abs_oangle_to_real {p p₁ p₂ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) :
  ∠ p₁ p p₂ = |(∡ p₁ p p₂).to_real| :=
(o).angle_eq_abs_oangle_to_real (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

/-- If the sign of the oriented angle at `p` between two points is zero, either one of the points
equals `p` or the unoriented angle is 0 or π. -/
lemma eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero {p p₁ p₂ : P}
  (h : (∡ p₁ p p₂).sign = 0) : p₁ = p ∨ p₂ = p ∨ ∠ p₁ p p₂ = 0 ∨ ∠ p₁ p p₂ = π :=
begin
  convert (o).eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero h;
    simp
end

/-- If two unoriented angles are equal, and the signs of the corresponding oriented angles are
equal, then the oriented angles are equal (even in degenerate cases). -/
lemma oangle_eq_of_angle_eq_of_sign_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆)
  (hs : (∡ p₁ p₂ p₃).sign = (∡ p₄ p₅ p₆).sign) : ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆ :=
(o).oangle_eq_of_angle_eq_of_sign_eq h hs

/-- If the signs of two nondegenerate oriented angles between points are equal, the oriented
angles are equal if and only if the unoriented angles are equal. -/
lemma angle_eq_iff_oangle_eq_of_sign_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P} (hp₁ : p₁ ≠ p₂) (hp₃ : p₃ ≠ p₂)
  (hp₄ : p₄ ≠ p₅) (hp₆ : p₆ ≠ p₅) (hs : (∡ p₁ p₂ p₃).sign = (∡ p₄ p₅ p₆).sign) :
  ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆ ↔ ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆ :=
(o).angle_eq_iff_oangle_eq_of_sign_eq (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₃)
                                      (vsub_ne_zero.2 hp₄) (vsub_ne_zero.2 hp₆) hs

/-- The unoriented angle at `p` between two points not equal to `p` is zero if and only if the
unoriented angle is zero. -/
lemma oangle_eq_zero_iff_angle_eq_zero {p p₁ p₂ : P} (hp₁ : p₁ ≠ p) (hp₂ : p₂ ≠ p) :
  ∡ p₁ p p₂ = 0 ↔ ∠ p₁ p p₂ = 0 :=
(o).oangle_eq_zero_iff_angle_eq_zero (vsub_ne_zero.2 hp₁) (vsub_ne_zero.2 hp₂)

/-- The oriented angle between three points is `π` if and only if the unoriented angle is `π`. -/
lemma oangle_eq_pi_iff_angle_eq_pi {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ ∠ p₁ p₂ p₃ = π :=
(o).oangle_eq_pi_iff_angle_eq_pi

/-- Swapping the first and second points in an oriented angle negates the sign of that angle. -/
lemma oangle_swap₁₂_sign (p₁ p₂ p₃ : P) : -(∡ p₁ p₂ p₃).sign = (∡ p₂ p₁ p₃).sign :=
begin
  rw [eq_comm, oangle, oangle, ←(o).oangle_neg_neg, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev,
      ←vsub_sub_vsub_cancel_left p₁ p₃ p₂, ←neg_vsub_eq_vsub_rev p₃ p₂, sub_eq_add_neg,
      neg_vsub_eq_vsub_rev p₂ p₁, add_comm, ←@neg_one_smul ℝ],
  nth_rewrite 1 [←one_smul ℝ (p₁ -ᵥ p₂)],
  rw (o).oangle_sign_smul_add_smul_right,
  simp
end

/-- Swapping the first and third points in an oriented angle negates the sign of that angle. -/
lemma oangle_swap₁₃_sign (p₁ p₂ p₃ : P) : -(∡ p₁ p₂ p₃).sign = (∡ p₃ p₂ p₁).sign :=
by rw [oangle_rev, real.angle.sign_neg, neg_neg]

/-- Swapping the second and third points in an oriented angle negates the sign of that angle. -/
lemma oangle_swap₂₃_sign (p₁ p₂ p₃ : P) : -(∡ p₁ p₂ p₃).sign = (∡ p₁ p₃ p₂).sign :=
by rw [oangle_swap₁₃_sign, ←oangle_swap₁₂_sign, oangle_swap₁₃_sign]

/-- Rotating the points in an oriented angle does not change the sign of that angle. -/
lemma oangle_rotate_sign (p₁ p₂ p₃ : P) : (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign :=
by rw [←oangle_swap₁₂_sign, oangle_swap₁₃_sign]

/-- The oriented angle between three points is π if and only if the second point is strictly
between the other two. -/
lemma oangle_eq_pi_iff_sbtw {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ sbtw ℝ p₁ p₂ p₃ :=
by rw [oangle_eq_pi_iff_angle_eq_pi, angle_eq_pi_iff_sbtw]

/-- If the second of three points is strictly between the other two, the oriented angle at that
point is π. -/
lemma _root_.sbtw.oangle₁₂₃_eq_pi {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∡ p₁ p₂ p₃ = π :=
oangle_eq_pi_iff_sbtw.2 h

/-- If the second of three points is strictly between the other two, the oriented angle at that
point (reversed) is π. -/
lemma _root_.sbtw.oangle₃₂₁_eq_pi {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∡ p₃ p₂ p₁ = π :=
by rw [oangle_eq_pi_iff_oangle_rev_eq_pi, ←h.oangle₁₂₃_eq_pi]

/-- If the second of three points is weakly between the other two, the oriented angle at the
first point is zero. -/
lemma _root_.wbtw.oangle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : wbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₁ p₃ = 0 :=
begin
  by_cases hp₂p₁ : p₂ = p₁, { simp [hp₂p₁] },
  by_cases hp₃p₁ : p₃ = p₁, { simp [hp₃p₁] },
  rw oangle_eq_zero_iff_angle_eq_zero hp₂p₁ hp₃p₁,
  exact h.angle₂₁₃_eq_zero_of_ne hp₂p₁
end

/-- If the second of three points is strictly between the other two, the oriented angle at the
first point is zero. -/
lemma _root_.sbtw.oangle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₁ p₃ = 0 :=
h.wbtw.oangle₂₁₃_eq_zero

/-- If the second of three points is weakly between the other two, the oriented angle at the
first point (reversed) is zero. -/
lemma _root_.wbtw.oangle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : wbtw ℝ p₁ p₂ p₃) : ∡ p₃ p₁ p₂ = 0 :=
by rw [oangle_eq_zero_iff_oangle_rev_eq_zero, h.oangle₂₁₃_eq_zero]

/-- If the second of three points is strictly between the other two, the oriented angle at the
first point (reversed) is zero. -/
lemma _root_.sbtw.oangle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∡ p₃ p₁ p₂ = 0 :=
h.wbtw.oangle₃₁₂_eq_zero

/-- If the second of three points is weakly between the other two, the oriented angle at the
third point is zero. -/
lemma _root_.wbtw.oangle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : wbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₃ p₁ = 0 :=
h.symm.oangle₂₁₃_eq_zero

/-- If the second of three points is strictly between the other two, the oriented angle at the
third point is zero. -/
lemma _root_.sbtw.oangle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₃ p₁ = 0 :=
h.wbtw.oangle₂₃₁_eq_zero

/-- If the second of three points is weakly between the other two, the oriented angle at the
third point (reversed) is zero. -/
lemma _root_.wbtw.oangle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : wbtw ℝ p₁ p₂ p₃) : ∡ p₁ p₃ p₂ = 0 :=
h.symm.oangle₃₁₂_eq_zero

/-- If the second of three points is strictly between the other two, the oriented angle at the
third point (reversed) is zero. -/
lemma _root_.sbtw.oangle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∡ p₁ p₃ p₂ = 0 :=
h.wbtw.oangle₁₃₂_eq_zero

/-- The oriented angle between three points is zero if and only if one of the first and third
points is weakly between the other two. -/
lemma oangle_eq_zero_iff_wbtw {p₁ p₂ p₃ : P} :
  ∡ p₁ p₂ p₃ = 0 ↔ wbtw ℝ p₂ p₁ p₃ ∨ wbtw ℝ p₂ p₃ p₁ :=
begin
  by_cases hp₁p₂ : p₁ = p₂, { simp [hp₁p₂] },
  by_cases hp₃p₂ : p₃ = p₂, { simp [hp₃p₂] },
  rw [oangle_eq_zero_iff_angle_eq_zero hp₁p₂ hp₃p₂, angle_eq_zero_iff_ne_and_wbtw],
  simp [hp₁p₂, hp₃p₂]
end

/-- An oriented angle is unchanged by replacing the first point by one weakly further away on the
same ray. -/
lemma _root_.wbtw.oangle_eq_left {p₁ p₁' p₂ p₃ : P} (h : wbtw ℝ p₂ p₁ p₁') (hp₁p₂ : p₁ ≠ p₂) :
  ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃ :=
begin
  by_cases hp₃p₂ : p₃ = p₂, { simp [hp₃p₂] },
  by_cases hp₁'p₂ : p₁' = p₂, { rw [hp₁'p₂, wbtw_self_iff] at h, exact false.elim (hp₁p₂ h) },
  rw [←oangle_add hp₁'p₂ hp₁p₂ hp₃p₂, h.oangle₃₁₂_eq_zero, zero_add]
end

/-- An oriented angle is unchanged by replacing the first point by one strictly further away on
the same ray. -/
lemma _root_.sbtw.oangle_eq_left {p₁ p₁' p₂ p₃ : P} (h : sbtw ℝ p₂ p₁ p₁') :
  ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃ :=
h.wbtw.oangle_eq_left h.ne_left

/-- An oriented angle is unchanged by replacing the third point by one weakly further away on the
same ray. -/
lemma _root_.wbtw.oangle_eq_right {p₁ p₂ p₃ p₃' : P} (h : wbtw ℝ p₂ p₃ p₃') (hp₃p₂ : p₃ ≠ p₂) :
  ∡ p₁ p₂ p₃ = ∡ p₁ p₂ p₃' :=
by rw [oangle_rev, h.oangle_eq_left hp₃p₂, ←oangle_rev]

/-- An oriented angle is unchanged by replacing the third point by one strictly further away on
the same ray. -/
lemma _root_.sbtw.oangle_eq_right {p₁ p₂ p₃ p₃' : P} (h : sbtw ℝ p₂ p₃ p₃') :
  ∡ p₁ p₂ p₃ = ∡ p₁ p₂ p₃' :=
h.wbtw.oangle_eq_right h.ne_left

/-- Replacing the first point by one on the same line but the opposite ray adds π to the oriented
angle. -/
lemma _root_.sbtw.oangle_eq_add_pi_left {p₁ p₁' p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₁')
  (hp₃p₂ : p₃ ≠ p₂) : ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃ + π :=
by rw [←h.oangle₁₂₃_eq_pi, oangle_add_swap h.left_ne h.right_ne hp₃p₂]

/-- Replacing the third point by one on the same line but the opposite ray adds π to the oriented
angle. -/
lemma _root_.sbtw.oangle_eq_add_pi_right {p₁ p₂ p₃ p₃' : P} (h : sbtw ℝ p₃ p₂ p₃')
  (hp₁p₂ : p₁ ≠ p₂) : ∡ p₁ p₂ p₃ = ∡ p₁ p₂ p₃' + π :=
by rw [←h.oangle₃₂₁_eq_pi, oangle_add hp₁p₂ h.right_ne h.left_ne]

/-- Replacing both the first and third points by ones on the same lines but the opposite rays
does not change the oriented angle (vertically opposite angles). -/
lemma _root_.sbtw.oangle_eq_left_right {p₁ p₁' p₂ p₃ p₃' : P} (h₁ : sbtw ℝ p₁ p₂ p₁')
  (h₃ : sbtw ℝ p₃ p₂ p₃') : ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃' :=
by rw [h₁.oangle_eq_add_pi_left h₃.left_ne, h₃.oangle_eq_add_pi_right h₁.right_ne, add_assoc,
       real.angle.coe_pi_add_coe_pi, add_zero]

/-- Replacing the first point by one on the same line does not change twice the oriented angle. -/
lemma _root_.collinear.two_zsmul_oangle_eq_left {p₁ p₁' p₂ p₃ : P}
  (h : collinear ℝ ({p₁, p₂, p₁'} : set P)) (hp₁p₂ : p₁ ≠ p₂) (hp₁'p₂ : p₁' ≠ p₂) :
  (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₁' p₂ p₃ :=
begin
  by_cases hp₃p₂ : p₃ = p₂, { simp [hp₃p₂] },
  rcases h.wbtw_or_wbtw_or_wbtw with hw | hw | hw,
  { have hw' : sbtw ℝ p₁ p₂ p₁' := ⟨hw, hp₁p₂.symm, hp₁'p₂.symm⟩,
    rw [hw'.oangle_eq_add_pi_left hp₃p₂, smul_add, real.angle.two_zsmul_coe_pi, add_zero] },
  { rw hw.oangle_eq_left hp₁'p₂ },
  { rw hw.symm.oangle_eq_left hp₁p₂ }
end

/-- Replacing the third point by one on the same line does not change twice the oriented angle. -/
lemma _root_.collinear.two_zsmul_oangle_eq_right {p₁ p₂ p₃ p₃' : P}
  (h : collinear ℝ ({p₃, p₂, p₃'} : set P)) (hp₃p₂ : p₃ ≠ p₂) (hp₃'p₂ : p₃' ≠ p₂) :
  (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₁ p₂ p₃' :=
by rw [oangle_rev, smul_neg, h.two_zsmul_oangle_eq_left hp₃p₂ hp₃'p₂, ←smul_neg, ←oangle_rev]

open affine_subspace

/-- Given two pairs of distinct points on the same line, such that the vectors between those
pairs of points are on the same ray (oriented in the same direction on that line), and a fifth
point, the angles at the fifth point between each of those two pairs of points have the same
sign. -/
lemma _root_.collinear.oangle_sign_of_same_ray_vsub {p₁ p₂ p₃ p₄ : P} (p₅ : P) (hp₁p₂ : p₁ ≠ p₂)
  (hp₃p₄ : p₃ ≠ p₄) (hc : collinear ℝ ({p₁, p₂, p₃, p₄} : set P))
  (hr : same_ray ℝ (p₂ -ᵥ p₁) (p₄ -ᵥ p₃)) : (∡ p₁ p₅ p₂).sign = (∡ p₃ p₅ p₄).sign :=
begin
  by_cases hc₅₁₂ : collinear ℝ ({p₅, p₁, p₂} : set P),
  { have hc₅₁₂₃₄ : collinear ℝ ({p₅, p₁, p₂, p₃, p₄} : set P) :=
      (hc.collinear_insert_iff_of_ne (set.mem_insert _ _)
                                     (set.mem_insert_of_mem _ (set.mem_insert _ _)) hp₁p₂).2 hc₅₁₂,
    have hc₅₃₄ : collinear ℝ ({p₅, p₃, p₄} : set P) :=
      (hc.collinear_insert_iff_of_ne
        (set.mem_insert_of_mem _ (set.mem_insert_of_mem _ (set.mem_insert _ _)))
        (set.mem_insert_of_mem _ (set.mem_insert_of_mem _ (set.mem_insert_of_mem _
          (set.mem_singleton _)))) hp₃p₄).1 hc₅₁₂₃₄,
    rw set.insert_comm at hc₅₁₂ hc₅₃₄,
    have hs₁₅₂ := oangle_eq_zero_or_eq_pi_iff_collinear.2 hc₅₁₂,
    have hs₃₅₄ := oangle_eq_zero_or_eq_pi_iff_collinear.2 hc₅₃₄,
    rw ←real.angle.sign_eq_zero_iff at hs₁₅₂ hs₃₅₄,
    rw [hs₁₅₂, hs₃₅₄] },
  { let s : set (P × P × P) :=
      (λ x : affine_span ℝ ({p₁, p₂} : set P) × V, (x.1, p₅, x.2 +ᵥ x.1)) ''
        set.univ ×ˢ {v | same_ray ℝ (p₂ -ᵥ p₁) v ∧ v ≠ 0},
    have hco : is_connected s,
    { haveI : connected_space (affine_span ℝ ({p₁, p₂} : set P)) := add_torsor.connected_space _ _,
      exact (is_connected_univ.prod (is_connected_set_of_same_ray_and_ne_zero
        (vsub_ne_zero.2 hp₁p₂.symm))).image _
          ((continuous_fst.subtype_coe.prod_mk
            (continuous_const.prod_mk
              (continuous_snd.vadd continuous_fst.subtype_coe))).continuous_on) },
    have hf : continuous_on (λ p : P × P × P, ∡ p.1 p.2.1 p.2.2) s,
    { refine continuous_at.continuous_on (λ p hp, continuous_at_oangle _ _),
      all_goals { simp_rw [s, set.mem_image, set.mem_prod, set.mem_univ, true_and,
                           prod.ext_iff] at hp,
                  obtain ⟨q₁, q₅, q₂⟩ := p,
                  dsimp only at ⊢ hp,
                  obtain ⟨⟨⟨q, hq⟩, v⟩, hv, rfl, rfl, rfl⟩ := hp,
                  dsimp only [subtype.coe_mk, set.mem_set_of] at ⊢ hv,
                  obtain ⟨hvr, -⟩ := hv,
                  rintro rfl,
                  refine hc₅₁₂ ((collinear_insert_iff_of_mem_affine_span _).2
                                  (collinear_pair _ _ _)) },
      { exact hq },
      { refine vadd_mem_of_mem_direction _ hq,
        rw ←exists_nonneg_left_iff_same_ray (vsub_ne_zero.2 hp₁p₂.symm) at hvr,
        obtain ⟨r, -, rfl⟩ := hvr,
        rw direction_affine_span,
        exact smul_vsub_rev_mem_vector_span_pair _ _ _ } },
    have hsp : ∀ p : P × P × P, p ∈ s → ∡ p.1 p.2.1 p.2.2 ≠ 0 ∧ ∡ p.1 p.2.1 p.2.2 ≠ π,
    { intros p hp,
      simp_rw [s, set.mem_image, set.mem_prod, set.mem_set_of, set.mem_univ, true_and,
               prod.ext_iff] at hp,
      obtain ⟨q₁, q₅, q₂⟩ := p,
      dsimp only at ⊢ hp,
      obtain ⟨⟨⟨q, hq⟩, v⟩, hv, rfl, rfl, rfl⟩ := hp,
      dsimp only [subtype.coe_mk, set.mem_set_of] at ⊢ hv,
      obtain ⟨hvr, hv0⟩ := hv,
      rw ←exists_nonneg_left_iff_same_ray (vsub_ne_zero.2 hp₁p₂.symm) at hvr,
      obtain ⟨r, -, rfl⟩ := hvr,
      change q ∈ affine_span ℝ ({p₁, p₂} : set P) at hq,
      rw [oangle_ne_zero_and_ne_pi_iff_affine_independent],
      refine affine_independent_of_ne_of_mem_of_not_mem_of_mem _ hq
        (λ h, hc₅₁₂ ((collinear_insert_iff_of_mem_affine_span h).2 (collinear_pair _ _ _))) _,
      { rwa [←@vsub_ne_zero V, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, neg_ne_zero] },
      { refine vadd_mem_of_mem_direction _ hq,
        rw direction_affine_span,
        exact smul_vsub_rev_mem_vector_span_pair _ _ _ } },
    have hp₁p₂s : (p₁, p₅, p₂) ∈ s,
    { simp_rw [s, set.mem_image, set.mem_prod, set.mem_set_of, set.mem_univ, true_and,
               prod.ext_iff],
      refine ⟨⟨⟨p₁, left_mem_affine_span_pair _ _ _⟩, p₂ -ᵥ p₁⟩,
              ⟨same_ray.rfl, vsub_ne_zero.2 hp₁p₂.symm⟩, _⟩,
      simp },
    have hp₃p₄s : (p₃, p₅, p₄) ∈ s,
    { simp_rw [s, set.mem_image, set.mem_prod, set.mem_set_of, set.mem_univ, true_and,
               prod.ext_iff],
      refine ⟨⟨⟨p₃,
                hc.mem_affine_span_of_mem_of_ne
                  (set.mem_insert _ _)
                  (set.mem_insert_of_mem _ (set.mem_insert _ _))
                  (set.mem_insert_of_mem _ (set.mem_insert_of_mem _ (set.mem_insert _ _)))
                  hp₁p₂⟩, p₄ -ᵥ p₃⟩, ⟨hr, vsub_ne_zero.2 hp₃p₄.symm⟩, _⟩,
      simp },
    convert real.angle.sign_eq_of_continuous_on hco hf hsp hp₃p₄s hp₁p₂s }
end

/-- Given three points in strict order on the same line, and a fourth point, the angles at the
fourth point between the first and second or second and third points have the same sign. -/
lemma _root_.sbtw.oangle_sign_eq {p₁ p₂ p₃ : P} (p₄ : P) (h : sbtw ℝ p₁ p₂ p₃) :
  (∡ p₁ p₄ p₂).sign = (∡ p₂ p₄ p₃).sign :=
begin
  have hc : collinear ℝ ({p₁, p₂, p₂, p₃} : set P), { simpa using h.wbtw.collinear },
  exact hc.oangle_sign_of_same_ray_vsub _ h.left_ne h.ne_right h.wbtw.same_ray_vsub
end

/-- Given three points in weak order on the same line, with the first not equal to the second,
and a fourth point, the angles at the fourth point between the first and second or first and
third points have the same sign. -/
lemma _root_.wbtw.oangle_sign_eq_of_ne_left {p₁ p₂ p₃ : P} (p₄ : P) (h : wbtw ℝ p₁ p₂ p₃)
  (hne : p₁ ≠ p₂) : (∡ p₁ p₄ p₂).sign = (∡ p₁ p₄ p₃).sign :=
begin
  have hc : collinear ℝ ({p₁, p₂, p₁, p₃} : set P),
  { simpa [set.insert_comm p₂] using h.collinear },
  exact hc.oangle_sign_of_same_ray_vsub _ hne (h.left_ne_right_of_ne_left hne.symm)
    h.same_ray_vsub_left
end

/-- Given three points in strict order on the same line, and a fourth point, the angles at the
fourth point between the first and second or first and third points have the same sign. -/
lemma _root_.sbtw.oangle_sign_eq_left {p₁ p₂ p₃ : P} (p₄ : P) (h : sbtw ℝ p₁ p₂ p₃) :
  (∡ p₁ p₄ p₂).sign = (∡ p₁ p₄ p₃).sign :=
h.wbtw.oangle_sign_eq_of_ne_left _ h.left_ne

/-- Given three points in weak order on the same line, with the second not equal to the third,
and a fourth point, the angles at the fourth point between the second and third or first and
third points have the same sign. -/
lemma _root_.wbtw.oangle_sign_eq_of_ne_right {p₁ p₂ p₃ : P} (p₄ : P) (h : wbtw ℝ p₁ p₂ p₃)
  (hne : p₂ ≠ p₃) : (∡ p₂ p₄ p₃).sign = (∡ p₁ p₄ p₃).sign :=
by simp_rw [oangle_rev p₃, real.angle.sign_neg, h.symm.oangle_sign_eq_of_ne_left _ hne.symm]

/-- Given three points in strict order on the same line, and a fourth point, the angles at the
fourth point between the second and third or first and third points have the same sign. -/
lemma _root_.sbtw.oangle_sign_eq_right {p₁ p₂ p₃ : P} (p₄ : P) (h : sbtw ℝ p₁ p₂ p₃) :
  (∡ p₂ p₄ p₃).sign = (∡ p₁ p₄ p₃).sign :=
h.wbtw.oangle_sign_eq_of_ne_right _ h.ne_right

end euclidean_geometry
