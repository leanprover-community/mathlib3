/-
Copyright (c) 2019 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
import analysis.special_functions.trigonometric.basic
import analysis.normed.group.add_circle
import algebra.char_zero.quotient
import algebra.order.to_interval_mod
import topology.instances.sign

/-!
# The type of angles

In this file we define `real.angle` to be the quotient group `ℝ/2πℤ` and prove a few simple lemmas
about trigonometric functions and angles.
-/

open_locale real

noncomputable theory

namespace real

/-- The type of angles -/
@[derive [normed_add_comm_group, inhabited, has_coe_t ℝ]]
def angle : Type := add_circle (2 * π)

namespace angle

@[continuity] lemma continuous_coe : continuous (coe : ℝ → angle) :=
continuous_quotient_mk

/-- Coercion `ℝ → angle` as an additive homomorphism. -/
def coe_hom : ℝ →+ angle := quotient_add_group.mk' _

@[simp] lemma coe_coe_hom : (coe_hom : ℝ → angle) = coe := rfl

/-- An induction principle to deduce results for `angle` from those for `ℝ`, used with
`induction θ using real.angle.induction_on`. -/
@[elab_as_eliminator]
protected lemma induction_on {p : angle → Prop} (θ : angle) (h : ∀ x : ℝ, p x) : p θ :=
quotient.induction_on' θ h

@[simp] lemma coe_zero : ↑(0 : ℝ) = (0 : angle) := rfl
@[simp] lemma coe_add (x y : ℝ) : ↑(x + y : ℝ) = (↑x + ↑y : angle) := rfl
@[simp] lemma coe_neg (x : ℝ) : ↑(-x : ℝ) = -(↑x : angle) := rfl
@[simp] lemma coe_sub (x y : ℝ) : ↑(x - y : ℝ) = (↑x - ↑y : angle) := rfl
lemma coe_nsmul (n : ℕ) (x : ℝ) : ↑(n • x : ℝ) = (n • ↑x : angle) := rfl
lemma coe_zsmul (z : ℤ) (x : ℝ) : ↑(z • x : ℝ) = (z • ↑x : angle) := rfl

@[simp, norm_cast] lemma coe_nat_mul_eq_nsmul (x : ℝ) (n : ℕ) :
  ↑((n : ℝ) * x) = n • (↑x : angle) :=
by simpa only [nsmul_eq_mul] using coe_hom.map_nsmul x n

@[simp, norm_cast] lemma coe_int_mul_eq_zsmul (x : ℝ) (n : ℤ) :
  ↑((n : ℝ) * x : ℝ) = n • (↑x : angle) :=
by simpa only [zsmul_eq_mul] using coe_hom.map_zsmul x n

lemma angle_eq_iff_two_pi_dvd_sub {ψ θ : ℝ} : (θ : angle) = ψ ↔ ∃ k : ℤ, θ - ψ = 2 * π * k :=
by simp only [quotient_add_group.eq, add_subgroup.zmultiples_eq_closure,
  add_subgroup.mem_closure_singleton, zsmul_eq_mul', (sub_eq_neg_add _ _).symm, eq_comm]

@[simp] lemma coe_two_pi : ↑(2 * π : ℝ) = (0 : angle) :=
angle_eq_iff_two_pi_dvd_sub.2 ⟨1, by rw [sub_zero, int.cast_one, mul_one]⟩

@[simp] lemma neg_coe_pi : -(π : angle) = π :=
begin
  rw [←coe_neg, angle_eq_iff_two_pi_dvd_sub],
  use -1,
  simp [two_mul, sub_eq_add_neg]
end

@[simp] lemma two_nsmul_coe_div_two (θ : ℝ) : (2 : ℕ) • (↑(θ / 2) : angle) = θ :=
by rw [←coe_nsmul, two_nsmul, add_halves]

@[simp] lemma two_zsmul_coe_div_two (θ : ℝ) : (2 : ℤ) • (↑(θ / 2) : angle) = θ :=
by rw [←coe_zsmul, two_zsmul, add_halves]

@[simp] lemma two_nsmul_neg_pi_div_two : (2 : ℕ) • (↑(-π / 2) : angle) = π :=
by rw [two_nsmul_coe_div_two, coe_neg, neg_coe_pi]

@[simp] lemma two_zsmul_neg_pi_div_two : (2 : ℤ) • (↑(-π / 2) : angle) = π :=
by rw [two_zsmul, ←two_nsmul, two_nsmul_neg_pi_div_two]

lemma sub_coe_pi_eq_add_coe_pi (θ : angle) : θ - π = θ + π :=
by rw [sub_eq_add_neg, neg_coe_pi]

@[simp] lemma two_nsmul_coe_pi : (2 : ℕ) • (π : angle) = 0 :=
by simp [←coe_nat_mul_eq_nsmul]

@[simp] lemma two_zsmul_coe_pi : (2 : ℤ) • (π : angle) = 0 :=
by simp [←coe_int_mul_eq_zsmul]

@[simp] lemma coe_pi_add_coe_pi : (π : real.angle) + π = 0 :=
by rw [←two_nsmul, two_nsmul_coe_pi]

lemma zsmul_eq_iff {ψ θ : angle} {z : ℤ} (hz : z ≠ 0) :
  z • ψ = z • θ ↔ (∃ k : fin z.nat_abs, ψ = θ + (k : ℕ) • (2 * π / z : ℝ)) :=
quotient_add_group.zmultiples_zsmul_eq_zsmul_iff hz

lemma nsmul_eq_iff {ψ θ : angle} {n : ℕ} (hz : n ≠ 0) :
  n • ψ = n • θ ↔ (∃ k : fin n, ψ = θ + (k : ℕ) • (2 * π / n : ℝ)) :=
quotient_add_group.zmultiples_nsmul_eq_nsmul_iff hz

lemma two_zsmul_eq_iff {ψ θ : angle} : (2 : ℤ) • ψ = (2 : ℤ) • θ ↔ (ψ = θ ∨ ψ = θ + π) :=
by rw [zsmul_eq_iff two_ne_zero, int.nat_abs_bit0, int.nat_abs_one,
    fin.exists_fin_two, fin.coe_zero, fin.coe_one, zero_smul, add_zero, one_smul,
    int.cast_two, mul_div_cancel_left (_ : ℝ) two_ne_zero]

lemma two_nsmul_eq_iff {ψ θ : angle} : (2 : ℕ) • ψ = (2 : ℕ) • θ ↔ (ψ = θ ∨ ψ = θ + π) :=
by simp_rw [←coe_nat_zsmul, int.coe_nat_bit0, int.coe_nat_one, two_zsmul_eq_iff]

lemma two_nsmul_eq_zero_iff {θ : angle} : (2 : ℕ) • θ = 0 ↔ (θ = 0 ∨ θ = π) :=
by convert two_nsmul_eq_iff; simp

lemma two_nsmul_ne_zero_iff {θ : angle} : (2 : ℕ) • θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π :=
by rw [←not_or_distrib, ←two_nsmul_eq_zero_iff]

lemma two_zsmul_eq_zero_iff {θ : angle} : (2 : ℤ) • θ = 0 ↔ (θ = 0 ∨ θ = π) :=
by simp_rw [two_zsmul, ←two_nsmul, two_nsmul_eq_zero_iff]

lemma two_zsmul_ne_zero_iff {θ : angle} : (2 : ℤ) • θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π :=
by rw [←not_or_distrib, ←two_zsmul_eq_zero_iff]

lemma eq_neg_self_iff {θ : angle} : θ = -θ ↔ θ = 0 ∨ θ = π :=
by rw [←add_eq_zero_iff_eq_neg, ←two_nsmul, two_nsmul_eq_zero_iff]

lemma ne_neg_self_iff {θ : angle} : θ ≠ -θ ↔ θ ≠ 0 ∧ θ ≠ π :=
by rw [←not_or_distrib, ←eq_neg_self_iff.not]

lemma neg_eq_self_iff {θ : angle} : -θ = θ ↔ θ = 0 ∨ θ = π :=
by rw [eq_comm, eq_neg_self_iff]

lemma neg_ne_self_iff {θ : angle} : -θ ≠ θ ↔ θ ≠ 0 ∧ θ ≠ π :=
by rw [←not_or_distrib, ←neg_eq_self_iff.not]

lemma two_nsmul_eq_pi_iff {θ : angle} : (2 : ℕ) • θ = π ↔ (θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ)) :=
begin
  have h : (π : angle) = (2 : ℕ) • (π / 2 : ℝ), { rw [two_nsmul, ←coe_add, add_halves] },
  nth_rewrite 0 h,
  rw [two_nsmul_eq_iff],
  congr',
  rw [add_comm, ←coe_add, ←sub_eq_zero, ←coe_sub, add_sub_assoc, neg_div, sub_neg_eq_add,
      add_halves, ←two_mul, coe_two_pi]
end

lemma two_zsmul_eq_pi_iff {θ : angle} : (2 : ℤ) • θ = π ↔ (θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ)) :=
by rw [two_zsmul, ←two_nsmul, two_nsmul_eq_pi_iff]

theorem cos_eq_iff_coe_eq_or_eq_neg {θ ψ : ℝ} :
  cos θ = cos ψ ↔ (θ : angle) = ψ ∨ (θ : angle) = -ψ :=
begin
  split,
  { intro Hcos,
    rw [← sub_eq_zero, cos_sub_cos, mul_eq_zero, mul_eq_zero, neg_eq_zero,
        eq_false_intro (two_ne_zero' ℝ), false_or, sin_eq_zero_iff, sin_eq_zero_iff] at Hcos,
    rcases Hcos with ⟨n, hn⟩ | ⟨n, hn⟩,
    { right,
      rw [eq_div_iff_mul_eq (two_ne_zero' ℝ), ← sub_eq_iff_eq_add] at hn,
      rw [← hn, coe_sub, eq_neg_iff_add_eq_zero, sub_add_cancel, mul_assoc,
          coe_int_mul_eq_zsmul, mul_comm, coe_two_pi, zsmul_zero] },
    { left,
      rw [eq_div_iff_mul_eq (two_ne_zero' ℝ), eq_sub_iff_add_eq] at hn,
      rw [← hn, coe_add, mul_assoc,
          coe_int_mul_eq_zsmul, mul_comm, coe_two_pi, zsmul_zero, zero_add] }, },
  { rw [angle_eq_iff_two_pi_dvd_sub, ← coe_neg, angle_eq_iff_two_pi_dvd_sub],
    rintro (⟨k, H⟩ | ⟨k, H⟩),
    rw [← sub_eq_zero, cos_sub_cos, H, mul_assoc 2 π k,
        mul_div_cancel_left _ (two_ne_zero' ℝ), mul_comm π _, sin_int_mul_pi, mul_zero],
    rw [← sub_eq_zero, cos_sub_cos, ← sub_neg_eq_add, H, mul_assoc 2 π k,
        mul_div_cancel_left _ (two_ne_zero' ℝ), mul_comm π _, sin_int_mul_pi, mul_zero,
        zero_mul] }
end

theorem sin_eq_iff_coe_eq_or_add_eq_pi {θ ψ : ℝ} :
  sin θ = sin ψ ↔ (θ : angle) = ψ ∨ (θ : angle) + ψ = π :=
begin
  split,
  { intro Hsin, rw [← cos_pi_div_two_sub, ← cos_pi_div_two_sub] at Hsin,
    cases cos_eq_iff_coe_eq_or_eq_neg.mp Hsin with h h,
    { left, rw [coe_sub, coe_sub] at h, exact sub_right_inj.1 h },
      right, rw [coe_sub, coe_sub, eq_neg_iff_add_eq_zero, add_sub,
      sub_add_eq_add_sub, ← coe_add, add_halves, sub_sub, sub_eq_zero] at h,
    exact h.symm },
  { rw [angle_eq_iff_two_pi_dvd_sub, ←eq_sub_iff_add_eq, ←coe_sub, angle_eq_iff_two_pi_dvd_sub],
    rintro (⟨k, H⟩ | ⟨k, H⟩),
    rw [← sub_eq_zero, sin_sub_sin, H, mul_assoc 2 π k,
         mul_div_cancel_left _ (two_ne_zero' ℝ), mul_comm π _, sin_int_mul_pi, mul_zero,
         zero_mul],
    have H' : θ + ψ = (2 * k) * π + π := by rwa [←sub_add, sub_add_eq_add_sub, sub_eq_iff_eq_add,
      mul_assoc, mul_comm π _, ←mul_assoc] at H,
    rw [← sub_eq_zero, sin_sub_sin, H', add_div, mul_assoc 2 _ π,
        mul_div_cancel_left _ (two_ne_zero' ℝ), cos_add_pi_div_two, sin_int_mul_pi, neg_zero,
        mul_zero] }
end

theorem cos_sin_inj {θ ψ : ℝ} (Hcos : cos θ = cos ψ) (Hsin : sin θ = sin ψ) : (θ : angle) = ψ :=
begin
  cases cos_eq_iff_coe_eq_or_eq_neg.mp Hcos with hc hc, { exact hc },
  cases sin_eq_iff_coe_eq_or_add_eq_pi.mp Hsin with hs hs, { exact hs },
  rw [eq_neg_iff_add_eq_zero, hs] at hc,
  obtain ⟨n, hn⟩ : ∃ n, n • _ = _ := quotient_add_group.left_rel_apply.mp (quotient.exact' hc),
  rw [← neg_one_mul, add_zero, ← sub_eq_zero, zsmul_eq_mul, ← mul_assoc, ← sub_mul,
      mul_eq_zero, eq_false_intro (ne_of_gt pi_pos), or_false, sub_neg_eq_add,
      ← int.cast_zero, ← int.cast_one, ← int.cast_bit0, ← int.cast_mul, ← int.cast_add,
      int.cast_inj] at hn,
  have : (n * 2 + 1) % (2:ℤ) = 0 % (2:ℤ) := congr_arg (%(2:ℤ)) hn,
  rw [add_comm, int.add_mul_mod_self] at this,
  exact absurd this one_ne_zero
end

/-- The sine of a `real.angle`. -/
def sin (θ : angle) : ℝ := sin_periodic.lift θ

@[simp] lemma sin_coe (x : ℝ) : sin (x : angle) = real.sin x :=
rfl

@[continuity] lemma continuous_sin : continuous sin :=
real.continuous_sin.quotient_lift_on' _

/-- The cosine of a `real.angle`. -/
def cos (θ : angle) : ℝ := cos_periodic.lift θ

@[simp] lemma cos_coe (x : ℝ) : cos (x : angle) = real.cos x :=
rfl

@[continuity] lemma continuous_cos : continuous cos :=
real.continuous_cos.quotient_lift_on' _

lemma cos_eq_real_cos_iff_eq_or_eq_neg {θ : angle} {ψ : ℝ} : cos θ = real.cos ψ ↔ θ = ψ ∨ θ = -ψ :=
begin
  induction θ using real.angle.induction_on,
  exact cos_eq_iff_coe_eq_or_eq_neg
end

lemma cos_eq_iff_eq_or_eq_neg {θ ψ : angle} : cos θ = cos ψ ↔ θ = ψ ∨ θ = -ψ :=
begin
  induction ψ using real.angle.induction_on,
  exact cos_eq_real_cos_iff_eq_or_eq_neg
end

lemma sin_eq_real_sin_iff_eq_or_add_eq_pi {θ : angle} {ψ : ℝ} :
  sin θ = real.sin ψ ↔ θ = ψ ∨ θ + ψ = π :=
begin
  induction θ using real.angle.induction_on,
  exact sin_eq_iff_coe_eq_or_add_eq_pi
end

lemma sin_eq_iff_eq_or_add_eq_pi {θ ψ : angle} : sin θ = sin ψ ↔ θ = ψ ∨ θ + ψ = π :=
begin
  induction ψ using real.angle.induction_on,
  exact sin_eq_real_sin_iff_eq_or_add_eq_pi
end

@[simp] lemma sin_zero : sin (0 : angle) = 0 :=
by rw [←coe_zero, sin_coe, real.sin_zero]

@[simp] lemma sin_coe_pi : sin (π : angle) = 0 :=
by rw [sin_coe, real.sin_pi]

lemma sin_eq_zero_iff {θ : angle} : sin θ = 0 ↔ θ = 0 ∨ θ = π :=
begin
  nth_rewrite 0 ←sin_zero,
  rw sin_eq_iff_eq_or_add_eq_pi,
  simp
end

lemma sin_ne_zero_iff {θ : angle} : sin θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π :=
by rw [←not_or_distrib, ←sin_eq_zero_iff]

@[simp] lemma sin_neg (θ : angle) : sin (-θ) = -sin θ :=
begin
  induction θ using real.angle.induction_on,
  exact real.sin_neg _
end

lemma sin_antiperiodic : function.antiperiodic sin (π : angle) :=
begin
  intro θ,
  induction θ using real.angle.induction_on,
  exact real.sin_antiperiodic θ
end

@[simp] lemma sin_add_pi (θ : angle) : sin (θ + π) = -sin θ :=
sin_antiperiodic θ

@[simp] lemma sin_sub_pi (θ : angle) : sin (θ - π) = -sin θ :=
sin_antiperiodic.sub_eq θ

@[simp] lemma cos_zero : cos (0 : angle) = 1 :=
by rw [←coe_zero, cos_coe, real.cos_zero]

@[simp] lemma cos_coe_pi : cos (π : angle) = -1 :=
by rw [cos_coe, real.cos_pi]

@[simp] lemma cos_neg (θ : angle) : cos (-θ) = cos θ :=
begin
  induction θ using real.angle.induction_on,
  exact real.cos_neg _
end

lemma cos_antiperiodic : function.antiperiodic cos (π : angle) :=
begin
  intro θ,
  induction θ using real.angle.induction_on,
  exact real.cos_antiperiodic θ
end

@[simp] lemma cos_add_pi (θ : angle) : cos (θ + π) = -cos θ :=
cos_antiperiodic θ

@[simp] lemma cos_sub_pi (θ : angle) : cos (θ - π) = -cos θ :=
cos_antiperiodic.sub_eq θ

lemma cos_eq_zero_iff {θ : angle} : cos θ = 0 ↔ (θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ)) :=
by rw [← cos_pi_div_two, ← cos_coe, cos_eq_iff_eq_or_eq_neg, ← coe_neg, ← neg_div]

lemma sin_add (θ₁ θ₂ : real.angle) : sin (θ₁ + θ₂) = sin θ₁ * cos θ₂ + cos θ₁ * sin θ₂ :=
begin
  induction θ₁ using real.angle.induction_on,
  induction θ₂ using real.angle.induction_on,
  exact real.sin_add θ₁ θ₂
end

lemma cos_add (θ₁ θ₂ : real.angle) : cos (θ₁ + θ₂) = cos θ₁ * cos θ₂ - sin θ₁ * sin θ₂ :=
begin
  induction θ₂ using real.angle.induction_on,
  induction θ₁ using real.angle.induction_on,
  exact real.cos_add θ₁ θ₂,
end

@[simp] lemma cos_sq_add_sin_sq (θ : real.angle) : cos θ ^ 2 + sin θ ^ 2 = 1 :=
begin
  induction θ using real.angle.induction_on,
  exact real.cos_sq_add_sin_sq θ,
end

lemma sin_add_pi_div_two (θ : angle) : sin (θ + ↑(π / 2)) = cos θ :=
begin
  induction θ using real.angle.induction_on,
  exact sin_add_pi_div_two _
end

lemma sin_sub_pi_div_two (θ : angle) : sin (θ - ↑(π / 2)) = -cos θ :=
begin
  induction θ using real.angle.induction_on,
  exact sin_sub_pi_div_two _
end

lemma sin_pi_div_two_sub (θ : angle) : sin (↑(π / 2) - θ) = cos θ :=
begin
  induction θ using real.angle.induction_on,
  exact sin_pi_div_two_sub _
end

lemma cos_add_pi_div_two (θ : angle) : cos (θ + ↑(π / 2)) = -sin θ :=
begin
  induction θ using real.angle.induction_on,
  exact cos_add_pi_div_two _
end

lemma cos_sub_pi_div_two (θ : angle) : cos (θ - ↑(π / 2)) = sin θ :=
begin
  induction θ using real.angle.induction_on,
  exact cos_sub_pi_div_two _
end

lemma cos_pi_div_two_sub (θ : angle) : cos (↑(π / 2) - θ) = sin θ :=
begin
  induction θ using real.angle.induction_on,
  exact cos_pi_div_two_sub _
end

lemma abs_sin_eq_of_two_nsmul_eq {θ ψ : angle} (h : (2 : ℕ) • θ = (2 : ℕ) • ψ) :
  |sin θ| = |sin ψ| :=
begin
  rw two_nsmul_eq_iff at h,
  rcases h with rfl | rfl,
  { refl },
  { rw [sin_add_pi, abs_neg] }
end

lemma abs_sin_eq_of_two_zsmul_eq {θ ψ : angle} (h : (2 : ℤ) • θ = (2 : ℤ) • ψ) :
  |sin θ| = |sin ψ| :=
begin
  simp_rw [two_zsmul, ←two_nsmul] at h,
  exact abs_sin_eq_of_two_nsmul_eq h
end

lemma abs_cos_eq_of_two_nsmul_eq {θ ψ : angle} (h : (2 : ℕ) • θ = (2 : ℕ) • ψ) :
  |cos θ| = |cos ψ| :=
begin
  rw two_nsmul_eq_iff at h,
  rcases h with rfl | rfl,
  { refl },
  { rw [cos_add_pi, abs_neg] }
end

lemma abs_cos_eq_of_two_zsmul_eq {θ ψ : angle} (h : (2 : ℤ) • θ = (2 : ℤ) • ψ) :
  |cos θ| = |cos ψ| :=
begin
  simp_rw [two_zsmul, ←two_nsmul] at h,
  exact abs_cos_eq_of_two_nsmul_eq h
end

@[simp] lemma coe_to_Ico_mod (θ ψ : ℝ) : ↑(to_Ico_mod ψ two_pi_pos θ) = (θ : angle) :=
begin
  rw angle_eq_iff_two_pi_dvd_sub,
  refine ⟨-to_Ico_div ψ two_pi_pos θ, _⟩,
  rw [to_Ico_mod_sub_self, zsmul_eq_mul, mul_comm]
end

@[simp] lemma coe_to_Ioc_mod (θ ψ : ℝ) : ↑(to_Ioc_mod ψ two_pi_pos θ) = (θ : angle) :=
begin
  rw angle_eq_iff_two_pi_dvd_sub,
  refine ⟨-to_Ioc_div ψ two_pi_pos θ, _⟩,
  rw [to_Ioc_mod_sub_self, zsmul_eq_mul, mul_comm]
end

/-- Convert a `real.angle` to a real number in the interval `Ioc (-π) π`. -/
def to_real (θ : angle) : ℝ :=
(to_Ioc_mod_periodic (-π) two_pi_pos).lift θ

lemma to_real_coe (θ : ℝ) : (θ : angle).to_real = to_Ioc_mod (-π) two_pi_pos θ :=
rfl

lemma to_real_coe_eq_self_iff {θ : ℝ} : (θ : angle).to_real = θ ↔ -π < θ ∧ θ ≤ π :=
begin
  rw [to_real_coe, to_Ioc_mod_eq_self two_pi_pos],
  ring_nf
end

lemma to_real_coe_eq_self_iff_mem_Ioc {θ : ℝ} : (θ : angle).to_real = θ ↔ θ ∈ set.Ioc (-π) π :=
by rw [to_real_coe_eq_self_iff, ←set.mem_Ioc]

lemma to_real_injective : function.injective to_real :=
begin
  intros θ ψ h,
  induction θ using real.angle.induction_on,
  induction ψ using real.angle.induction_on,
  simpa [to_real_coe, to_Ioc_mod_eq_to_Ioc_mod, zsmul_eq_mul, mul_comm _ (2 * π),
         ←angle_eq_iff_two_pi_dvd_sub, eq_comm] using h,
end

@[simp] lemma to_real_inj {θ ψ : angle} : θ.to_real = ψ.to_real ↔ θ = ψ :=
to_real_injective.eq_iff

@[simp] lemma coe_to_real (θ : angle): (θ.to_real : angle) = θ :=
begin
  induction θ using real.angle.induction_on,
  exact coe_to_Ioc_mod _ _
end

lemma neg_pi_lt_to_real (θ : angle) : -π < θ.to_real :=
begin
  induction θ using real.angle.induction_on,
  exact left_lt_to_Ioc_mod _ two_pi_pos _
end

lemma to_real_le_pi (θ : angle) : θ.to_real ≤ π :=
begin
  induction θ using real.angle.induction_on,
  convert to_Ioc_mod_le_right _ two_pi_pos _,
  ring
end

lemma abs_to_real_le_pi (θ : angle) : |θ.to_real| ≤ π :=
abs_le.2 ⟨(neg_pi_lt_to_real _).le, to_real_le_pi _⟩

lemma to_real_mem_Ioc (θ : angle) : θ.to_real ∈ set.Ioc (-π) π :=
⟨neg_pi_lt_to_real _, to_real_le_pi _⟩

@[simp] lemma to_Ioc_mod_to_real (θ : angle): to_Ioc_mod (-π) two_pi_pos θ.to_real = θ.to_real :=
begin
  induction θ using real.angle.induction_on,
  rw to_real_coe,
  exact to_Ioc_mod_to_Ioc_mod _ _ _ _
end

@[simp] lemma to_real_zero : (0 : angle).to_real = 0 :=
begin
  rw [←coe_zero, to_real_coe_eq_self_iff],
  exact ⟨(left.neg_neg_iff.2 real.pi_pos), real.pi_pos.le⟩
end

@[simp] lemma to_real_eq_zero_iff {θ : angle} : θ.to_real = 0 ↔ θ = 0 :=
begin
  nth_rewrite 0 ←to_real_zero,
  exact to_real_inj
end

@[simp] lemma to_real_pi : (π : angle).to_real = π :=
begin
  rw [to_real_coe_eq_self_iff],
  exact ⟨left.neg_lt_self real.pi_pos, le_refl _⟩
end

@[simp] lemma to_real_eq_pi_iff {θ : angle} : θ.to_real = π ↔ θ = π :=
by rw [← to_real_inj, to_real_pi]

lemma pi_ne_zero : (π : angle) ≠ 0 :=
begin
  rw [←to_real_injective.ne_iff, to_real_pi, to_real_zero],
  exact pi_ne_zero
end

@[simp] lemma to_real_pi_div_two : ((π / 2 : ℝ) : angle).to_real = π / 2 :=
to_real_coe_eq_self_iff.2 $ by split; linarith [pi_pos]

@[simp] lemma to_real_eq_pi_div_two_iff {θ : angle} : θ.to_real = π / 2 ↔ θ = (π / 2 : ℝ) :=
by rw [← to_real_inj, to_real_pi_div_two]

@[simp] lemma to_real_neg_pi_div_two : ((-π / 2 : ℝ) : angle).to_real = -π / 2 :=
to_real_coe_eq_self_iff.2 $ by split; linarith [pi_pos]

@[simp] lemma to_real_eq_neg_pi_div_two_iff {θ : angle} : θ.to_real = -π / 2 ↔ θ = (-π / 2 : ℝ) :=
by rw [← to_real_inj, to_real_neg_pi_div_two]

lemma pi_div_two_ne_zero : ((π / 2 : ℝ) : angle) ≠ 0 :=
begin
  rw [←to_real_injective.ne_iff, to_real_pi_div_two, to_real_zero],
  exact div_ne_zero real.pi_ne_zero two_ne_zero
end

lemma neg_pi_div_two_ne_zero : ((-π / 2 : ℝ) : angle) ≠ 0 :=
begin
  rw [←to_real_injective.ne_iff, to_real_neg_pi_div_two, to_real_zero],
  exact div_ne_zero (neg_ne_zero.2 real.pi_ne_zero) two_ne_zero
end

lemma abs_to_real_coe_eq_self_iff {θ : ℝ} : |(θ : angle).to_real| = θ ↔ 0 ≤ θ ∧ θ ≤ π :=
⟨λ h, h ▸ ⟨abs_nonneg _, abs_to_real_le_pi _⟩, λ h,
 (to_real_coe_eq_self_iff.2 ⟨(left.neg_neg_iff.2 real.pi_pos).trans_le h.1, h.2⟩).symm ▸
    abs_eq_self.2 h.1⟩

lemma abs_to_real_neg_coe_eq_self_iff {θ : ℝ} : |(-θ : angle).to_real| = θ ↔ 0 ≤ θ ∧ θ ≤ π :=
begin
  refine ⟨λ h, h ▸ ⟨abs_nonneg _, abs_to_real_le_pi _⟩, λ h, _⟩,
  by_cases hnegpi : θ = π, { simp [hnegpi, real.pi_pos.le] },
  rw [←coe_neg, to_real_coe_eq_self_iff.2 ⟨neg_lt_neg (lt_of_le_of_ne h.2 hnegpi),
                                           (neg_nonpos.2 h.1).trans real.pi_pos.le⟩, abs_neg,
      abs_eq_self.2 h.1]
end

lemma abs_to_real_eq_pi_div_two_iff {θ : angle} :
  |θ.to_real| = π / 2 ↔ (θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ)) :=
by rw [abs_eq (div_nonneg real.pi_pos.le two_pos.le), ←neg_div, to_real_eq_pi_div_two_iff,
       to_real_eq_neg_pi_div_two_iff]

lemma nsmul_to_real_eq_mul {n : ℕ} (h : n ≠ 0) {θ : angle} :
  (n • θ).to_real = n * θ.to_real ↔ θ.to_real ∈ set.Ioc (-π / n) (π / n) :=
begin
  nth_rewrite 0 ←coe_to_real θ,
  have h' : 0 < (n : ℝ), { exact_mod_cast nat.pos_of_ne_zero h },
  rw [←coe_nsmul, nsmul_eq_mul, to_real_coe_eq_self_iff, set.mem_Ioc, div_lt_iff' h',
      le_div_iff' h']
end

lemma two_nsmul_to_real_eq_two_mul {θ : angle} :
  ((2 : ℕ) • θ).to_real = 2 * θ.to_real ↔ θ.to_real ∈ set.Ioc (-π / 2) (π / 2) :=
by exact_mod_cast nsmul_to_real_eq_mul two_ne_zero

lemma two_zsmul_to_real_eq_two_mul {θ : angle} :
  ((2 : ℤ) • θ).to_real = 2 * θ.to_real ↔ θ.to_real ∈ set.Ioc (-π / 2) (π / 2) :=
by rw [two_zsmul, ←two_nsmul, two_nsmul_to_real_eq_two_mul]

lemma to_real_coe_eq_self_sub_two_mul_int_mul_pi_iff {θ : ℝ} {k : ℤ} :
  (θ : angle).to_real = θ - 2 * k * π ↔ θ ∈ set.Ioc ((2 * k - 1 : ℝ) * π) ((2 * k + 1) * π) :=
begin
  rw [←sub_zero (θ : angle), ←zsmul_zero k, ←coe_two_pi, ←coe_zsmul, ←coe_sub,
      zsmul_eq_mul, ←mul_assoc, mul_comm (k : ℝ), to_real_coe_eq_self_iff, set.mem_Ioc],
  exact ⟨λ h, ⟨by linarith, by linarith⟩, λ h, ⟨by linarith, by linarith⟩⟩
end

lemma to_real_coe_eq_self_sub_two_pi_iff {θ : ℝ} :
  (θ : angle).to_real = θ - 2 * π ↔ θ ∈ set.Ioc π (3 * π) :=
by { convert @to_real_coe_eq_self_sub_two_mul_int_mul_pi_iff θ 1; norm_num }

lemma to_real_coe_eq_self_add_two_pi_iff {θ : ℝ} :
  (θ : angle).to_real = θ + 2 * π ↔ θ ∈ set.Ioc (-3 * π) (-π) :=
by { convert @to_real_coe_eq_self_sub_two_mul_int_mul_pi_iff θ (-1); norm_num }

lemma two_nsmul_to_real_eq_two_mul_sub_two_pi {θ : angle} :
  ((2 : ℕ) • θ).to_real = 2 * θ.to_real - 2 * π ↔ π / 2 < θ.to_real :=
begin
  nth_rewrite 0 ←coe_to_real θ,
  rw [←coe_nsmul, two_nsmul, ←two_mul, to_real_coe_eq_self_sub_two_pi_iff, set.mem_Ioc],
  exact ⟨λ h, by linarith,
         λ h, ⟨(div_lt_iff' (zero_lt_two' ℝ)).1 h, by linarith [pi_pos, to_real_le_pi θ]⟩⟩
end

lemma two_zsmul_to_real_eq_two_mul_sub_two_pi {θ : angle} :
  ((2 : ℤ) • θ).to_real = 2 * θ.to_real - 2 * π ↔ π / 2 < θ.to_real :=
by rw [two_zsmul, ←two_nsmul, two_nsmul_to_real_eq_two_mul_sub_two_pi]

lemma two_nsmul_to_real_eq_two_mul_add_two_pi {θ : angle} :
  ((2 : ℕ) • θ).to_real = 2 * θ.to_real + 2 * π ↔ θ.to_real ≤ -π / 2 :=
begin
  nth_rewrite 0 ←coe_to_real θ,
  rw [←coe_nsmul, two_nsmul, ←two_mul, to_real_coe_eq_self_add_two_pi_iff, set.mem_Ioc],
  refine ⟨λ h, by linarith,
          λ h, ⟨by linarith [pi_pos, neg_pi_lt_to_real θ], (le_div_iff' (zero_lt_two' ℝ)).1 h⟩⟩
end

lemma two_zsmul_to_real_eq_two_mul_add_two_pi {θ : angle} :
  ((2 : ℤ) • θ).to_real = 2 * θ.to_real + 2 * π ↔ θ.to_real ≤ -π / 2 :=
by rw [two_zsmul, ←two_nsmul, two_nsmul_to_real_eq_two_mul_add_two_pi]

@[simp] lemma sin_to_real (θ : angle) : real.sin θ.to_real = sin θ :=
by conv_rhs { rw [← coe_to_real θ, sin_coe] }

@[simp] lemma cos_to_real (θ : angle) : real.cos θ.to_real = cos θ :=
by conv_rhs { rw [← coe_to_real θ, cos_coe] }

lemma cos_nonneg_iff_abs_to_real_le_pi_div_two {θ : angle} : 0 ≤ cos θ ↔ |θ.to_real| ≤ π / 2 :=
begin
  nth_rewrite 0 ←coe_to_real θ,
  rw [abs_le, cos_coe],
  refine ⟨λ h, _, cos_nonneg_of_mem_Icc⟩,
  by_contra hn,
  rw [not_and_distrib, not_le, not_le] at hn,
  refine (not_lt.2 h) _,
  rcases hn with hn | hn,
  { rw ←real.cos_neg,
    refine cos_neg_of_pi_div_two_lt_of_lt (by linarith) _,
    linarith [neg_pi_lt_to_real θ] },
  { refine cos_neg_of_pi_div_two_lt_of_lt hn _,
    linarith [to_real_le_pi θ] }
end

lemma cos_pos_iff_abs_to_real_lt_pi_div_two {θ : angle} : 0 < cos θ ↔ |θ.to_real| < π / 2 :=
begin
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, cos_nonneg_iff_abs_to_real_le_pi_div_two,
      ←and_congr_right],
  rintro -,
  rw [ne.def, ne.def, not_iff_not, @eq_comm ℝ 0, abs_to_real_eq_pi_div_two_iff, cos_eq_zero_iff]
end

lemma cos_neg_iff_pi_div_two_lt_abs_to_real {θ : angle} : cos θ < 0 ↔ π / 2 < |θ.to_real| :=
by rw [←not_le, ←not_le, not_iff_not, cos_nonneg_iff_abs_to_real_le_pi_div_two]

lemma abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi {θ ψ : angle}
  (h : (2 : ℕ) • θ + (2 : ℕ) • ψ = π) : |cos θ| = |sin ψ| :=
begin
  rw [←eq_sub_iff_add_eq, ←two_nsmul_coe_div_two, ←nsmul_sub, two_nsmul_eq_iff] at h,
  rcases h with rfl | rfl;
    simp [cos_pi_div_two_sub]
end

lemma abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi {θ ψ : angle}
  (h : (2 : ℤ) • θ + (2 : ℤ) • ψ = π) : |cos θ| = |sin ψ| :=
begin
  simp_rw [two_zsmul, ←two_nsmul] at h,
  exact abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi h
end

/-- The tangent of a `real.angle`. -/
def tan (θ : angle) : ℝ := sin θ / cos θ

lemma tan_eq_sin_div_cos (θ : angle) : tan θ = sin θ / cos θ := rfl

@[simp] lemma tan_coe (x : ℝ) : tan (x : angle) = real.tan x :=
by rw [tan, sin_coe, cos_coe, real.tan_eq_sin_div_cos]

@[simp] lemma tan_zero : tan (0 : angle) = 0 :=
by rw [←coe_zero, tan_coe, real.tan_zero]

@[simp] lemma tan_coe_pi : tan (π : angle) = 0 :=
by rw [tan_eq_sin_div_cos, sin_coe_pi, zero_div]

lemma tan_periodic : function.periodic tan (π : angle) :=
begin
  intro θ,
  induction θ using real.angle.induction_on,
  rw [←coe_add, tan_coe, tan_coe],
  exact real.tan_periodic θ
end

@[simp] lemma tan_add_pi (θ : angle) : tan (θ + π) = tan θ :=
tan_periodic θ

@[simp] lemma tan_sub_pi (θ : angle) : tan (θ - π) = tan θ :=
tan_periodic.sub_eq θ

@[simp] lemma tan_to_real (θ : angle) : real.tan θ.to_real = tan θ :=
by conv_rhs { rw [←coe_to_real θ, tan_coe] }

lemma tan_eq_of_two_nsmul_eq {θ ψ : angle} (h : (2 : ℕ) • θ = (2 : ℕ) • ψ) : tan θ = tan ψ :=
begin
  rw two_nsmul_eq_iff at h,
  rcases h with rfl | rfl,
  { refl },
  { exact tan_add_pi _ }
end

lemma tan_eq_of_two_zsmul_eq {θ ψ : angle} (h : (2 : ℤ) • θ = (2 : ℤ) • ψ) : tan θ = tan ψ :=
begin
  simp_rw [two_zsmul, ←two_nsmul] at h,
  exact tan_eq_of_two_nsmul_eq h
end

lemma tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi {θ ψ : angle}
  (h : (2 : ℕ) • θ + (2 : ℕ) • ψ = π) : tan ψ = (tan θ)⁻¹ :=
begin
  induction θ using real.angle.induction_on,
  induction ψ using real.angle.induction_on,
  rw [←smul_add, ←coe_add, ←coe_nsmul, two_nsmul, ←two_mul, angle_eq_iff_two_pi_dvd_sub] at h,
  rcases h with ⟨k, h⟩,
  rw [sub_eq_iff_eq_add, ←mul_inv_cancel_left₀ two_ne_zero π, mul_assoc, ←mul_add,
      mul_right_inj' (two_ne_zero' ℝ), ←eq_sub_iff_add_eq',
      mul_inv_cancel_left₀ two_ne_zero π, inv_mul_eq_div, mul_comm] at h,
  rw [tan_coe, tan_coe, ←tan_pi_div_two_sub, h, add_sub_assoc, add_comm],
  exact real.tan_periodic.int_mul _ _
end

lemma tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi {θ ψ : angle}
  (h : (2 : ℤ) • θ + (2 : ℤ) • ψ = π) : tan ψ = (tan θ)⁻¹ :=
begin
  simp_rw [two_zsmul, ←two_nsmul] at h,
  exact tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi h
end

/-- The sign of a `real.angle` is `0` if the angle is `0` or `π`, `1` if the angle is strictly
between `0` and `π` and `-1` is the angle is strictly between `-π` and `0`. It is defined as the
sign of the sine of the angle. -/
def sign (θ : angle) : sign_type := sign (sin θ)

@[simp] lemma sign_zero : (0 : angle).sign = 0 :=
by rw [sign, sin_zero, sign_zero]

@[simp] lemma sign_coe_pi : (π : angle).sign = 0 :=
by rw [sign, sin_coe_pi, _root_.sign_zero]

@[simp] lemma sign_neg (θ : angle) : (-θ).sign = - θ.sign :=
by simp_rw [sign, sin_neg, left.sign_neg]

lemma sign_antiperiodic : function.antiperiodic sign (π : angle) :=
λ θ, by rw [sign, sign, sin_add_pi, left.sign_neg]

@[simp] lemma sign_add_pi (θ : angle) : (θ + π).sign = -θ.sign :=
sign_antiperiodic θ

@[simp] lemma sign_pi_add (θ : angle) : ((π : angle) + θ).sign = -θ.sign :=
by rw [add_comm, sign_add_pi]

@[simp] lemma sign_sub_pi (θ : angle) : (θ - π).sign = -θ.sign :=
sign_antiperiodic.sub_eq θ

@[simp] lemma sign_pi_sub (θ : angle) : ((π : angle) - θ).sign = θ.sign :=
by simp [sign_antiperiodic.sub_eq']

lemma sign_eq_zero_iff {θ : angle} : θ.sign = 0 ↔ θ = 0 ∨ θ = π :=
by rw [sign, sign_eq_zero_iff, sin_eq_zero_iff]

lemma sign_ne_zero_iff {θ : angle} : θ.sign ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π :=
by rw [←not_or_distrib, ←sign_eq_zero_iff]

lemma to_real_neg_iff_sign_neg {θ : angle} : θ.to_real < 0 ↔ θ.sign = -1 :=
begin
  rw [sign, ←sin_to_real, sign_eq_neg_one_iff],
  rcases lt_trichotomy θ.to_real 0 with (h|h|h),
  { exact ⟨λ _, real.sin_neg_of_neg_of_neg_pi_lt h (neg_pi_lt_to_real θ), λ _, h⟩ },
  { simp [h] },
  { exact ⟨λ hn, false.elim (h.asymm hn),
           λ hn, false.elim (hn.not_le (sin_nonneg_of_nonneg_of_le_pi h.le (to_real_le_pi θ)))⟩ }
end

lemma to_real_nonneg_iff_sign_nonneg {θ : angle} : 0 ≤ θ.to_real ↔ 0 ≤ θ.sign :=
begin
  rcases lt_trichotomy θ.to_real 0 with (h|h|h),
  { refine ⟨λ hn, false.elim (h.not_le hn), λ hn, _⟩,
    rw [to_real_neg_iff_sign_neg.1 h] at hn,
    exact false.elim (hn.not_lt dec_trivial) },
  { simp [h, sign, ←sin_to_real] },
  { refine ⟨λ _, _, λ _, h.le⟩,
    rw [sign, ←sin_to_real, sign_nonneg_iff],
    exact sin_nonneg_of_nonneg_of_le_pi h.le (to_real_le_pi θ) }
end

@[simp] lemma sign_to_real {θ : angle} (h : θ ≠ π) : _root_.sign θ.to_real = θ.sign :=
begin
  rcases lt_trichotomy θ.to_real 0 with (ht|ht|ht),
  { simp [ht, to_real_neg_iff_sign_neg.1 ht] },
  { simp [sign, ht, ←sin_to_real] },
  { rw [sign, ←sin_to_real, sign_pos ht,
        sign_pos (sin_pos_of_pos_of_lt_pi ht
          ((to_real_le_pi θ).lt_of_ne (to_real_eq_pi_iff.not.2 h)))] }
end

lemma coe_abs_to_real_of_sign_nonneg {θ : angle} (h : 0 ≤ θ.sign) : ↑|θ.to_real| = θ :=
by rw [abs_eq_self.2 (to_real_nonneg_iff_sign_nonneg.2 h), coe_to_real]

lemma neg_coe_abs_to_real_of_sign_nonpos {θ : angle} (h : θ.sign ≤ 0) : -↑|θ.to_real| = θ :=
begin
  rw sign_type.nonpos_iff at h,
  rcases h with h|h,
  { rw [abs_of_neg (to_real_neg_iff_sign_neg.2 h), coe_neg, neg_neg, coe_to_real] },
  { rw sign_eq_zero_iff at h,
    rcases h with rfl|rfl;
      simp [abs_of_pos real.pi_pos] }
end

lemma eq_iff_sign_eq_and_abs_to_real_eq {θ ψ : angle} :
  θ = ψ ↔ θ.sign = ψ.sign ∧ |θ.to_real| = |ψ.to_real| :=
begin
  refine ⟨_, λ h, _⟩, { rintro rfl, exact ⟨rfl, rfl⟩ },
  rcases h with ⟨hs, hr⟩,
  rw abs_eq_abs at hr,
  rcases hr with (hr|hr),
  { exact to_real_injective hr },
  { by_cases h : θ = π,
    { rw [h, to_real_pi, ← neg_eq_iff_eq_neg] at hr,
      exact false.elim ((neg_pi_lt_to_real ψ).ne hr) },
    { by_cases h' : ψ = π,
      { rw [h', to_real_pi] at hr,
        exact false.elim ((neg_pi_lt_to_real θ).ne hr.symm) },
      { rw [←sign_to_real h, ←sign_to_real h', hr, left.sign_neg, sign_type.neg_eq_self_iff,
            _root_.sign_eq_zero_iff, to_real_eq_zero_iff] at hs,
        rw [hs, to_real_zero, neg_zero, to_real_eq_zero_iff] at hr,
        rw [hr, hs] } } }
end

lemma eq_iff_abs_to_real_eq_of_sign_eq {θ ψ : angle} (h : θ.sign = ψ.sign) :
  θ = ψ ↔ |θ.to_real| = |ψ.to_real| :=
by simpa [h] using @eq_iff_sign_eq_and_abs_to_real_eq θ ψ

@[simp] lemma sign_coe_pi_div_two : (↑(π / 2) : angle).sign = 1 :=
by rw [sign, sin_coe, sin_pi_div_two, sign_one]

@[simp] lemma sign_coe_neg_pi_div_two : (↑(-π / 2) : angle).sign = -1 :=
by rw [sign, sin_coe, neg_div, real.sin_neg, sin_pi_div_two, left.sign_neg, sign_one]

lemma sign_coe_nonneg_of_nonneg_of_le_pi {θ : ℝ} (h0 : 0 ≤ θ) (hpi : θ ≤ π) :
  0 ≤ (θ : angle).sign :=
begin
  rw [sign, sign_nonneg_iff],
  exact sin_nonneg_of_nonneg_of_le_pi h0 hpi
end

lemma sign_neg_coe_nonpos_of_nonneg_of_le_pi {θ : ℝ} (h0 : 0 ≤ θ) (hpi : θ ≤ π) :
  (-θ : angle).sign ≤ 0 :=
begin
  rw [sign, sign_nonpos_iff, sin_neg, left.neg_nonpos_iff],
  exact sin_nonneg_of_nonneg_of_le_pi h0 hpi
end

lemma sign_two_nsmul_eq_sign_iff {θ : angle} :
  ((2 : ℕ) • θ).sign = θ.sign ↔ (θ = π ∨ |θ.to_real| < π / 2) :=
begin
  by_cases hpi : θ = π, { simp [hpi] },
  rw or_iff_right hpi,
  refine ⟨λ h, _, λ h, _⟩,
  { by_contra hle,
    rw [not_lt, le_abs, le_neg] at hle,
    have hpi' : θ.to_real ≠ π, { simpa using hpi },
    rcases hle with hle | hle; rcases hle.eq_or_lt with heq | hlt,
    { rw [←coe_to_real θ, ←heq] at h, simpa using h },
    { rw [←sign_to_real hpi, sign_pos (pi_div_two_pos.trans hlt),
          ←sign_to_real, two_nsmul_to_real_eq_two_mul_sub_two_pi.2 hlt, _root_.sign_neg] at h,
      { simpa using h },
      { rw ←mul_sub,
        exact mul_neg_of_pos_of_neg two_pos (sub_neg.2 ((to_real_le_pi _).lt_of_ne hpi')) },
      { intro he, simpa [he] using h } },
    { rw [←coe_to_real θ, heq] at h, simpa using h },
    { rw [←sign_to_real hpi,
          _root_.sign_neg (hlt.trans (left.neg_neg_iff.2 pi_div_two_pos)),
          ←sign_to_real] at h, swap, { intro he, simpa [he] using h },
      rw ←neg_div at hlt,
      rw [two_nsmul_to_real_eq_two_mul_add_two_pi.2 hlt.le, sign_pos] at h,
      { simpa using h },
      { linarith [neg_pi_lt_to_real θ] } } },
  { have hpi' : (2 : ℕ) • θ ≠ π,
    { rw [ne.def, two_nsmul_eq_pi_iff, not_or_distrib],
      split,
      { rintro rfl, simpa [pi_pos, div_pos, abs_of_pos] using h },
      { rintro rfl,
        rw [to_real_neg_pi_div_two] at h,
        simpa [pi_pos, div_pos, neg_div, abs_of_pos] using h } },
    rw [abs_lt, ←neg_div] at h,
    rw [←sign_to_real hpi, ←sign_to_real hpi', two_nsmul_to_real_eq_two_mul.2 ⟨h.1, h.2.le⟩,
        sign_mul, sign_pos (zero_lt_two' ℝ), one_mul] }
end

lemma sign_two_zsmul_eq_sign_iff {θ : angle} :
  ((2 : ℤ) • θ).sign = θ.sign ↔ (θ = π ∨ |θ.to_real| < π / 2) :=
by rw [two_zsmul, ←two_nsmul, sign_two_nsmul_eq_sign_iff]

lemma continuous_at_sign {θ : angle} (h0 : θ ≠ 0) (hpi : θ ≠ π) : continuous_at sign θ :=
(continuous_at_sign_of_ne_zero (sin_ne_zero_iff.2 ⟨h0, hpi⟩)).comp continuous_sin.continuous_at

lemma _root_.continuous_on.angle_sign_comp {α : Type*} [topological_space α] {f : α → angle}
  {s : set α} (hf : continuous_on f s) (hs : ∀ z ∈ s, f z ≠ 0 ∧ f z ≠ π) :
  continuous_on (sign ∘ f) s :=
begin
  refine (continuous_at.continuous_on (λ θ hθ, _)).comp hf (set.maps_to_image f s),
  obtain ⟨z, hz, rfl⟩ := hθ,
  exact continuous_at_sign (hs _ hz).1 (hs _ hz).2
end

/-- Suppose a function to angles is continuous on a connected set and never takes the values `0`
or `π` on that set. Then the values of the function on that set all have the same sign. -/
lemma sign_eq_of_continuous_on {α : Type*} [topological_space α] {f : α → angle} {s : set α}
  {x y : α} (hc : is_connected s) (hf : continuous_on f s) (hs : ∀ z ∈ s, f z ≠ 0 ∧ f z ≠ π)
  (hx : x ∈ s) (hy : y ∈ s) : (f y).sign = (f x).sign :=
(hc.image _ (hf.angle_sign_comp hs)).is_preconnected.subsingleton
  (set.mem_image_of_mem _ hy) (set.mem_image_of_mem _ hx)

end angle

end real
