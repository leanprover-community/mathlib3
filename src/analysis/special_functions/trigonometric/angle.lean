/-
Copyright (c) 2019 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
import analysis.special_functions.trigonometric.basic
import algebra.char_zero.quotient

/-!
# The type of angles

In this file we define `real.angle` to be the quotient group `ℝ/2πℤ` and prove a few simple lemmas
about trigonometric functions and angles.
-/

open_locale real

noncomputable theory

namespace real

/-- The type of angles -/
@[derive [add_comm_group, topological_space, topological_add_group]]
def angle : Type :=
ℝ ⧸ (add_subgroup.zmultiples (2 * π))

namespace angle

instance : inhabited angle := ⟨0⟩

instance : has_coe ℝ angle := ⟨quotient_add_group.mk' _⟩

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

lemma two_zsmul_eq_zero_iff {θ : angle} : (2 : ℤ) • θ = 0 ↔ (θ = 0 ∨ θ = π) :=
by simp_rw [two_zsmul, ←two_nsmul, two_nsmul_eq_zero_iff]

theorem cos_eq_iff_coe_eq_or_eq_neg {θ ψ : ℝ} :
  cos θ = cos ψ ↔ (θ : angle) = ψ ∨ (θ : angle) = -ψ :=
begin
  split,
  { intro Hcos,
    rw [← sub_eq_zero, cos_sub_cos, mul_eq_zero, mul_eq_zero, neg_eq_zero,
        eq_false_intro two_ne_zero, false_or, sin_eq_zero_iff, sin_eq_zero_iff] at Hcos,
    rcases Hcos with ⟨n, hn⟩ | ⟨n, hn⟩,
    { right,
      rw [eq_div_iff_mul_eq (@two_ne_zero ℝ _ _), ← sub_eq_iff_eq_add] at hn,
      rw [← hn, coe_sub, eq_neg_iff_add_eq_zero, sub_add_cancel, mul_assoc,
          coe_int_mul_eq_zsmul, mul_comm, coe_two_pi, zsmul_zero] },
    { left,
      rw [eq_div_iff_mul_eq (@two_ne_zero ℝ _ _), eq_sub_iff_add_eq] at hn,
      rw [← hn, coe_add, mul_assoc,
          coe_int_mul_eq_zsmul, mul_comm, coe_two_pi, zsmul_zero, zero_add] },
    apply_instance, },
  { rw [angle_eq_iff_two_pi_dvd_sub, ← coe_neg, angle_eq_iff_two_pi_dvd_sub],
    rintro (⟨k, H⟩ | ⟨k, H⟩),
    rw [← sub_eq_zero, cos_sub_cos, H, mul_assoc 2 π k,
        mul_div_cancel_left _ (@two_ne_zero ℝ _ _), mul_comm π _, sin_int_mul_pi, mul_zero],
    rw [← sub_eq_zero, cos_sub_cos, ← sub_neg_eq_add, H, mul_assoc 2 π k,
        mul_div_cancel_left _ (@two_ne_zero ℝ _ _), mul_comm π _, sin_int_mul_pi, mul_zero,
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
         mul_div_cancel_left _ (@two_ne_zero ℝ _ _), mul_comm π _, sin_int_mul_pi, mul_zero,
         zero_mul],
    have H' : θ + ψ = (2 * k) * π + π := by rwa [←sub_add, sub_add_eq_add_sub, sub_eq_iff_eq_add,
      mul_assoc, mul_comm π _, ←mul_assoc] at H,
    rw [← sub_eq_zero, sin_sub_sin, H', add_div, mul_assoc 2 _ π,
        mul_div_cancel_left _ (@two_ne_zero ℝ _ _), cos_add_pi_div_two, sin_int_mul_pi, neg_zero,
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
continuous_quotient_lift_on' _ real.continuous_sin

/-- The cosine of a `real.angle`. -/
def cos (θ : angle) : ℝ := cos_periodic.lift θ

@[simp] lemma cos_coe (x : ℝ) : cos (x : angle) = real.cos x :=
rfl

@[continuity] lemma continuous_cos : continuous cos :=
continuous_quotient_lift_on' _ real.continuous_cos

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

end angle

end real
