/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import analysis.special_functions.exp
import data.set.intervals.infinite

/-!
# Trigonometric functions

## Main definitions

This file contains the definition of `π`.

See also `analysis.special_functions.trigonometric.inverse` and
`analysis.special_functions.trigonometric.arctan` for the inverse trigonometric functions.

See also `analysis.special_functions.complex.arg` and
`analysis.special_functions.complex.log` for the complex argument function
and the complex logarithm.

## Main statements

Many basic inequalities on the real trigonometric functions are established.

The continuity of the usual trigonometric functions is proved.

Several facts about the real trigonometric functions have the proofs deferred to
`analysis.special_functions.trigonometric.complex`,
as they are most easily proved by appealing to the corresponding fact for
complex trigonometric functions.

See also `analysis.special_functions.trigonometric.chebyshev` for the multiple angle formulas
in terms of Chebyshev polynomials.

## Tags

sin, cos, tan, angle
-/

noncomputable theory
open_locale classical topological_space filter
open set filter

namespace complex

@[continuity] lemma continuous_sin : continuous sin :=
by { change continuous (λ z, ((exp (-z * I) - exp (z * I)) * I) / 2), continuity, }

lemma continuous_on_sin {s : set ℂ} : continuous_on sin s := continuous_sin.continuous_on

@[continuity] lemma continuous_cos : continuous cos :=
by { change continuous (λ z, (exp (z * I) + exp (-z * I)) / 2), continuity, }

lemma continuous_on_cos {s : set ℂ} : continuous_on cos s := continuous_cos.continuous_on

@[continuity] lemma continuous_sinh : continuous sinh :=
by { change continuous (λ z, (exp z - exp (-z)) / 2), continuity, }

@[continuity] lemma continuous_cosh : continuous cosh :=
by { change continuous (λ z, (exp z + exp (-z)) / 2), continuity, }

end complex


namespace real

variables {x y z : ℝ}

@[continuity] lemma continuous_sin : continuous sin :=
complex.continuous_re.comp (complex.continuous_sin.comp complex.continuous_of_real)

lemma continuous_on_sin {s} : continuous_on sin s :=
continuous_sin.continuous_on

@[continuity] lemma continuous_cos : continuous cos :=
complex.continuous_re.comp (complex.continuous_cos.comp complex.continuous_of_real)

lemma continuous_on_cos {s} : continuous_on cos s := continuous_cos.continuous_on

@[continuity] lemma continuous_sinh : continuous sinh :=
complex.continuous_re.comp (complex.continuous_sinh.comp complex.continuous_of_real)

@[continuity] lemma continuous_cosh : continuous cosh :=
complex.continuous_re.comp (complex.continuous_cosh.comp complex.continuous_of_real)

end real

namespace real

lemma exists_cos_eq_zero : 0 ∈ cos '' Icc (1:ℝ) 2 :=
intermediate_value_Icc' (by norm_num) continuous_on_cos
  ⟨le_of_lt cos_two_neg, le_of_lt cos_one_pos⟩

/-- The number π = 3.14159265... Defined here using choice as twice a zero of cos in [1,2], from
which one can derive all its properties. For explicit bounds on π, see `data.real.pi.bounds`. -/
protected noncomputable def pi : ℝ := 2 * classical.some exists_cos_eq_zero

localized "notation `π` := real.pi" in real

@[simp] lemma cos_pi_div_two : cos (π / 2) = 0 :=
by rw [real.pi, mul_div_cancel_left _ (@two_ne_zero' ℝ _ _ _)];
  exact (classical.some_spec exists_cos_eq_zero).2

lemma one_le_pi_div_two : (1 : ℝ) ≤ π / 2 :=
by rw [real.pi, mul_div_cancel_left _ (@two_ne_zero' ℝ _ _ _)];
  exact (classical.some_spec exists_cos_eq_zero).1.1

lemma pi_div_two_le_two : π / 2 ≤ 2 :=
by rw [real.pi, mul_div_cancel_left _ (@two_ne_zero' ℝ _ _ _)];
  exact (classical.some_spec exists_cos_eq_zero).1.2

lemma two_le_pi : (2 : ℝ) ≤ π :=
(div_le_div_right (show (0 : ℝ) < 2, by norm_num)).1
  (by rw div_self (@two_ne_zero' ℝ _ _ _); exact one_le_pi_div_two)

lemma pi_le_four : π ≤ 4 :=
(div_le_div_right (show (0 : ℝ) < 2, by norm_num)).1
  (calc π / 2 ≤ 2 : pi_div_two_le_two
    ... = 4 / 2 : by norm_num)

lemma pi_pos : 0 < π :=
lt_of_lt_of_le (by norm_num) two_le_pi

lemma pi_ne_zero : π ≠ 0 :=
ne_of_gt pi_pos

lemma pi_div_two_pos : 0 < π / 2 :=
half_pos pi_pos

lemma two_pi_pos : 0 < 2 * π :=
by linarith [pi_pos]

end real

namespace nnreal
open real
open_locale real nnreal

/-- `π` considered as a nonnegative real. -/
noncomputable def pi : ℝ≥0 := ⟨π, real.pi_pos.le⟩

@[simp] lemma coe_real_pi : (pi : ℝ) = π := rfl

lemma pi_pos : 0 < pi := by exact_mod_cast real.pi_pos

lemma pi_ne_zero : pi ≠ 0 := pi_pos.ne'

end nnreal

namespace real
open_locale real

@[simp] lemma sin_pi : sin π = 0 :=
by rw [← mul_div_cancel_left π (@two_ne_zero ℝ _ _), two_mul, add_div,
    sin_add, cos_pi_div_two]; simp

@[simp] lemma cos_pi : cos π = -1 :=
by rw [← mul_div_cancel_left π (@two_ne_zero ℝ _ _), mul_div_assoc,
    cos_two_mul, cos_pi_div_two];
  simp [bit0, pow_add]

@[simp] lemma sin_two_pi : sin (2 * π) = 0 :=
by simp [two_mul, sin_add]

@[simp] lemma cos_two_pi : cos (2 * π) = 1 :=
by simp [two_mul, cos_add]

lemma sin_antiperiodic : function.antiperiodic sin π :=
by simp [sin_add]

lemma sin_periodic : function.periodic sin (2 * π) :=
sin_antiperiodic.periodic

@[simp] lemma sin_add_pi (x : ℝ) : sin (x + π) = -sin x :=
sin_antiperiodic x

@[simp] lemma sin_add_two_pi (x : ℝ) : sin (x + 2 * π) = sin x :=
sin_periodic x

@[simp] lemma sin_sub_pi (x : ℝ) : sin (x - π) = -sin x :=
sin_antiperiodic.sub_eq x

@[simp] lemma sin_sub_two_pi (x : ℝ) : sin (x - 2 * π) = sin x :=
sin_periodic.sub_eq x

@[simp] lemma sin_pi_sub (x : ℝ) : sin (π - x) = sin x :=
neg_neg (sin x) ▸ sin_neg x ▸ sin_antiperiodic.sub_eq'

@[simp] lemma sin_two_pi_sub (x : ℝ) : sin (2 * π - x) = -sin x :=
sin_neg x ▸ sin_periodic.sub_eq'

@[simp] lemma sin_nat_mul_pi (n : ℕ) : sin (n * π) = 0 :=
sin_antiperiodic.nat_mul_eq_of_eq_zero sin_zero n

@[simp] lemma sin_int_mul_pi (n : ℤ) : sin (n * π) = 0 :=
sin_antiperiodic.int_mul_eq_of_eq_zero sin_zero n

@[simp] lemma sin_add_nat_mul_two_pi (x : ℝ) (n : ℕ) : sin (x + n * (2 * π)) = sin x :=
sin_periodic.nat_mul n x

@[simp] lemma sin_add_int_mul_two_pi (x : ℝ) (n : ℤ) : sin (x + n * (2 * π)) = sin x :=
sin_periodic.int_mul n x

@[simp] lemma sin_sub_nat_mul_two_pi (x : ℝ) (n : ℕ) : sin (x - n * (2 * π)) = sin x :=
sin_periodic.sub_nat_mul_eq n

@[simp] lemma sin_sub_int_mul_two_pi (x : ℝ) (n : ℤ) : sin (x - n * (2 * π)) = sin x :=
sin_periodic.sub_int_mul_eq n

@[simp] lemma sin_nat_mul_two_pi_sub (x : ℝ) (n : ℕ) : sin (n * (2 * π) - x) = -sin x :=
sin_neg x ▸ sin_periodic.nat_mul_sub_eq n

@[simp] lemma sin_int_mul_two_pi_sub (x : ℝ) (n : ℤ) : sin (n * (2 * π) - x) = -sin x :=
sin_neg x ▸ sin_periodic.int_mul_sub_eq n

lemma cos_antiperiodic : function.antiperiodic cos π :=
by simp [cos_add]

lemma cos_periodic : function.periodic cos (2 * π) :=
cos_antiperiodic.periodic

@[simp] lemma cos_add_pi (x : ℝ) : cos (x + π) = -cos x :=
cos_antiperiodic x

@[simp] lemma cos_add_two_pi (x : ℝ) : cos (x + 2 * π) = cos x :=
cos_periodic x

@[simp] lemma cos_sub_pi (x : ℝ) : cos (x - π) = -cos x :=
cos_antiperiodic.sub_eq x

@[simp] lemma cos_sub_two_pi (x : ℝ) : cos (x - 2 * π) = cos x :=
cos_periodic.sub_eq x

@[simp] lemma cos_pi_sub (x : ℝ) : cos (π - x) = -cos x :=
cos_neg x ▸ cos_antiperiodic.sub_eq'

@[simp] lemma cos_two_pi_sub (x : ℝ) : cos (2 * π - x) = cos x :=
cos_neg x ▸ cos_periodic.sub_eq'

@[simp] lemma cos_nat_mul_two_pi (n : ℕ) : cos (n * (2 * π)) = 1 :=
(cos_periodic.nat_mul_eq n).trans cos_zero

@[simp] lemma cos_int_mul_two_pi (n : ℤ) : cos (n * (2 * π)) = 1 :=
(cos_periodic.int_mul_eq n).trans cos_zero

@[simp] lemma cos_add_nat_mul_two_pi (x : ℝ) (n : ℕ) : cos (x + n * (2 * π)) = cos x :=
cos_periodic.nat_mul n x

@[simp] lemma cos_add_int_mul_two_pi (x : ℝ) (n : ℤ) : cos (x + n * (2 * π)) = cos x :=
cos_periodic.int_mul n x

@[simp] lemma cos_sub_nat_mul_two_pi (x : ℝ) (n : ℕ) : cos (x - n * (2 * π)) = cos x :=
cos_periodic.sub_nat_mul_eq n

@[simp] lemma cos_sub_int_mul_two_pi (x : ℝ) (n : ℤ) : cos (x - n * (2 * π)) = cos x :=
cos_periodic.sub_int_mul_eq n

@[simp] lemma cos_nat_mul_two_pi_sub (x : ℝ) (n : ℕ) : cos (n * (2 * π) - x) = cos x :=
cos_neg x ▸ cos_periodic.nat_mul_sub_eq n

@[simp] lemma cos_int_mul_two_pi_sub (x : ℝ) (n : ℤ) : cos (n * (2 * π) - x) = cos x :=
cos_neg x ▸ cos_periodic.int_mul_sub_eq n

@[simp] lemma cos_nat_mul_two_pi_add_pi (n : ℕ) : cos (n * (2 * π) + π) = -1 :=
by simpa only [cos_zero] using (cos_periodic.nat_mul n).add_antiperiod_eq cos_antiperiodic

@[simp] lemma cos_int_mul_two_pi_add_pi (n : ℤ) : cos (n * (2 * π) + π) = -1 :=
by simpa only [cos_zero] using (cos_periodic.int_mul n).add_antiperiod_eq cos_antiperiodic

@[simp] lemma cos_nat_mul_two_pi_sub_pi (n : ℕ) : cos (n * (2 * π) - π) = -1 :=
by simpa only [cos_zero] using (cos_periodic.nat_mul n).sub_antiperiod_eq cos_antiperiodic

@[simp] lemma cos_int_mul_two_pi_sub_pi (n : ℤ) : cos (n * (2 * π) - π) = -1 :=
by simpa only [cos_zero] using (cos_periodic.int_mul n).sub_antiperiod_eq cos_antiperiodic

lemma sin_pos_of_pos_of_lt_pi {x : ℝ} (h0x : 0 < x) (hxp : x < π) : 0 < sin x :=
if hx2 : x ≤ 2 then sin_pos_of_pos_of_le_two h0x hx2
else
  have (2 : ℝ) + 2 = 4, from rfl,
  have π - x ≤ 2, from sub_le_iff_le_add.2
    (le_trans pi_le_four (this ▸ add_le_add_left (le_of_not_ge hx2) _)),
  sin_pi_sub x ▸ sin_pos_of_pos_of_le_two (sub_pos.2 hxp) this

lemma sin_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 π) : 0 < sin x :=
sin_pos_of_pos_of_lt_pi hx.1 hx.2

lemma sin_nonneg_of_mem_Icc {x : ℝ} (hx : x ∈ Icc 0 π) : 0 ≤ sin x :=
begin
  rw ← closure_Ioo pi_pos at hx,
  exact closure_lt_subset_le continuous_const continuous_sin
    (closure_mono (λ y, sin_pos_of_mem_Ioo) hx)
end

lemma sin_nonneg_of_nonneg_of_le_pi {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ π) : 0 ≤ sin x :=
sin_nonneg_of_mem_Icc ⟨h0x, hxp⟩

lemma sin_neg_of_neg_of_neg_pi_lt {x : ℝ} (hx0 : x < 0) (hpx : -π < x) : sin x < 0 :=
neg_pos.1 $ sin_neg x ▸ sin_pos_of_pos_of_lt_pi (neg_pos.2 hx0) (neg_lt.1 hpx)

lemma sin_nonpos_of_nonnpos_of_neg_pi_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -π ≤ x) : sin x ≤ 0 :=
neg_nonneg.1 $ sin_neg x ▸ sin_nonneg_of_nonneg_of_le_pi (neg_nonneg.2 hx0) (neg_le.1 hpx)

@[simp] lemma sin_pi_div_two : sin (π / 2) = 1 :=
have sin (π / 2) = 1 ∨ sin (π / 2) = -1 :=
by simpa [sq, mul_self_eq_one_iff] using sin_sq_add_cos_sq (π / 2),
this.resolve_right
  (λ h, (show ¬(0 : ℝ) < -1, by norm_num) $
    h ▸ sin_pos_of_pos_of_lt_pi pi_div_two_pos (half_lt_self pi_pos))

lemma sin_add_pi_div_two (x : ℝ) : sin (x + π / 2) = cos x :=
by simp [sin_add]

lemma sin_sub_pi_div_two (x : ℝ) : sin (x - π / 2) = -cos x :=
by simp [sub_eq_add_neg, sin_add]

lemma sin_pi_div_two_sub (x : ℝ) : sin (π / 2 - x) = cos x :=
by simp [sub_eq_add_neg, sin_add]

lemma cos_add_pi_div_two (x : ℝ) : cos (x + π / 2) = -sin x :=
by simp [cos_add]

lemma cos_sub_pi_div_two (x : ℝ) : cos (x - π / 2) = sin x :=
by simp [sub_eq_add_neg, cos_add]

lemma cos_pi_div_two_sub (x : ℝ) : cos (π / 2 - x) = sin x :=
by rw [← cos_neg, neg_sub, cos_sub_pi_div_two]

lemma cos_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) : 0 < cos x :=
sin_add_pi_div_two x ▸ sin_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma cos_nonneg_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) : 0 ≤ cos x :=
sin_add_pi_div_two x ▸ sin_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma cos_nonneg_of_neg_pi_div_two_le_of_le {x : ℝ} (hl : -(π / 2) ≤ x) (hu : x ≤ π / 2) :
  0 ≤ cos x :=
cos_nonneg_of_mem_Icc ⟨hl, hu⟩

lemma cos_neg_of_pi_div_two_lt_of_lt {x : ℝ} (hx₁ : π / 2 < x) (hx₂ : x < π + π / 2) : cos x < 0 :=
neg_pos.1 $ cos_pi_sub x ▸ cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

lemma cos_nonpos_of_pi_div_two_le_of_le {x : ℝ} (hx₁ : π / 2 ≤ x) (hx₂ : x ≤ π + π / 2) :
  cos x ≤ 0 :=
neg_nonneg.1 $ cos_pi_sub x ▸ cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩

lemma sin_eq_sqrt_one_sub_cos_sq {x : ℝ} (hl : 0 ≤ x) (hu : x ≤ π) :
  sin x = sqrt (1 - cos x ^ 2) :=
by rw [← abs_sin_eq_sqrt_one_sub_cos_sq, abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi hl hu)]

lemma cos_eq_sqrt_one_sub_sin_sq {x : ℝ} (hl : -(π / 2) ≤ x) (hu : x ≤ π / 2) :
  cos x = sqrt (1 - sin x ^ 2) :=
by rw [← abs_cos_eq_sqrt_one_sub_sin_sq, abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨hl, hu⟩)]

lemma sin_eq_zero_iff_of_lt_of_lt {x : ℝ} (hx₁ : -π < x) (hx₂ : x < π) :
  sin x = 0 ↔ x = 0 :=
⟨λ h, le_antisymm
    (le_of_not_gt (λ h0, lt_irrefl (0 : ℝ) $
      calc 0 < sin x : sin_pos_of_pos_of_lt_pi h0 hx₂
        ... = 0 : h))
    (le_of_not_gt (λ h0, lt_irrefl (0 : ℝ) $
      calc 0 = sin x : h.symm
        ... < 0 : sin_neg_of_neg_of_neg_pi_lt h0 hx₁)),
  λ h, by simp [h]⟩

lemma sin_eq_zero_iff {x : ℝ} : sin x = 0 ↔ ∃ n : ℤ, (n : ℝ) * π = x :=
⟨λ h, ⟨⌊x / π⌋, le_antisymm (sub_nonneg.1 (sub_floor_div_mul_nonneg _ pi_pos))
  (sub_nonpos.1 $ le_of_not_gt $ λ h₃,
    (sin_pos_of_pos_of_lt_pi h₃ (sub_floor_div_mul_lt _ pi_pos)).ne
    (by simp [sub_eq_add_neg, sin_add, h, sin_int_mul_pi]))⟩,
  λ ⟨n, hn⟩, hn ▸ sin_int_mul_pi _⟩

lemma sin_ne_zero_iff {x : ℝ} : sin x ≠ 0 ↔ ∀ n : ℤ, (n : ℝ) * π ≠ x :=
by rw [← not_exists, not_iff_not, sin_eq_zero_iff]

lemma sin_eq_zero_iff_cos_eq {x : ℝ} : sin x = 0 ↔ cos x = 1 ∨ cos x = -1 :=
by rw [← mul_self_eq_one_iff, ← sin_sq_add_cos_sq x,
    sq, sq, ← sub_eq_iff_eq_add, sub_self];
  exact ⟨λ h, by rw [h, mul_zero], eq_zero_of_mul_self_eq_zero ∘ eq.symm⟩

lemma cos_eq_one_iff (x : ℝ) : cos x = 1 ↔ ∃ n : ℤ, (n : ℝ) * (2 * π) = x :=
⟨λ h, let ⟨n, hn⟩ := sin_eq_zero_iff.1 (sin_eq_zero_iff_cos_eq.2 (or.inl h)) in
    ⟨n / 2, (int.mod_two_eq_zero_or_one n).elim
      (λ hn0, by rwa [← mul_assoc, ← @int.cast_two ℝ, ← int.cast_mul, int.div_mul_cancel
        ((int.dvd_iff_mod_eq_zero _ _).2 hn0)])
      (λ hn1, by rw [← int.mod_add_div n 2, hn1, int.cast_add, int.cast_one, add_mul,
          one_mul, add_comm, mul_comm (2 : ℤ), int.cast_mul, mul_assoc, int.cast_two] at hn;
        rw [← hn, cos_int_mul_two_pi_add_pi] at h;
        exact absurd h (by norm_num))⟩,
  λ ⟨n, hn⟩, hn ▸ cos_int_mul_two_pi _⟩

lemma cos_eq_one_iff_of_lt_of_lt {x : ℝ} (hx₁ : -(2 * π) < x) (hx₂ : x < 2 * π) :
  cos x = 1 ↔ x = 0 :=
⟨λ h,
    begin
      rcases (cos_eq_one_iff _).1 h with ⟨n, rfl⟩,
      rw [mul_lt_iff_lt_one_left two_pi_pos] at hx₂,
      rw [neg_lt, neg_mul_eq_neg_mul, mul_lt_iff_lt_one_left two_pi_pos] at hx₁,
      norm_cast at hx₁ hx₂,
      obtain rfl : n = 0 := le_antisymm (by linarith) (by linarith),
      simp
    end,
  λ h, by simp [h]⟩

lemma cos_lt_cos_of_nonneg_of_le_pi_div_two {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π / 2)
  (hxy : x < y) :
  cos y < cos x :=
begin
  rw [← sub_lt_zero, cos_sub_cos],
  have : 0 < sin ((y + x) / 2),
  { refine sin_pos_of_pos_of_lt_pi _ _; linarith },
  have : 0 < sin ((y - x) / 2),
  { refine sin_pos_of_pos_of_lt_pi _ _; linarith },
  nlinarith,
end

lemma cos_lt_cos_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π) (hxy : x < y) :
  cos y < cos x :=
match (le_total x (π / 2) : x ≤ π / 2 ∨ π / 2 ≤ x), le_total y (π / 2) with
| or.inl hx, or.inl hy := cos_lt_cos_of_nonneg_of_le_pi_div_two hx₁ hy hxy
| or.inl hx, or.inr hy := (lt_or_eq_of_le hx).elim
  (λ hx, calc cos y ≤ 0 : cos_nonpos_of_pi_div_two_le_of_le hy (by linarith [pi_pos])
    ... < cos x : cos_pos_of_mem_Ioo ⟨by linarith, hx⟩)
  (λ hx, calc cos y < 0 : cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [pi_pos])
    ... = cos x : by rw [hx, cos_pi_div_two])
| or.inr hx, or.inl hy := by linarith
| or.inr hx, or.inr hy := neg_lt_neg_iff.1 (by rw [← cos_pi_sub, ← cos_pi_sub];
  apply cos_lt_cos_of_nonneg_of_le_pi_div_two; linarith)
end

lemma strict_anti_on_cos : strict_anti_on cos (Icc 0 π) :=
λ x hx y hy hxy, cos_lt_cos_of_nonneg_of_le_pi hx.1 hy.2 hxy

lemma cos_le_cos_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π) (hxy : x ≤ y) :
  cos y ≤ cos x :=
(strict_anti_on_cos.le_iff_le ⟨hx₁.trans hxy, hy₂⟩ ⟨hx₁, hxy.trans hy₂⟩).2 hxy

lemma sin_lt_sin_of_lt_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x)
  (hy₂ : y ≤ π / 2) (hxy : x < y) : sin x < sin y :=
by rw [← cos_sub_pi_div_two, ← cos_sub_pi_div_two, ← cos_neg (x - _), ← cos_neg (y - _)];
  apply cos_lt_cos_of_nonneg_of_le_pi; linarith

lemma strict_mono_on_sin : strict_mono_on sin (Icc (-(π / 2)) (π / 2)) :=
λ x hx y hy hxy, sin_lt_sin_of_lt_of_le_pi_div_two hx.1 hy.2 hxy

lemma sin_le_sin_of_le_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x)
  (hy₂ : y ≤ π / 2) (hxy : x ≤ y) : sin x ≤ sin y :=
(strict_mono_on_sin.le_iff_le ⟨hx₁, hxy.trans hy₂⟩ ⟨hx₁.trans hxy, hy₂⟩).2 hxy

lemma inj_on_sin : inj_on sin (Icc (-(π / 2)) (π / 2)) :=
strict_mono_on_sin.inj_on

lemma inj_on_cos : inj_on cos (Icc 0 π) := strict_anti_on_cos.inj_on

lemma surj_on_sin : surj_on sin (Icc (-(π / 2)) (π / 2)) (Icc (-1) 1) :=
by simpa only [sin_neg, sin_pi_div_two]
  using intermediate_value_Icc (neg_le_self pi_div_two_pos.le) continuous_sin.continuous_on

lemma surj_on_cos : surj_on cos (Icc 0 π) (Icc (-1) 1) :=
by simpa only [cos_zero, cos_pi]
  using intermediate_value_Icc' pi_pos.le continuous_cos.continuous_on

lemma sin_mem_Icc (x : ℝ) : sin x ∈ Icc (-1 : ℝ) 1 := ⟨neg_one_le_sin x, sin_le_one x⟩

lemma cos_mem_Icc (x : ℝ) : cos x ∈ Icc (-1 : ℝ) 1 := ⟨neg_one_le_cos x, cos_le_one x⟩

lemma maps_to_sin (s : set ℝ) : maps_to sin s (Icc (-1 : ℝ) 1) := λ x _, sin_mem_Icc x

lemma maps_to_cos (s : set ℝ) : maps_to cos s (Icc (-1 : ℝ) 1) := λ x _, cos_mem_Icc x

lemma bij_on_sin : bij_on sin (Icc (-(π / 2)) (π / 2)) (Icc (-1) 1) :=
⟨maps_to_sin _, inj_on_sin, surj_on_sin⟩

lemma bij_on_cos : bij_on cos (Icc 0 π) (Icc (-1) 1) :=
⟨maps_to_cos _, inj_on_cos, surj_on_cos⟩

@[simp] lemma range_cos : range cos = (Icc (-1) 1 : set ℝ) :=
subset.antisymm (range_subset_iff.2 cos_mem_Icc) surj_on_cos.subset_range

@[simp] lemma range_sin : range sin = (Icc (-1) 1 : set ℝ) :=
subset.antisymm (range_subset_iff.2 sin_mem_Icc) surj_on_sin.subset_range

lemma range_cos_infinite : (range real.cos).infinite :=
by { rw real.range_cos, exact Icc.infinite (by norm_num) }

lemma range_sin_infinite : (range real.sin).infinite :=
by { rw real.range_sin, exact Icc.infinite (by norm_num) }

lemma sin_lt {x : ℝ} (h : 0 < x) : sin x < x :=
begin
  cases le_or_gt x 1 with h' h',
  { have hx : |x| = x := abs_of_nonneg (le_of_lt h),
    have : |x| ≤ 1, rwa [hx],
    have := sin_bound this, rw [abs_le] at this,
    have := this.2, rw [sub_le_iff_le_add', hx] at this,
    apply lt_of_le_of_lt this, rw [sub_add], apply lt_of_lt_of_le _ (le_of_eq (sub_zero x)),
    apply sub_lt_sub_left, rw [sub_pos, div_eq_mul_inv (x ^ 3)], apply mul_lt_mul',
    { rw [pow_succ x 3], refine le_trans _ (le_of_eq (one_mul _)),
      rw mul_le_mul_right, exact h', apply pow_pos h },
    norm_num, norm_num, apply pow_pos h },
  exact lt_of_le_of_lt (sin_le_one x) h'
end

/- note 1: this inequality is not tight, the tighter inequality is sin x > x - x ^ 3 / 6.
   note 2: this is also true for x > 1, but it's nontrivial for x just above 1. -/
lemma sin_gt_sub_cube {x : ℝ} (h : 0 < x) (h' : x ≤ 1) : x - x ^ 3 / 4 < sin x :=
begin
  have hx : |x| = x := abs_of_nonneg (le_of_lt h),
  have : |x| ≤ 1, rwa [hx],
  have := sin_bound this, rw [abs_le] at this,
  have := this.1, rw [le_sub_iff_add_le, hx] at this,
  refine lt_of_lt_of_le _ this,
  rw [add_comm, sub_add, sub_neg_eq_add], apply sub_lt_sub_left,
  apply add_lt_of_lt_sub_left,
  rw (show x ^ 3 / 4 - x ^ 3 / 6 = x ^ 3 * 12⁻¹,
    by simp [div_eq_mul_inv, ← mul_sub]; norm_num),
  apply mul_lt_mul',
  { rw [pow_succ x 3], refine le_trans _ (le_of_eq (one_mul _)),
    rw mul_le_mul_right, exact h', apply pow_pos h },
  norm_num, norm_num, apply pow_pos h
end

section cos_div_sq

variable (x : ℝ)

/-- the series `sqrt_two_add_series x n` is `sqrt(2 + sqrt(2 + ... ))` with `n` square roots,
  starting with `x`. We define it here because `cos (pi / 2 ^ (n+1)) = sqrt_two_add_series 0 n / 2`
-/
@[simp, pp_nodot] noncomputable def sqrt_two_add_series (x : ℝ) : ℕ → ℝ
| 0     := x
| (n+1) := sqrt (2 + sqrt_two_add_series n)

lemma sqrt_two_add_series_zero : sqrt_two_add_series x 0 = x := by simp
lemma sqrt_two_add_series_one : sqrt_two_add_series 0 1 = sqrt 2 := by simp
lemma sqrt_two_add_series_two : sqrt_two_add_series 0 2 = sqrt (2 + sqrt 2) := by simp

lemma sqrt_two_add_series_zero_nonneg : ∀(n : ℕ), 0 ≤ sqrt_two_add_series 0 n
| 0     := le_refl 0
| (n+1) := sqrt_nonneg _

lemma sqrt_two_add_series_nonneg {x : ℝ} (h : 0 ≤ x) : ∀(n : ℕ), 0 ≤ sqrt_two_add_series x n
| 0     := h
| (n+1) := sqrt_nonneg _

lemma sqrt_two_add_series_lt_two : ∀(n : ℕ), sqrt_two_add_series 0 n < 2
| 0     := by norm_num
| (n+1) :=
  begin
    refine lt_of_lt_of_le _ (sqrt_sq zero_lt_two.le).le,
    rw [sqrt_two_add_series, sqrt_lt_sqrt_iff, ← lt_sub_iff_add_lt'],
    { refine (sqrt_two_add_series_lt_two n).trans_le _, norm_num },
    { exact add_nonneg zero_le_two (sqrt_two_add_series_zero_nonneg n) }
  end

lemma sqrt_two_add_series_succ (x : ℝ) :
  ∀(n : ℕ), sqrt_two_add_series x (n+1) = sqrt_two_add_series (sqrt (2 + x)) n
| 0     := rfl
| (n+1) := by rw [sqrt_two_add_series, sqrt_two_add_series_succ, sqrt_two_add_series]

lemma sqrt_two_add_series_monotone_left {x y : ℝ} (h : x ≤ y) :
  ∀(n : ℕ), sqrt_two_add_series x n ≤ sqrt_two_add_series y n
| 0     := h
| (n+1) :=
  begin
    rw [sqrt_two_add_series, sqrt_two_add_series],
    exact sqrt_le_sqrt (add_le_add_left (sqrt_two_add_series_monotone_left _) _)
  end

@[simp] lemma cos_pi_over_two_pow : ∀(n : ℕ), cos (π / 2 ^ (n+1)) = sqrt_two_add_series 0 n / 2
| 0     := by simp
| (n+1) :=
  begin
    have : (2 : ℝ) ≠ 0 := two_ne_zero,
    symmetry, rw [div_eq_iff_mul_eq this], symmetry,
    rw [sqrt_two_add_series, sqrt_eq_iff_sq_eq, mul_pow, cos_sq, ←mul_div_assoc,
      nat.add_succ, pow_succ, mul_div_mul_left _ _ this, cos_pi_over_two_pow, add_mul],
    congr, { norm_num },
    rw [mul_comm, sq, mul_assoc, ←mul_div_assoc, mul_div_cancel_left, ←mul_div_assoc,
        mul_div_cancel_left]; try { exact this },
    apply add_nonneg, norm_num, apply sqrt_two_add_series_zero_nonneg, norm_num,
    apply le_of_lt, apply cos_pos_of_mem_Ioo ⟨_, _⟩,
    { transitivity (0 : ℝ), rw neg_lt_zero, apply pi_div_two_pos,
      apply div_pos pi_pos, apply pow_pos, norm_num },
    apply div_lt_div' (le_refl π) _ pi_pos _,
    refine lt_of_le_of_lt (le_of_eq (pow_one _).symm) _,
    apply pow_lt_pow, norm_num, apply nat.succ_lt_succ, apply nat.succ_pos, all_goals {norm_num}
  end

lemma sin_sq_pi_over_two_pow (n : ℕ) :
  sin (π / 2 ^ (n+1)) ^ 2 = 1 - (sqrt_two_add_series 0 n / 2) ^ 2 :=
by rw [sin_sq, cos_pi_over_two_pow]

lemma sin_sq_pi_over_two_pow_succ (n : ℕ) :
  sin (π / 2 ^ (n+2)) ^ 2 = 1 / 2 - sqrt_two_add_series 0 n / 4 :=
begin
  rw [sin_sq_pi_over_two_pow, sqrt_two_add_series, div_pow, sq_sqrt, add_div, ←sub_sub],
  congr, norm_num, norm_num, apply add_nonneg, norm_num, apply sqrt_two_add_series_zero_nonneg,
end

@[simp] lemma sin_pi_over_two_pow_succ (n : ℕ) :
  sin (π / 2 ^ (n+2)) = sqrt (2 - sqrt_two_add_series 0 n) / 2 :=
begin
  symmetry, rw [div_eq_iff_mul_eq], symmetry,
  rw [sqrt_eq_iff_sq_eq, mul_pow, sin_sq_pi_over_two_pow_succ, sub_mul],
  { congr, norm_num, rw [mul_comm], convert mul_div_cancel' _ _, norm_num, norm_num },
  { rw [sub_nonneg], apply le_of_lt, apply sqrt_two_add_series_lt_two },
  apply le_of_lt, apply mul_pos, apply sin_pos_of_pos_of_lt_pi,
  { apply div_pos pi_pos, apply pow_pos, norm_num },
  refine lt_of_lt_of_le _ (le_of_eq (div_one _)), rw [div_lt_div_left],
  refine lt_of_le_of_lt (le_of_eq (pow_zero 2).symm) _,
  apply pow_lt_pow, norm_num, apply nat.succ_pos, apply pi_pos,
  apply pow_pos, all_goals {norm_num}
end

@[simp] lemma cos_pi_div_four : cos (π / 4) = sqrt 2 / 2 :=
by { transitivity cos (π / 2 ^ 2), congr, norm_num, simp }

@[simp] lemma sin_pi_div_four : sin (π / 4) = sqrt 2 / 2 :=
by { transitivity sin (π / 2 ^ 2), congr, norm_num, simp }

@[simp] lemma cos_pi_div_eight : cos (π / 8) = sqrt (2 + sqrt 2) / 2 :=
by { transitivity cos (π / 2 ^ 3), congr, norm_num, simp }

@[simp] lemma sin_pi_div_eight : sin (π / 8) = sqrt (2 - sqrt 2) / 2 :=
by { transitivity sin (π / 2 ^ 3), congr, norm_num, simp }

@[simp] lemma cos_pi_div_sixteen : cos (π / 16) = sqrt (2 + sqrt (2 + sqrt 2)) / 2 :=
by { transitivity cos (π / 2 ^ 4), congr, norm_num, simp }

@[simp] lemma sin_pi_div_sixteen : sin (π / 16) = sqrt (2 - sqrt (2 + sqrt 2)) / 2 :=
by { transitivity sin (π / 2 ^ 4), congr, norm_num, simp }

@[simp] lemma cos_pi_div_thirty_two : cos (π / 32) = sqrt (2 + sqrt (2 + sqrt (2 + sqrt 2))) / 2 :=
by { transitivity cos (π / 2 ^ 5), congr, norm_num, simp }

@[simp] lemma sin_pi_div_thirty_two : sin (π / 32) = sqrt (2 - sqrt (2 + sqrt (2 + sqrt 2))) / 2 :=
by { transitivity sin (π / 2 ^ 5), congr, norm_num, simp }

-- This section is also a convenient location for other explicit values of `sin` and `cos`.

/-- The cosine of `π / 3` is `1 / 2`. -/
@[simp] lemma cos_pi_div_three : cos (π / 3) = 1 / 2 :=
begin
  have h₁ : (2 * cos (π / 3) - 1) ^ 2 * (2 * cos (π / 3) + 2) = 0,
  { have : cos (3 * (π / 3)) = cos π := by { congr' 1, ring },
    linarith [cos_pi, cos_three_mul (π / 3)] },
  cases mul_eq_zero.mp h₁ with h h,
  { linarith [pow_eq_zero h] },
  { have : cos π < cos (π / 3),
    { refine cos_lt_cos_of_nonneg_of_le_pi _ rfl.ge _;
      linarith [pi_pos] },
    linarith [cos_pi] }
end

/-- The square of the cosine of `π / 6` is `3 / 4` (this is sometimes more convenient than the
result for cosine itself). -/
lemma sq_cos_pi_div_six : cos (π / 6) ^ 2 = 3 / 4 :=
begin
  have h1 : cos (π / 6) ^ 2 = 1 / 2 + 1 / 2 / 2,
  { convert cos_sq (π / 6),
    have h2 : 2 * (π / 6) = π / 3 := by cancel_denoms,
    rw [h2, cos_pi_div_three] },
  rw ← sub_eq_zero at h1 ⊢,
  convert h1 using 1,
  ring
end

/-- The cosine of `π / 6` is `√3 / 2`. -/
@[simp] lemma cos_pi_div_six : cos (π / 6) = (sqrt 3) / 2 :=
begin
  suffices : sqrt 3 = cos (π / 6) * 2,
  { field_simp [(by norm_num : 0 ≠ 2)], exact this.symm },
  rw sqrt_eq_iff_sq_eq,
  { have h1 := (mul_right_inj' (by norm_num : (4:ℝ) ≠ 0)).mpr sq_cos_pi_div_six,
    rw ← sub_eq_zero at h1 ⊢,
    convert h1 using 1,
    ring },
  { norm_num },
  { have : 0 < cos (π / 6) := by { apply cos_pos_of_mem_Ioo; split; linarith [pi_pos] },
    linarith },
end

/-- The sine of `π / 6` is `1 / 2`. -/
@[simp] lemma sin_pi_div_six : sin (π / 6) = 1 / 2 :=
begin
  rw [← cos_pi_div_two_sub, ← cos_pi_div_three],
  congr,
  ring
end

/-- The square of the sine of `π / 3` is `3 / 4` (this is sometimes more convenient than the
result for cosine itself). -/
lemma sq_sin_pi_div_three : sin (π / 3) ^ 2 = 3 / 4 :=
begin
  rw [← cos_pi_div_two_sub, ← sq_cos_pi_div_six],
  congr,
  ring
end

/-- The sine of `π / 3` is `√3 / 2`. -/
@[simp] lemma sin_pi_div_three : sin (π / 3) = (sqrt 3) / 2 :=
begin
  rw [← cos_pi_div_two_sub, ← cos_pi_div_six],
  congr,
  ring
end

end cos_div_sq

/-- `real.sin` as an `order_iso` between `[-(π / 2), π / 2]` and `[-1, 1]`. -/
def sin_order_iso : Icc (-(π / 2)) (π / 2) ≃o Icc (-1:ℝ) 1 :=
(strict_mono_on_sin.order_iso _ _).trans $ order_iso.set_congr _ _ bij_on_sin.image_eq

@[simp] lemma coe_sin_order_iso_apply (x : Icc (-(π / 2)) (π / 2)) :
  (sin_order_iso x : ℝ) = sin x := rfl

lemma sin_order_iso_apply (x : Icc (-(π / 2)) (π / 2)) :
  sin_order_iso x = ⟨sin x, sin_mem_Icc x⟩ := rfl

@[simp] lemma tan_pi_div_four : tan (π / 4) = 1 :=
begin
  rw [tan_eq_sin_div_cos, cos_pi_div_four, sin_pi_div_four],
  have h : (sqrt 2) / 2 > 0 := by cancel_denoms,
  exact div_self (ne_of_gt h),
end

@[simp] lemma tan_pi_div_two : tan (π / 2) = 0 := by simp [tan_eq_sin_div_cos]

lemma tan_pos_of_pos_of_lt_pi_div_two {x : ℝ} (h0x : 0 < x) (hxp : x < π / 2) : 0 < tan x :=
by rw tan_eq_sin_div_cos; exact div_pos (sin_pos_of_pos_of_lt_pi h0x (by linarith))
  (cos_pos_of_mem_Ioo ⟨by linarith, hxp⟩)

lemma tan_nonneg_of_nonneg_of_le_pi_div_two {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ π / 2) : 0 ≤ tan x :=
match lt_or_eq_of_le h0x, lt_or_eq_of_le hxp with
| or.inl hx0, or.inl hxp := le_of_lt (tan_pos_of_pos_of_lt_pi_div_two hx0 hxp)
| or.inl hx0, or.inr hxp := by simp [hxp, tan_eq_sin_div_cos]
| or.inr hx0, _          := by simp [hx0.symm]
end

lemma tan_neg_of_neg_of_pi_div_two_lt {x : ℝ} (hx0 : x < 0) (hpx : -(π / 2) < x) : tan x < 0 :=
neg_pos.1 (tan_neg x ▸ tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith [pi_pos]))

lemma tan_nonpos_of_nonpos_of_neg_pi_div_two_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -(π / 2) ≤ x) :
  tan x ≤ 0 :=
neg_nonneg.1 (tan_neg x ▸ tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith))

lemma tan_lt_tan_of_nonneg_of_lt_pi_div_two {x y : ℝ}
  (hx₁ : 0 ≤ x) (hy₂ : y < π / 2) (hxy : x < y) :
  tan x < tan y :=
begin
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos],
  exact div_lt_div
    (sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (le_of_lt hy₂) hxy)
    (cos_le_cos_of_nonneg_of_le_pi hx₁ (by linarith) (le_of_lt hxy))
    (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
    (cos_pos_of_mem_Ioo ⟨by linarith, hy₂⟩)
end

lemma tan_lt_tan_of_lt_of_lt_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) < x)
 (hy₂ : y < π / 2) (hxy : x < y) : tan x < tan y :=
match le_total x 0, le_total y 0 with
| or.inl hx0, or.inl hy0 := neg_lt_neg_iff.1 $ by rw [← tan_neg, ← tan_neg]; exact
  tan_lt_tan_of_nonneg_of_lt_pi_div_two (neg_nonneg.2 hy0)
    (neg_lt.2 hx₁) (neg_lt_neg hxy)
| or.inl hx0, or.inr hy0 := (lt_or_eq_of_le hy0).elim
  (λ hy0, calc tan x ≤ 0 : tan_nonpos_of_nonpos_of_neg_pi_div_two_le hx0 (le_of_lt hx₁)
    ... < tan y : tan_pos_of_pos_of_lt_pi_div_two hy0 hy₂)
  (λ hy0, by rw [← hy0, tan_zero]; exact
    tan_neg_of_neg_of_pi_div_two_lt (hy0.symm ▸ hxy) hx₁)
| or.inr hx0, or.inl hy0 := by linarith
| or.inr hx0, or.inr hy0 := tan_lt_tan_of_nonneg_of_lt_pi_div_two hx0 hy₂ hxy
end

lemma strict_mono_on_tan : strict_mono_on tan (Ioo (-(π / 2)) (π / 2)) :=
λ x hx y hy, tan_lt_tan_of_lt_of_lt_pi_div_two hx.1 hy.2

lemma inj_on_tan : inj_on tan (Ioo (-(π / 2)) (π / 2)) :=
strict_mono_on_tan.inj_on

lemma tan_inj_of_lt_of_lt_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2)
  (hy₁ : -(π / 2) < y) (hy₂ : y < π / 2) (hxy : tan x = tan y) : x = y :=
inj_on_tan ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩ hxy

lemma tan_periodic : function.periodic tan π :=
by simpa only [function.periodic, tan_eq_sin_div_cos] using sin_antiperiodic.div cos_antiperiodic

lemma tan_add_pi (x : ℝ) : tan (x + π) = tan x :=
tan_periodic x

lemma tan_sub_pi (x : ℝ) : tan (x - π) = tan x :=
tan_periodic.sub_eq x

lemma tan_pi_sub (x : ℝ) : tan (π - x) = -tan x :=
tan_neg x ▸ tan_periodic.sub_eq'

lemma tan_nat_mul_pi (n : ℕ) : tan (n * π) = 0 :=
tan_zero ▸ tan_periodic.nat_mul_eq n

lemma tan_int_mul_pi (n : ℤ) : tan (n * π) = 0 :=
tan_zero ▸ tan_periodic.int_mul_eq n

lemma tan_add_nat_mul_pi (x : ℝ) (n : ℕ) : tan (x + n * π) = tan x :=
tan_periodic.nat_mul n x

lemma tan_add_int_mul_pi (x : ℝ) (n : ℤ) : tan (x + n * π) = tan x :=
tan_periodic.int_mul n x

lemma tan_sub_nat_mul_pi (x : ℝ) (n : ℕ) : tan (x - n * π) = tan x :=
tan_periodic.sub_nat_mul_eq n

lemma tan_sub_int_mul_pi (x : ℝ) (n : ℤ) : tan (x - n * π) = tan x :=
tan_periodic.sub_int_mul_eq n

lemma tan_nat_mul_pi_sub (x : ℝ) (n : ℕ) : tan (n * π - x) = -tan x :=
tan_neg x ▸ tan_periodic.nat_mul_sub_eq n

lemma tan_int_mul_pi_sub (x : ℝ) (n : ℤ) : tan (n * π - x) = -tan x :=
tan_neg x ▸ tan_periodic.int_mul_sub_eq n


lemma tendsto_sin_pi_div_two : tendsto sin (𝓝[Iio (π/2)] (π/2)) (𝓝 1) :=
by { convert continuous_sin.continuous_within_at, simp }

lemma tendsto_cos_pi_div_two : tendsto cos (𝓝[Iio (π/2)] (π/2)) (𝓝[Ioi 0] 0) :=
begin
  apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within,
  { convert continuous_cos.continuous_within_at, simp },
  { filter_upwards [Ioo_mem_nhds_within_Iio (right_mem_Ioc.mpr (norm_num.lt_neg_pos
      _ _ pi_div_two_pos pi_div_two_pos))] λ x hx, cos_pos_of_mem_Ioo hx },
end

lemma tendsto_tan_pi_div_two : tendsto tan (𝓝[Iio (π/2)] (π/2)) at_top :=
begin
  convert tendsto_cos_pi_div_two.inv_tendsto_zero.at_top_mul zero_lt_one
            tendsto_sin_pi_div_two,
  simp only [pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]
end

lemma tendsto_sin_neg_pi_div_two : tendsto sin (𝓝[Ioi (-(π/2))] (-(π/2))) (𝓝 (-1)) :=
by { convert continuous_sin.continuous_within_at, simp }

lemma tendsto_cos_neg_pi_div_two : tendsto cos (𝓝[Ioi (-(π/2))] (-(π/2))) (𝓝[Ioi 0] 0) :=
begin
  apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within,
  { convert continuous_cos.continuous_within_at, simp },
  { filter_upwards [Ioo_mem_nhds_within_Ioi (left_mem_Ico.mpr (norm_num.lt_neg_pos
      _ _ pi_div_two_pos pi_div_two_pos))] λ x hx, cos_pos_of_mem_Ioo hx },
end

lemma tendsto_tan_neg_pi_div_two : tendsto tan (𝓝[Ioi (-(π/2))] (-(π/2))) at_bot :=
begin
  convert tendsto_cos_neg_pi_div_two.inv_tendsto_zero.at_top_mul_neg (by norm_num)
            tendsto_sin_neg_pi_div_two,
  simp only [pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]
end

end real

namespace complex

open_locale real

lemma sin_eq_zero_iff_cos_eq {z : ℂ} : sin z = 0 ↔ cos z = 1 ∨ cos z = -1 :=
by rw [← mul_self_eq_one_iff, ← sin_sq_add_cos_sq, sq, sq, ← sub_eq_iff_eq_add, sub_self];
  exact ⟨λ h, by rw [h, mul_zero], eq_zero_of_mul_self_eq_zero ∘ eq.symm⟩

@[simp] lemma cos_pi_div_two : cos (π / 2) = 0 :=
calc cos (π / 2) = real.cos (π / 2) : by rw [of_real_cos]; simp
... = 0 : by simp

@[simp] lemma sin_pi_div_two : sin (π / 2) = 1 :=
calc sin (π / 2) = real.sin (π / 2) : by rw [of_real_sin]; simp
... = 1 : by simp

@[simp] lemma sin_pi : sin π = 0 :=
by rw [← of_real_sin, real.sin_pi]; simp

@[simp] lemma cos_pi : cos π = -1 :=
by rw [← of_real_cos, real.cos_pi]; simp

@[simp] lemma sin_two_pi : sin (2 * π) = 0 :=
by simp [two_mul, sin_add]

@[simp] lemma cos_two_pi : cos (2 * π) = 1 :=
by simp [two_mul, cos_add]

lemma sin_antiperiodic : function.antiperiodic sin π :=
by simp [sin_add]

lemma sin_periodic : function.periodic sin (2 * π) :=
sin_antiperiodic.periodic

lemma sin_add_pi (x : ℂ) : sin (x + π) = -sin x :=
sin_antiperiodic x

lemma sin_add_two_pi (x : ℂ) : sin (x + 2 * π) = sin x :=
sin_periodic x

lemma sin_sub_pi (x : ℂ) : sin (x - π) = -sin x :=
sin_antiperiodic.sub_eq x

lemma sin_sub_two_pi (x : ℂ) : sin (x - 2 * π) = sin x :=
sin_periodic.sub_eq x

lemma sin_pi_sub (x : ℂ) : sin (π - x) = sin x :=
neg_neg (sin x) ▸ sin_neg x ▸ sin_antiperiodic.sub_eq'

lemma sin_two_pi_sub (x : ℂ) : sin (2 * π - x) = -sin x :=
sin_neg x ▸ sin_periodic.sub_eq'

lemma sin_nat_mul_pi (n : ℕ) : sin (n * π) = 0 :=
sin_antiperiodic.nat_mul_eq_of_eq_zero sin_zero n

lemma sin_int_mul_pi (n : ℤ) : sin (n * π) = 0 :=
sin_antiperiodic.int_mul_eq_of_eq_zero sin_zero n

lemma sin_add_nat_mul_two_pi (x : ℂ) (n : ℕ) : sin (x + n * (2 * π)) = sin x :=
sin_periodic.nat_mul n x

lemma sin_add_int_mul_two_pi (x : ℂ) (n : ℤ) : sin (x + n * (2 * π)) = sin x :=
sin_periodic.int_mul n x

lemma sin_sub_nat_mul_two_pi (x : ℂ) (n : ℕ) : sin (x - n * (2 * π)) = sin x :=
sin_periodic.sub_nat_mul_eq n

lemma sin_sub_int_mul_two_pi (x : ℂ) (n : ℤ) : sin (x - n * (2 * π)) = sin x :=
sin_periodic.sub_int_mul_eq n

lemma sin_nat_mul_two_pi_sub (x : ℂ) (n : ℕ) : sin (n * (2 * π) - x) = -sin x :=
sin_neg x ▸ sin_periodic.nat_mul_sub_eq n

lemma sin_int_mul_two_pi_sub (x : ℂ) (n : ℤ) : sin (n * (2 * π) - x) = -sin x :=
sin_neg x ▸ sin_periodic.int_mul_sub_eq n

lemma cos_antiperiodic : function.antiperiodic cos π :=
by simp [cos_add]

lemma cos_periodic : function.periodic cos (2 * π) :=
cos_antiperiodic.periodic

lemma cos_add_pi (x : ℂ) : cos (x + π) = -cos x :=
cos_antiperiodic x

lemma cos_add_two_pi (x : ℂ) : cos (x + 2 * π) = cos x :=
cos_periodic x

lemma cos_sub_pi (x : ℂ) : cos (x - π) = -cos x :=
cos_antiperiodic.sub_eq x

lemma cos_sub_two_pi (x : ℂ) : cos (x - 2 * π) = cos x :=
cos_periodic.sub_eq x

lemma cos_pi_sub (x : ℂ) : cos (π - x) = -cos x :=
cos_neg x ▸ cos_antiperiodic.sub_eq'

lemma cos_two_pi_sub (x : ℂ) : cos (2 * π - x) = cos x :=
cos_neg x ▸ cos_periodic.sub_eq'

lemma cos_nat_mul_two_pi (n : ℕ) : cos (n * (2 * π)) = 1 :=
(cos_periodic.nat_mul_eq n).trans cos_zero

lemma cos_int_mul_two_pi (n : ℤ) : cos (n * (2 * π)) = 1 :=
(cos_periodic.int_mul_eq n).trans cos_zero

lemma cos_add_nat_mul_two_pi (x : ℂ) (n : ℕ) : cos (x + n * (2 * π)) = cos x :=
cos_periodic.nat_mul n x

lemma cos_add_int_mul_two_pi (x : ℂ) (n : ℤ) : cos (x + n * (2 * π)) = cos x :=
cos_periodic.int_mul n x

lemma cos_sub_nat_mul_two_pi (x : ℂ) (n : ℕ) : cos (x - n * (2 * π)) = cos x :=
cos_periodic.sub_nat_mul_eq n

lemma cos_sub_int_mul_two_pi (x : ℂ) (n : ℤ) : cos (x - n * (2 * π)) = cos x :=
cos_periodic.sub_int_mul_eq n

lemma cos_nat_mul_two_pi_sub (x : ℂ) (n : ℕ) : cos (n * (2 * π) - x) = cos x :=
cos_neg x ▸ cos_periodic.nat_mul_sub_eq n

lemma cos_int_mul_two_pi_sub (x : ℂ) (n : ℤ) : cos (n * (2 * π) - x) = cos x :=
cos_neg x ▸ cos_periodic.int_mul_sub_eq n

lemma cos_nat_mul_two_pi_add_pi (n : ℕ) : cos (n * (2 * π) + π) = -1 :=
by simpa only [cos_zero] using (cos_periodic.nat_mul n).add_antiperiod_eq cos_antiperiodic

lemma cos_int_mul_two_pi_add_pi (n : ℤ) : cos (n * (2 * π) + π) = -1 :=
by simpa only [cos_zero] using (cos_periodic.int_mul n).add_antiperiod_eq cos_antiperiodic

lemma cos_nat_mul_two_pi_sub_pi (n : ℕ) : cos (n * (2 * π) - π) = -1 :=
by simpa only [cos_zero] using (cos_periodic.nat_mul n).sub_antiperiod_eq cos_antiperiodic

lemma cos_int_mul_two_pi_sub_pi (n : ℤ) : cos (n * (2 * π) - π) = -1 :=
by simpa only [cos_zero] using (cos_periodic.int_mul n).sub_antiperiod_eq cos_antiperiodic

lemma sin_add_pi_div_two (x : ℂ) : sin (x + π / 2) = cos x :=
by simp [sin_add]

lemma sin_sub_pi_div_two (x : ℂ) : sin (x - π / 2) = -cos x :=
by simp [sub_eq_add_neg, sin_add]

lemma sin_pi_div_two_sub (x : ℂ) : sin (π / 2 - x) = cos x :=
by simp [sub_eq_add_neg, sin_add]

lemma cos_add_pi_div_two (x : ℂ) : cos (x + π / 2) = -sin x :=
by simp [cos_add]

lemma cos_sub_pi_div_two (x : ℂ) : cos (x - π / 2) = sin x :=
by simp [sub_eq_add_neg, cos_add]

lemma cos_pi_div_two_sub (x : ℂ) : cos (π / 2 - x) = sin x :=
by rw [← cos_neg, neg_sub, cos_sub_pi_div_two]

lemma tan_periodic : function.periodic tan π :=
by simpa only [tan_eq_sin_div_cos] using sin_antiperiodic.div cos_antiperiodic

lemma tan_add_pi (x : ℂ) : tan (x + π) = tan x :=
tan_periodic x

lemma tan_sub_pi (x : ℂ) : tan (x - π) = tan x :=
tan_periodic.sub_eq x

lemma tan_pi_sub (x : ℂ) : tan (π - x) = -tan x :=
tan_neg x ▸ tan_periodic.sub_eq'

lemma tan_nat_mul_pi (n : ℕ) : tan (n * π) = 0 :=
tan_zero ▸ tan_periodic.nat_mul_eq n

lemma tan_int_mul_pi (n : ℤ) : tan (n * π) = 0 :=
tan_zero ▸ tan_periodic.int_mul_eq n

lemma tan_add_nat_mul_pi (x : ℂ) (n : ℕ) : tan (x + n * π) = tan x :=
tan_periodic.nat_mul n x

lemma tan_add_int_mul_pi (x : ℂ) (n : ℤ) : tan (x + n * π) = tan x :=
tan_periodic.int_mul n x

lemma tan_sub_nat_mul_pi (x : ℂ) (n : ℕ) : tan (x - n * π) = tan x :=
tan_periodic.sub_nat_mul_eq n

lemma tan_sub_int_mul_pi (x : ℂ) (n : ℤ) : tan (x - n * π) = tan x :=
tan_periodic.sub_int_mul_eq n

lemma tan_nat_mul_pi_sub (x : ℂ) (n : ℕ) : tan (n * π - x) = -tan x :=
tan_neg x ▸ tan_periodic.nat_mul_sub_eq n

lemma tan_int_mul_pi_sub (x : ℂ) (n : ℤ) : tan (n * π - x) = -tan x :=
tan_neg x ▸ tan_periodic.int_mul_sub_eq n

lemma exp_antiperiodic : function.antiperiodic exp (π * I) :=
by simp [exp_add, exp_mul_I]

lemma exp_periodic : function.periodic exp (2 * π * I) :=
(mul_assoc (2:ℂ) π I).symm ▸ exp_antiperiodic.periodic

lemma exp_mul_I_antiperiodic : function.antiperiodic (λ x, exp (x * I)) π :=
by simpa only [mul_inv_cancel_right₀ I_ne_zero] using exp_antiperiodic.mul_const I_ne_zero

lemma exp_mul_I_periodic : function.periodic (λ x, exp (x * I)) (2 * π) :=
exp_mul_I_antiperiodic.periodic

lemma exp_pi_mul_I : exp (π * I) = -1 :=
exp_zero ▸ exp_antiperiodic.eq

lemma exp_two_pi_mul_I : exp (2 * π * I) = 1 :=
exp_periodic.eq.trans exp_zero

lemma exp_nat_mul_two_pi_mul_I (n : ℕ) : exp (n * (2 * π * I)) = 1 :=
(exp_periodic.nat_mul_eq n).trans exp_zero

lemma exp_int_mul_two_pi_mul_I (n : ℤ) : exp (n * (2 * π * I)) = 1 :=
(exp_periodic.int_mul_eq n).trans exp_zero

end complex
