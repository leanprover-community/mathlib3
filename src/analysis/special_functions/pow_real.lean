/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
import analysis.special_functions.pow_complex

/-! # Power function on `ℝ`

We construct the power functions `x ^ y`, where `x` and `y` are real numbers.
-/

noncomputable theory

open_locale classical real big_operators complex_conjugate
open finset set

/-
## Definitions
-/

namespace real

/-- The real power function `x ^ y`, defined as the real part of the complex power function.
For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`, one sets `0 ^ 0=1` and `0 ^ y=0` for
`y ≠ 0`. For `x < 0`, the definition is somewhat arbitary as it depends on the choice of a complex
determination of the logarithm. With our conventions, it is equal to `exp (y log x) cos (π y)`. -/
noncomputable def rpow (x y : ℝ) := ((x : ℂ) ^ (y : ℂ)).re

noncomputable instance : has_pow ℝ ℝ := ⟨rpow⟩

@[simp] lemma rpow_eq_pow (x y : ℝ) : rpow x y = x ^ y := rfl

lemma rpow_def (x y : ℝ) : x ^ y = ((x : ℂ) ^ (y : ℂ)).re := rfl

lemma rpow_def_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ y =
  if x = 0
    then if y = 0
      then 1
      else 0
    else exp (log x * y) :=
by simp only [rpow_def, complex.cpow_def];
  split_ifs;
  simp [*, (complex.of_real_log hx).symm, -complex.of_real_mul, -is_R_or_C.of_real_mul,
    (complex.of_real_mul _ _).symm, complex.exp_of_real_re] at *

lemma rpow_def_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : x ^ y = exp (log x * y) :=
by rw [rpow_def_of_nonneg (le_of_lt hx), if_neg (ne_of_gt hx)]

lemma exp_mul (x y : ℝ) : exp (x * y) = (exp x) ^ y :=
by rw [rpow_def_of_pos (exp_pos _), log_exp]

@[simp] lemma exp_one_rpow (x : ℝ) : exp 1 ^ x = exp x := by rw [←exp_mul, one_mul]

lemma rpow_eq_zero_iff_of_nonneg {x y : ℝ} (hx : 0 ≤ x) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 :=
by { simp only [rpow_def_of_nonneg hx], split_ifs; simp [*, exp_ne_zero] }

open_locale real

lemma rpow_def_of_neg {x : ℝ} (hx : x < 0) (y : ℝ) : x ^ y = exp (log x * y) * cos (y * π) :=
begin
  rw [rpow_def, complex.cpow_def, if_neg],
  have : complex.log x * y = ↑(log(-x) * y) + ↑(y * π) * complex.I,
  { simp only [complex.log, abs_of_neg hx, complex.arg_of_real_of_neg hx,
      complex.abs_of_real, complex.of_real_mul], ring },
  { rw [this, complex.exp_add_mul_I, ← complex.of_real_exp, ← complex.of_real_cos,
      ← complex.of_real_sin, mul_add, ← complex.of_real_mul, ← mul_assoc, ← complex.of_real_mul,
      complex.add_re, complex.of_real_re, complex.mul_re, complex.I_re, complex.of_real_im,
      real.log_neg_eq_log],
    ring },
  { rw complex.of_real_eq_zero, exact ne_of_lt hx }
end

lemma rpow_def_of_nonpos {x : ℝ} (hx : x ≤ 0) (y : ℝ) : x ^ y =
  if x = 0
    then if y = 0
      then 1
      else 0
    else exp (log x * y) * cos (y * π) :=
by split_ifs; simp [rpow_def, *]; exact rpow_def_of_neg (lt_of_le_of_ne hx h) _

lemma rpow_pos_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : 0 < x ^ y :=
by rw rpow_def_of_pos hx; apply exp_pos

@[simp] lemma rpow_zero (x : ℝ) : x ^ (0 : ℝ) = 1 := by simp [rpow_def]

@[simp] lemma zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ) ^ x = 0 :=
by simp [rpow_def, *]

lemma zero_rpow_eq_iff {x : ℝ} {a : ℝ} : 0 ^ x = a ↔ (x ≠ 0 ∧ a = 0) ∨ (x = 0 ∧ a = 1) :=
begin
  split,
  { intros hyp,
    simp only [rpow_def, complex.of_real_zero] at hyp,
    by_cases x = 0,
    { subst h,
      simp only [complex.one_re, complex.of_real_zero, complex.cpow_zero] at hyp,
      exact or.inr ⟨rfl, hyp.symm⟩},
    { rw complex.zero_cpow (complex.of_real_ne_zero.mpr h) at hyp,
      exact or.inl ⟨h, hyp.symm⟩, }, },
  { rintro (⟨h,rfl⟩|⟨rfl,rfl⟩),
    { exact zero_rpow h, },
    { exact rpow_zero _, }, },
end

lemma eq_zero_rpow_iff {x : ℝ} {a : ℝ} : a = 0 ^ x ↔ (x ≠ 0 ∧ a = 0) ∨ (x = 0 ∧ a = 1) :=
by rw [←zero_rpow_eq_iff, eq_comm]

@[simp] lemma rpow_one (x : ℝ) : x ^ (1 : ℝ) = x := by simp [rpow_def]

@[simp] lemma one_rpow (x : ℝ) : (1 : ℝ) ^ x = 1 := by simp [rpow_def]

lemma zero_rpow_le_one (x : ℝ) : (0 : ℝ) ^ x ≤ 1 :=
by { by_cases h : x = 0; simp [h, zero_le_one] }

lemma zero_rpow_nonneg (x : ℝ) : 0 ≤ (0 : ℝ) ^ x :=
by { by_cases h : x = 0; simp [h, zero_le_one] }

lemma rpow_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y :=
by rw [rpow_def_of_nonneg hx];
  split_ifs; simp only [zero_le_one, le_refl, le_of_lt (exp_pos _)]

lemma abs_rpow_of_nonneg {x y : ℝ} (hx_nonneg : 0 ≤ x) : |x ^ y| = |x| ^ y :=
begin
  have h_rpow_nonneg : 0 ≤ x ^ y, from real.rpow_nonneg_of_nonneg hx_nonneg _,
  rw [abs_eq_self.mpr hx_nonneg, abs_eq_self.mpr h_rpow_nonneg],
end

lemma abs_rpow_le_abs_rpow (x y : ℝ) : |x ^ y| ≤ |x| ^ y :=
begin
  cases le_or_lt 0 x with hx hx,
  { rw [abs_rpow_of_nonneg hx] },
  { rw [abs_of_neg hx, rpow_def_of_neg hx, rpow_def_of_pos (neg_pos.2 hx), log_neg_eq_log,
      abs_mul, abs_of_pos (exp_pos _)],
    exact mul_le_of_le_one_right (exp_pos _).le (abs_cos_le_one _) }
end

lemma abs_rpow_le_exp_log_mul (x y : ℝ) : |x ^ y| ≤ exp (log x * y) :=
begin
  refine (abs_rpow_le_abs_rpow x y).trans _,
  by_cases hx : x = 0,
  { by_cases hy : y = 0; simp [hx, hy, zero_le_one] },
  { rw [rpow_def_of_pos (abs_pos.2 hx), log_abs] }
end

lemma norm_rpow_of_nonneg {x y : ℝ} (hx_nonneg : 0 ≤ x) : ‖x ^ y‖ = ‖x‖ ^ y :=
by { simp_rw real.norm_eq_abs, exact abs_rpow_of_nonneg hx_nonneg, }


variables {x y z : ℝ}

lemma rpow_add (hx : 0 < x) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z :=
by simp only [rpow_def_of_pos hx, mul_add, exp_add]

lemma rpow_add' (hx : 0 ≤ x) (h : y + z ≠ 0) : x ^ (y + z) = x ^ y * x ^ z :=
begin
  rcases hx.eq_or_lt with rfl|pos,
  { rw [zero_rpow h, zero_eq_mul],
    have : y ≠ 0 ∨ z ≠ 0, from not_and_distrib.1 (λ ⟨hy, hz⟩, h $ hy.symm ▸ hz.symm ▸ zero_add 0),
    exact this.imp zero_rpow zero_rpow },
  { exact rpow_add pos _ _ }
end

lemma rpow_add_of_nonneg (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
  x ^ (y + z) = x ^ y * x ^ z :=
begin
  rcases hy.eq_or_lt with rfl|hy,
  { rw [zero_add, rpow_zero, one_mul] },
  exact rpow_add' hx (ne_of_gt $ add_pos_of_pos_of_nonneg hy hz)
end

/-- For `0 ≤ x`, the only problematic case in the equality `x ^ y * x ^ z = x ^ (y + z)` is for
`x = 0` and `y + z = 0`, where the right hand side is `1` while the left hand side can vanish.
The inequality is always true, though, and given in this lemma. -/
lemma le_rpow_add {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ y * x ^ z ≤ x ^ (y + z) :=
begin
  rcases le_iff_eq_or_lt.1 hx with H|pos,
  { by_cases h : y + z = 0,
    { simp only [H.symm, h, rpow_zero],
      calc (0 : ℝ) ^ y * 0 ^ z ≤ 1 * 1 :
        mul_le_mul (zero_rpow_le_one y) (zero_rpow_le_one z) (zero_rpow_nonneg z) zero_le_one
      ... = 1 : by simp },
    { simp [rpow_add', ← H, h] } },
  { simp [rpow_add pos] }
end

lemma rpow_sum_of_pos {ι : Type*} {a : ℝ} (ha : 0 < a) (f : ι → ℝ) (s : finset ι) :
  a ^ (∑ x in s, f x) = ∏ x in s, a ^ f x :=
@add_monoid_hom.map_sum ℝ ι (additive ℝ) _ _ ⟨λ x : ℝ, (a ^ x : ℝ), rpow_zero a, rpow_add ha⟩ f s

lemma rpow_sum_of_nonneg {ι : Type*} {a : ℝ} (ha : 0 ≤ a) {s : finset ι} {f : ι → ℝ}
  (h : ∀ x ∈ s, 0 ≤ f x) :
  a ^ (∑ x in s, f x) = ∏ x in s, a ^ f x :=
begin
  induction s using finset.cons_induction with i s hi ihs,
  { rw [sum_empty, finset.prod_empty, rpow_zero] },
  { rw forall_mem_cons at h,
    rw [sum_cons, prod_cons, ← ihs h.2, rpow_add_of_nonneg ha h.1 (sum_nonneg h.2)] }
end

lemma rpow_neg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ -y = (x ^ y)⁻¹ :=
by simp only [rpow_def_of_nonneg hx]; split_ifs; simp [*, exp_neg] at *

lemma rpow_sub {x : ℝ} (hx : 0 < x) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z :=
by simp only [sub_eq_add_neg, rpow_add hx, rpow_neg (le_of_lt hx), div_eq_mul_inv]

lemma rpow_sub' {x : ℝ} (hx : 0 ≤ x) {y z : ℝ} (h : y - z ≠ 0) :
  x ^ (y - z) = x ^ y / x ^ z :=
by { simp only [sub_eq_add_neg] at h ⊢, simp only [rpow_add' hx h, rpow_neg hx, div_eq_mul_inv] }

end real

/-!
## Comparing real and complex powers
-/

namespace complex

lemma of_real_cpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : ((x ^ y : ℝ) : ℂ) = (x : ℂ) ^ (y : ℂ) :=
by simp only [real.rpow_def_of_nonneg hx, complex.cpow_def, of_real_eq_zero]; split_ifs;
  simp [complex.of_real_log hx]

lemma of_real_cpow_of_nonpos {x : ℝ} (hx : x ≤ 0) (y : ℂ) :
  (x : ℂ) ^ y = ((-x) : ℂ) ^ y * exp (π * I * y) :=
begin
  rcases hx.eq_or_lt with rfl|hlt,
  { rcases eq_or_ne y 0 with rfl|hy; simp * },
  have hne : (x : ℂ) ≠ 0, from of_real_ne_zero.mpr hlt.ne,
  rw [cpow_def_of_ne_zero hne, cpow_def_of_ne_zero (neg_ne_zero.2 hne), ← exp_add, ← add_mul,
      log, log, abs.map_neg, arg_of_real_of_neg hlt, ← of_real_neg,
      arg_of_real_of_nonneg (neg_nonneg.2 hx), of_real_zero, zero_mul, add_zero]
end

lemma abs_cpow_of_ne_zero {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
  abs (z ^ w) = abs z ^ w.re / real.exp (arg z * im w) :=
by rw [cpow_def_of_ne_zero hz, abs_exp, mul_re, log_re, log_im, real.exp_sub,
  real.rpow_def_of_pos (abs.pos hz)]

lemma abs_cpow_of_imp {z w : ℂ} (h : z = 0 → w.re = 0 → w = 0) :
  abs (z ^ w) = abs z ^ w.re / real.exp (arg z * im w) :=
begin
  rcases ne_or_eq z 0 with hz|rfl; [exact (abs_cpow_of_ne_zero hz w), rw map_zero],
  cases eq_or_ne w.re 0 with hw hw,
  { simp [hw, h rfl hw] },
  { rw [real.zero_rpow hw, zero_div, zero_cpow, map_zero],
    exact ne_of_apply_ne re hw }
end

lemma abs_cpow_le (z w : ℂ) : abs (z ^ w) ≤ abs z ^ w.re / real.exp (arg z * im w) :=
begin
  rcases ne_or_eq z 0 with hz|rfl; [exact (abs_cpow_of_ne_zero hz w).le, rw map_zero],
  rcases eq_or_ne w 0 with rfl|hw, { simp },
  rw [zero_cpow hw, map_zero],
  exact div_nonneg (real.rpow_nonneg_of_nonneg le_rfl _) (real.exp_pos _).le
end

@[simp] lemma abs_cpow_real (x : ℂ) (y : ℝ) : abs (x ^ (y : ℂ)) = x.abs ^ y :=
by rcases eq_or_ne x 0 with rfl|hx; [rcases eq_or_ne y 0 with rfl|hy, skip];
  simp [*, abs_cpow_of_ne_zero]

@[simp] lemma abs_cpow_inv_nat (x : ℂ) (n : ℕ) : abs (x ^ (n⁻¹ : ℂ)) = x.abs ^ (n⁻¹ : ℝ) :=
by rw ← abs_cpow_real; simp [-abs_cpow_real]

lemma abs_cpow_eq_rpow_re_of_pos {x : ℝ} (hx : 0 < x) (y : ℂ) : abs (x ^ y) = x ^ y.re :=
by rw [abs_cpow_of_ne_zero (of_real_ne_zero.mpr hx.ne'), arg_of_real_of_nonneg hx.le, zero_mul,
  real.exp_zero, div_one, abs_of_nonneg hx.le]

lemma abs_cpow_eq_rpow_re_of_nonneg {x : ℝ} (hx : 0 ≤ x) {y : ℂ} (hy : re y ≠ 0) :
  abs (x ^ y) = x ^ re y :=
begin
  rcases hx.eq_or_lt with rfl|hlt,
  { rw [of_real_zero, zero_cpow, map_zero, real.zero_rpow hy],
    exact ne_of_apply_ne re hy },
  { exact abs_cpow_eq_rpow_re_of_pos hlt y }
end

end complex

/-!
## Further algebraic properties of `rpow`
-/

namespace real

variables {x y z : ℝ}

lemma rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
by rw [← complex.of_real_inj, complex.of_real_cpow (rpow_nonneg_of_nonneg hx _),
    complex.of_real_cpow hx, complex.of_real_mul, complex.cpow_mul, complex.of_real_cpow hx];
  simp only [(complex.of_real_mul _ _).symm, (complex.of_real_log hx).symm,
    complex.of_real_im, neg_lt_zero, pi_pos, le_of_lt pi_pos]

lemma rpow_add_int {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℤ) : x ^ (y + n) = x ^ y * x ^ n :=
by rw [rpow_def, complex.of_real_add, complex.cpow_add _ _ (complex.of_real_ne_zero.mpr hx),
  complex.of_real_int_cast, complex.cpow_int_cast, ← complex.of_real_zpow, mul_comm,
  complex.of_real_mul_re, ← rpow_def, mul_comm]

lemma rpow_add_nat {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y + n) = x ^ y * x ^ n :=
by simpa using rpow_add_int hx y n

lemma rpow_sub_int {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℤ) : x ^ (y - n) = x ^ y / x ^ n :=
by simpa using rpow_add_int hx y (-n)

lemma rpow_sub_nat {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y - n) = x ^ y / x ^ n :=
by simpa using rpow_sub_int hx y n

lemma rpow_add_one {x : ℝ} (hx : x ≠ 0) (y : ℝ) : x ^ (y + 1) = x ^ y * x :=
by simpa using rpow_add_nat hx y 1

lemma rpow_sub_one {x : ℝ} (hx : x ≠ 0) (y : ℝ) : x ^ (y - 1) = x ^ y / x :=
by simpa using rpow_sub_nat hx y 1

@[simp, norm_cast] lemma rpow_int_cast (x : ℝ) (n : ℤ) : x ^ (n : ℝ) = x ^ n :=
by simp only [rpow_def, ← complex.of_real_zpow, complex.cpow_int_cast,
  complex.of_real_int_cast, complex.of_real_re]

@[simp, norm_cast] lemma rpow_nat_cast (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
by simpa using rpow_int_cast x n

@[simp] lemma rpow_two (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 :=
by { rw ← rpow_nat_cast, simp only [nat.cast_bit0, nat.cast_one] }

lemma rpow_neg_one (x : ℝ) : x ^ (-1 : ℝ) = x⁻¹ :=
begin
  suffices H : x ^ ((-1 : ℤ) : ℝ) = x⁻¹, by rwa [int.cast_neg, int.cast_one] at H,
  simp only [rpow_int_cast, zpow_one, zpow_neg],
end

lemma mul_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : 0 ≤ y) : (x*y)^z = x^z * y^z :=
begin
  iterate 3 { rw real.rpow_def_of_nonneg }, split_ifs; simp * at *,
  { have hx : 0 < x,
    { cases lt_or_eq_of_le h with h₂ h₂, { exact h₂ },
      exfalso, apply h_2, exact eq.symm h₂ },
    have hy : 0 < y,
    { cases lt_or_eq_of_le h₁ with h₂ h₂, { exact h₂ },
      exfalso, apply h_3, exact eq.symm h₂ },
    rw [log_mul (ne_of_gt hx) (ne_of_gt hy), add_mul, exp_add]},
  { exact h₁ },
  { exact h },
  { exact mul_nonneg h h₁ },
end

lemma inv_rpow (hx : 0 ≤ x) (y : ℝ) : (x⁻¹)^y = (x^y)⁻¹ :=
by simp only [← rpow_neg_one, ← rpow_mul hx, mul_comm]

lemma div_rpow (hx : 0 ≤ x) (hy : 0 ≤ y) (z : ℝ) : (x / y) ^ z = x^z / y^z :=
by simp only [div_eq_mul_inv, mul_rpow hx (inv_nonneg.2 hy), inv_rpow hy]

lemma log_rpow {x : ℝ} (hx : 0 < x) (y : ℝ) : log (x^y) = y * (log x) :=
begin
  apply exp_injective,
  rw [exp_log (rpow_pos_of_pos hx y), ← exp_log hx, mul_comm, rpow_def_of_pos (exp_pos (log x)) y],
end

/-!
## Order and monotonicity
-/

lemma rpow_lt_rpow (hx : 0 ≤ x) (hxy : x < y) (hz : 0 < z) : x^z < y^z :=
begin
  rw le_iff_eq_or_lt at hx, cases hx,
  { rw [← hx, zero_rpow (ne_of_gt hz)], exact rpow_pos_of_pos (by rwa ← hx at hxy) _ },
  rw [rpow_def_of_pos hx, rpow_def_of_pos (lt_trans hx hxy), exp_lt_exp],
  exact mul_lt_mul_of_pos_right (log_lt_log hx hxy) hz
end

lemma rpow_le_rpow {x y z: ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x^z ≤ y^z :=
begin
  rcases eq_or_lt_of_le h₁ with rfl|h₁', { refl },
  rcases eq_or_lt_of_le h₂ with rfl|h₂', { simp },
  exact le_of_lt (rpow_lt_rpow h h₁' h₂')
end

lemma rpow_lt_rpow_iff (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
⟨lt_imp_lt_of_le_imp_le $ λ h, rpow_le_rpow hy h (le_of_lt hz), λ h, rpow_lt_rpow hx h hz⟩

lemma rpow_le_rpow_iff (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
le_iff_le_iff_lt_iff_lt.2 $ rpow_lt_rpow_iff hy hx hz

lemma le_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
  x ≤ y ^ z⁻¹ ↔ y ≤ x ^ z :=
begin
  have hz' : 0 < -z := by rwa [lt_neg, neg_zero],
  have hxz : 0 < x ^ (-z) := real.rpow_pos_of_pos hx _,
  have hyz : 0 < y ^ z⁻¹ := real.rpow_pos_of_pos hy _,
  rw [←real.rpow_le_rpow_iff hx.le hyz.le hz', ←real.rpow_mul hy.le],
  simp only [ne_of_lt hz, real.rpow_neg_one, mul_neg, inv_mul_cancel, ne.def, not_false_iff],
  rw [le_inv hxz hy, ←real.rpow_neg_one, ←real.rpow_mul hx.le],
  simp,
end

lemma lt_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
  x < y ^ z⁻¹ ↔ y < x ^ z :=
begin
  have hz' : 0 < -z := by rwa [lt_neg, neg_zero],
  have hxz : 0 < x ^ (-z) := real.rpow_pos_of_pos hx _,
  have hyz : 0 < y ^ z⁻¹ := real.rpow_pos_of_pos hy _,
  rw [←real.rpow_lt_rpow_iff hx.le hyz.le hz', ←real.rpow_mul hy.le],
  simp only [ne_of_lt hz, real.rpow_neg_one, mul_neg, inv_mul_cancel, ne.def, not_false_iff],
  rw [lt_inv hxz hy, ←real.rpow_neg_one, ←real.rpow_mul hx.le],
  simp,
end

lemma rpow_inv_lt_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
  x ^ z⁻¹ < y ↔ y ^ z < x :=
begin
  convert lt_rpow_inv_iff_of_neg (real.rpow_pos_of_pos hx _) (real.rpow_pos_of_pos hy _) hz;
  simp [←real.rpow_mul hx.le, ←real.rpow_mul hy.le, ne_of_lt hz],
end

lemma rpow_inv_le_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
  x ^ z⁻¹ ≤ y ↔ y ^ z ≤ x :=
begin
  convert le_rpow_inv_iff_of_neg (real.rpow_pos_of_pos hx _) (real.rpow_pos_of_pos hy _) hz;
  simp [←real.rpow_mul hx.le, ←real.rpow_mul hy.le, ne_of_lt hz],
end

lemma rpow_lt_rpow_of_exponent_lt (hx : 1 < x) (hyz : y < z) : x^y < x^z :=
begin
  repeat {rw [rpow_def_of_pos (lt_trans zero_lt_one hx)]},
  rw exp_lt_exp, exact mul_lt_mul_of_pos_left hyz (log_pos hx),
end

lemma rpow_le_rpow_of_exponent_le (hx : 1 ≤ x) (hyz : y ≤ z) : x^y ≤ x^z :=
begin
  repeat {rw [rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hx)]},
  rw exp_le_exp, exact mul_le_mul_of_nonneg_left hyz (log_nonneg hx),
end

@[simp] lemma rpow_le_rpow_left_iff (hx : 1 < x) : x ^ y ≤ x ^ z ↔ y ≤ z :=
begin
  have x_pos : 0 < x := lt_trans zero_lt_one hx,
  rw [←log_le_log (rpow_pos_of_pos x_pos y) (rpow_pos_of_pos x_pos z),
      log_rpow x_pos, log_rpow x_pos, mul_le_mul_right (log_pos hx)],
end

@[simp] lemma rpow_lt_rpow_left_iff (hx : 1 < x) : x ^ y < x ^ z ↔ y < z :=
by rw [lt_iff_not_le, rpow_le_rpow_left_iff hx, lt_iff_not_le]

lemma rpow_lt_rpow_of_exponent_gt (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
  x^y < x^z :=
begin
  repeat {rw [rpow_def_of_pos hx0]},
  rw exp_lt_exp, exact mul_lt_mul_of_neg_left hyz (log_neg hx0 hx1),
end

lemma rpow_le_rpow_of_exponent_ge (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) :
  x^y ≤ x^z :=
begin
  repeat {rw [rpow_def_of_pos hx0]},
  rw exp_le_exp, exact mul_le_mul_of_nonpos_left hyz (log_nonpos (le_of_lt hx0) hx1),
end

@[simp] lemma rpow_le_rpow_left_iff_of_base_lt_one (hx0 : 0 < x) (hx1 : x < 1) :
  x ^ y ≤ x ^ z ↔ z ≤ y :=
begin
  rw [←log_le_log (rpow_pos_of_pos hx0 y) (rpow_pos_of_pos hx0 z),
      log_rpow hx0, log_rpow hx0, mul_le_mul_right_of_neg (log_neg hx0 hx1)],
end

@[simp] lemma rpow_lt_rpow_left_iff_of_base_lt_one (hx0 : 0 < x) (hx1 : x < 1) :
  x ^ y < x ^ z ↔ z < y :=
by rw [lt_iff_not_le, rpow_le_rpow_left_iff_of_base_lt_one hx0 hx1, lt_iff_not_le]

lemma rpow_lt_one {x z : ℝ} (hx1 : 0 ≤ x) (hx2 : x < 1) (hz : 0 < z) : x^z < 1 :=
by { rw ← one_rpow z, exact rpow_lt_rpow hx1 hx2 hz }

lemma rpow_le_one {x z : ℝ} (hx1 : 0 ≤ x) (hx2 : x ≤ 1) (hz : 0 ≤ z) : x^z ≤ 1 :=
by { rw ← one_rpow z, exact rpow_le_rpow hx1 hx2 hz }

lemma rpow_lt_one_of_one_lt_of_neg {x z : ℝ} (hx : 1 < x) (hz : z < 0) : x^z < 1 :=
by { convert rpow_lt_rpow_of_exponent_lt hx hz, exact (rpow_zero x).symm }

lemma rpow_le_one_of_one_le_of_nonpos {x z : ℝ} (hx : 1 ≤ x) (hz : z ≤ 0) : x^z ≤ 1 :=
by { convert rpow_le_rpow_of_exponent_le hx hz, exact (rpow_zero x).symm }

lemma one_lt_rpow {x z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x^z :=
by { rw ← one_rpow z, exact rpow_lt_rpow zero_le_one hx hz }

lemma one_le_rpow {x z : ℝ} (hx : 1 ≤ x) (hz : 0 ≤ z) : 1 ≤ x^z :=
by { rw ← one_rpow z, exact rpow_le_rpow zero_le_one hx hz }

lemma one_lt_rpow_of_pos_of_lt_one_of_neg (hx1 : 0 < x) (hx2 : x < 1) (hz : z < 0) :
  1 < x^z :=
by { convert rpow_lt_rpow_of_exponent_gt hx1 hx2 hz, exact (rpow_zero x).symm }

lemma one_le_rpow_of_pos_of_le_one_of_nonpos (hx1 : 0 < x) (hx2 : x ≤ 1) (hz : z ≤ 0) :
  1 ≤ x^z :=
by { convert rpow_le_rpow_of_exponent_ge hx1 hx2 hz, exact (rpow_zero x).symm }

lemma rpow_lt_one_iff_of_pos (hx : 0 < x) : x ^ y < 1 ↔ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y :=
by rw [rpow_def_of_pos hx, exp_lt_one_iff, mul_neg_iff, log_pos_iff hx, log_neg_iff hx]

lemma rpow_lt_one_iff (hx : 0 ≤ x) : x ^ y < 1 ↔ x = 0 ∧ y ≠ 0 ∨ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y :=
begin
  rcases hx.eq_or_lt with (rfl|hx),
  { rcases em (y = 0) with (rfl|hy); simp [*, lt_irrefl, zero_lt_one] },
  { simp [rpow_lt_one_iff_of_pos hx, hx.ne.symm] }
end

lemma one_lt_rpow_iff_of_pos (hx : 0 < x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ x < 1 ∧ y < 0 :=
by rw [rpow_def_of_pos hx, one_lt_exp_iff, mul_pos_iff, log_pos_iff hx, log_neg_iff hx]

lemma one_lt_rpow_iff (hx : 0 ≤ x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ 0 < x ∧ x < 1 ∧ y < 0 :=
begin
  rcases hx.eq_or_lt with (rfl|hx),
  { rcases em (y = 0) with (rfl|hy); simp [*, lt_irrefl, (zero_lt_one' ℝ).not_lt] },
  { simp [one_lt_rpow_iff_of_pos hx, hx] }
end

lemma rpow_le_rpow_of_exponent_ge' (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hz : 0 ≤ z) (hyz : z ≤ y) :
  x^y ≤ x^z :=
begin
  rcases eq_or_lt_of_le hx0 with rfl | hx0',
  { rcases eq_or_lt_of_le hz with rfl | hz',
    { exact (rpow_zero 0).symm ▸ (rpow_le_one hx0 hx1 hyz), },
    rw [zero_rpow, zero_rpow]; linarith, },
  { exact rpow_le_rpow_of_exponent_ge hx0' hx1 hyz, },
end

lemma rpow_left_inj_on {x : ℝ} (hx : x ≠ 0) :
  inj_on (λ y : ℝ, y^x) {y : ℝ | 0 ≤ y} :=
begin
  rintros y hy z hz (hyz : y ^ x = z ^ x),
  rw [←rpow_one y, ←rpow_one z, ←_root_.mul_inv_cancel hx, rpow_mul hy, rpow_mul hz, hyz]
end

lemma le_rpow_iff_log_le (hx : 0 < x) (hy : 0 < y) :
  x ≤ y^z ↔ real.log x ≤ z * real.log y :=
by rw [←real.log_le_log hx (real.rpow_pos_of_pos hy z), real.log_rpow hy]

lemma le_rpow_of_log_le (hx : 0 ≤ x) (hy : 0 < y) (h : real.log x ≤ z * real.log y) :
  x ≤ y^z :=
begin
  obtain hx | rfl := hx.lt_or_eq,
  { exact (le_rpow_iff_log_le hx hy).2 h },
  exact (real.rpow_pos_of_pos hy z).le,
end

lemma lt_rpow_iff_log_lt (hx : 0 < x) (hy : 0 < y) :
  x < y^z ↔ real.log x < z * real.log y :=
by rw [←real.log_lt_log_iff hx (real.rpow_pos_of_pos hy z), real.log_rpow hy]

lemma lt_rpow_of_log_lt (hx : 0 ≤ x) (hy : 0 < y) (h : real.log x < z * real.log y) :
  x < y^z :=
begin
  obtain hx | rfl := hx.lt_or_eq,
  { exact (lt_rpow_iff_log_lt hx hy).2 h },
  exact real.rpow_pos_of_pos hy z,
end

lemma rpow_le_one_iff_of_pos (hx : 0 < x) : x ^ y ≤ 1 ↔ 1 ≤ x ∧ y ≤ 0 ∨ x ≤ 1 ∧ 0 ≤ y :=
by rw [rpow_def_of_pos hx, exp_le_one_iff, mul_nonpos_iff, log_nonneg_iff hx, log_nonpos_iff hx]

/-- Bound for `|log x * x ^ t|` in the interval `(0, 1]`, for positive real `t`. -/
lemma abs_log_mul_self_rpow_lt (x t : ℝ) (h1 : 0 < x) (h2 : x ≤ 1) (ht : 0 < t) :
  |log x * x ^ t| < 1 / t :=
begin
  rw lt_div_iff ht,
  have := abs_log_mul_self_lt (x ^ t) (rpow_pos_of_pos h1 t) (rpow_le_one h1.le h2 ht.le),
  rwa [log_rpow h1, mul_assoc, abs_mul, abs_of_pos ht, mul_comm] at this
end

lemma pow_nat_rpow_nat_inv {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) :
  (x ^ n) ^ (n⁻¹ : ℝ) = x :=
have hn0 : (n : ℝ) ≠ 0, from nat.cast_ne_zero.2 hn,
by rw [← rpow_nat_cast, ← rpow_mul hx, mul_inv_cancel hn0, rpow_one]

lemma rpow_nat_inv_pow_nat {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) :
  (x ^ (n⁻¹ : ℝ)) ^ n = x :=
have hn0 : (n : ℝ) ≠ 0, from nat.cast_ne_zero.2 hn,
by rw [← rpow_nat_cast, ← rpow_mul hx, inv_mul_cancel hn0, rpow_one]


end real

/-!
## Square roots of reals
-/
namespace real

variables {z x y : ℝ}

section sqrt

lemma sqrt_eq_rpow (x : ℝ) : sqrt x = x ^ (1/(2:ℝ)) :=
begin
  obtain h | h := le_or_lt 0 x,
  { rw [← mul_self_inj_of_nonneg (sqrt_nonneg _) (rpow_nonneg_of_nonneg h _), mul_self_sqrt h,
      ← sq, ← rpow_nat_cast, ← rpow_mul h],
    norm_num },
  { have : 1 / (2:ℝ) * π = π / (2:ℝ), ring,
    rw [sqrt_eq_zero_of_nonpos h.le, rpow_def_of_neg h, this, cos_pi_div_two, mul_zero] }
end

lemma rpow_div_two_eq_sqrt {x : ℝ} (r : ℝ) (hx : 0 ≤ x) : x ^ (r/2) = (sqrt x) ^ r :=
begin
  rw [sqrt_eq_rpow, ← rpow_mul hx],
  congr,
  ring,
end

end sqrt

variables {n : ℕ}

lemma exists_rat_pow_btwn_rat_aux (hn : n ≠ 0) (x y : ℝ) (h : x < y) (hy : 0 < y) :
  ∃ q : ℚ, 0 < q ∧ x < q^n ∧ ↑q^n < y :=
begin
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn.bot_lt,
  obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn (rpow_lt_rpow (le_max_left 0 x) (max_lt hy h) $
    inv_pos.mpr hn'),
  have := rpow_nonneg_of_nonneg (le_max_left 0 x) n⁻¹,
  have hq := this.trans_lt hxq,
  replace hxq := rpow_lt_rpow this hxq hn',
  replace hqy := rpow_lt_rpow hq.le hqy hn',
  rw [rpow_nat_cast, rpow_nat_cast, rpow_nat_inv_pow_nat _ hn] at hxq hqy,
  exact ⟨q, by exact_mod_cast hq, (le_max_right _ _).trans_lt hxq, hqy⟩,
  { exact le_max_left _ _ },
  { exact hy.le }
end

lemma exists_rat_pow_btwn_rat (hn : n ≠ 0) {x y : ℚ} (h : x < y) (hy : 0 < y) :
  ∃ q : ℚ, 0 < q ∧ x < q^n ∧ q^n < y :=
by apply_mod_cast exists_rat_pow_btwn_rat_aux hn x y; assumption

/-- There is a rational power between any two positive elements of an archimedean ordered field. -/
lemma exists_rat_pow_btwn {α : Type*} [linear_ordered_field α] [archimedean α] (hn : n ≠ 0)
  {x y : α} (h : x < y) (hy : 0 < y) : ∃ q : ℚ, 0 < q ∧ x < q^n ∧ (q^n : α) < y :=
begin
  obtain ⟨q₂, hx₂, hy₂⟩ := exists_rat_btwn (max_lt h hy),
  obtain ⟨q₁, hx₁, hq₁₂⟩ := exists_rat_btwn hx₂,
  have : (0 : α) < q₂ := (le_max_right _ _).trans_lt hx₂,
  norm_cast at hq₁₂ this,
  obtain ⟨q, hq, hq₁, hq₂⟩ := exists_rat_pow_btwn_rat hn hq₁₂ this,
  refine ⟨q, hq, (le_max_left _ _).trans_lt $ hx₁.trans _, hy₂.trans' _⟩; assumption_mod_cast,
end

end real
