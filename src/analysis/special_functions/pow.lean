/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel
-/
import analysis.special_functions.trigonometric
import analysis.calculus.extend_deriv

/-!
# Power function on `ℂ`, `ℝ` and `ℝ⁺`

We construct the power functions `x ^ y` where `x` and `y` are complex numbers, or `x` and `y` are
real numbers, or `x` is a nonnegative real and `y` is real, and prove their basic properties.
-/

noncomputable theory

open_locale classical real topological_space nnreal

namespace complex

/-- The complex power function `x^y`, given by `x^y = exp(y log x)` (where `log` is the principal
determination of the logarithm), unless `x = 0` where one sets `0^0 = 1` and `0^y = 0` for
`y ≠ 0`. -/
noncomputable def cpow (x y : ℂ) : ℂ :=
if x = 0
  then if y = 0
    then 1
    else 0
  else exp (log x * y)

noncomputable instance : has_pow ℂ ℂ := ⟨cpow⟩

@[simp] lemma cpow_eq_pow (x y : ℂ) : cpow x y = x ^ y := rfl

lemma cpow_def (x y : ℂ) : x ^ y =
  if x = 0
    then if y = 0
      then 1
      else 0
    else exp (log x * y) := rfl

@[simp] lemma cpow_zero (x : ℂ) : x ^ (0 : ℂ) = 1 := by simp [cpow_def]

@[simp] lemma cpow_eq_zero_iff (x y : ℂ) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 :=
by { simp only [cpow_def], split_ifs; simp [*, exp_ne_zero] }

@[simp] lemma zero_cpow {x : ℂ} (h : x ≠ 0) : (0 : ℂ) ^ x = 0 :=
by simp [cpow_def, *]

@[simp] lemma cpow_one (x : ℂ) : x ^ (1 : ℂ) = x :=
if hx : x = 0 then by simp [hx, cpow_def]
else by rw [cpow_def, if_neg (one_ne_zero : (1 : ℂ) ≠ 0), if_neg hx, mul_one, exp_log hx]

@[simp] lemma one_cpow (x : ℂ) : (1 : ℂ) ^ x = 1 :=
by rw cpow_def; split_ifs; simp [one_ne_zero, *] at *

lemma cpow_add {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y + z) = x ^ y * x ^ z :=
by simp [cpow_def]; split_ifs; simp [*, exp_add, mul_add] at *

lemma cpow_mul {x y : ℂ} (z : ℂ) (h₁ : -π < (log x * y).im) (h₂ : (log x * y).im ≤ π) :
  x ^ (y * z) = (x ^ y) ^ z :=
begin
  simp [cpow_def],
  split_ifs;
  simp [*, exp_ne_zero, log_exp h₁ h₂, mul_assoc] at *
end

lemma cpow_neg (x y : ℂ) : x ^ -y = (x ^ y)⁻¹ :=
by simp [cpow_def]; split_ifs; simp [exp_neg]

lemma cpow_neg_one (x : ℂ) : x ^ (-1 : ℂ) = x⁻¹ :=
by simpa using cpow_neg x 1

@[simp] lemma cpow_nat_cast (x : ℂ) : ∀ (n : ℕ), x ^ (n : ℂ) = x ^ n
| 0       := by simp
| (n + 1) := if hx : x = 0 then by simp only [hx, pow_succ,
    complex.zero_cpow (nat.cast_ne_zero.2 (nat.succ_ne_zero _)), zero_mul]
  else by simp [cpow_add, hx, pow_add, cpow_nat_cast n]

@[simp] lemma cpow_int_cast (x : ℂ) : ∀ (n : ℤ), x ^ (n : ℂ) = x ^ n
| (n : ℕ) := by simp; refl
| -[1+ n] := by rw fpow_neg_succ_of_nat;
  simp only [int.neg_succ_of_nat_coe, int.cast_neg, complex.cpow_neg, inv_eq_one_div,
    int.cast_coe_nat, cpow_nat_cast]

lemma cpow_nat_inv_pow (x : ℂ) {n : ℕ} (hn : 0 < n) : (x ^ (n⁻¹ : ℂ)) ^ n = x :=
have (log x * (↑n)⁻¹).im = (log x).im / n,
  by rw [div_eq_mul_inv, ← of_real_nat_cast, ← of_real_inv, mul_im,
                of_real_re, of_real_im]; simp,
have h : -π < (log x * (↑n)⁻¹).im ∧ (log x * (↑n)⁻¹).im ≤ π,
  from (le_total (log x).im 0).elim
    (λ h, ⟨calc -π < (log x).im : by simp [log, neg_pi_lt_arg]
            ... ≤ ((log x).im * 1) / n : le_div_of_mul_le (nat.cast_pos.2 hn)
              (mul_le_mul_of_nonpos_left (by rw ← nat.cast_one; exact nat.cast_le.2 hn) h)
            ... = (log x * (↑n)⁻¹).im : by simp [this],
          this.symm ▸ le_trans (div_nonpos_of_nonpos_of_pos h (nat.cast_pos.2 hn))
            (le_of_lt real.pi_pos)⟩)
    (λ h, ⟨this.symm ▸ lt_of_lt_of_le (neg_neg_of_pos real.pi_pos)
            (div_nonneg h (nat.cast_pos.2 hn)),
          calc (log x * (↑n)⁻¹).im = (1 * (log x).im) / n : by simp [this]
            ... ≤ (log x).im : (div_le_of_le_mul (nat.cast_pos.2 hn)
              (mul_le_mul_of_nonneg_right (by rw ← nat.cast_one; exact nat.cast_le.2 hn) h))
            ... ≤ _ : by simp [log, arg_le_pi]⟩),
by rw [← cpow_nat_cast, ← cpow_mul _ h.1 h.2,
    inv_mul_cancel (show (n : ℂ) ≠ 0, from nat.cast_ne_zero.2 (nat.pos_iff_ne_zero.1 hn)),
    cpow_one]

end complex

namespace real

/-- The real power function `x^y`, defined as the real part of the complex power function.
For `x > 0`, it is equal to `exp(y log x)`. For `x = 0`, one sets `0^0=1` and `0^y=0` for `y ≠ 0`.
For `x < 0`, the definition is somewhat arbitary as it depends on the choice of a complex
determination of the logarithm. With our conventions, it is equal to `exp (y log x) cos (πy)`. -/
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
  simp [*, (complex.of_real_log hx).symm, -complex.of_real_mul,
    (complex.of_real_mul _ _).symm, complex.exp_of_real_re] at *

lemma rpow_def_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : x ^ y = exp (log x * y) :=
by rw [rpow_def_of_nonneg (le_of_lt hx), if_neg (ne_of_gt hx)]

lemma rpow_eq_zero_iff_of_nonneg {x y : ℝ} (hx : 0 ≤ x) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 :=
by { simp only [rpow_def_of_nonneg hx], split_ifs; simp [*, exp_ne_zero] }

open_locale real

lemma rpow_def_of_neg {x : ℝ} (hx : x < 0) (y : ℝ) : x ^ y = exp (log x * y) * cos (y * π) :=
begin
  rw [rpow_def, complex.cpow_def, if_neg],
  have : complex.log x * y = ↑(log(-x) * y) + ↑(y * π) * complex.I,
    simp only [complex.log, abs_of_neg hx, complex.arg_of_real_of_neg hx,
      complex.abs_of_real, complex.of_real_mul], ring,
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

lemma abs_rpow_le_abs_rpow (x y : ℝ) : abs (x ^ y) ≤ abs (x) ^ y :=
abs_le_of_le_of_neg_le
begin
  cases lt_trichotomy 0 x, { rw abs_of_pos h },
  cases h, { simp [h.symm] },
  rw [rpow_def_of_neg h, rpow_def_of_pos (abs_pos_of_neg h), log_abs],
  calc exp (log x * y) * cos (y * π) ≤ exp (log x * y) * 1 :
    mul_le_mul_of_nonneg_left (cos_le_one _) (le_of_lt $ exp_pos _)
  ... = _ : mul_one _
end
begin
  cases lt_trichotomy 0 x, { rw abs_of_pos h, have : 0 < x^y := rpow_pos_of_pos h _, linarith },
  cases h, { simp only [h.symm, abs_zero, rpow_def_of_nonneg], split_ifs, repeat {norm_num} },
  rw [rpow_def_of_neg h, rpow_def_of_pos (abs_pos_of_neg h), log_abs],
  calc -(exp (log x * y) * cos (y * π)) = exp (log x * y) * (-cos (y * π)) : by ring
    ... ≤ exp (log x * y) * 1 :
      mul_le_mul_of_nonneg_left (neg_le.2 $ neg_one_le_cos _) (le_of_lt $ exp_pos _)
    ... = exp (log x * y) : mul_one _
end

end real

namespace complex

lemma of_real_cpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : ((x ^ y : ℝ) : ℂ) = (x : ℂ) ^ (y : ℂ) :=
by simp [real.rpow_def_of_nonneg hx, complex.cpow_def]; split_ifs; simp [complex.of_real_log hx]

@[simp] lemma abs_cpow_real (x : ℂ) (y : ℝ) : abs (x ^ (y : ℂ)) = x.abs ^ y :=
begin
  rw [real.rpow_def_of_nonneg (abs_nonneg _), complex.cpow_def],
  split_ifs;
  simp [*, abs_of_nonneg (le_of_lt (real.exp_pos _)), complex.log, complex.exp_add,
    add_mul, mul_right_comm _ I, exp_mul_I, abs_cos_add_sin_mul_I,
    (complex.of_real_mul _ _).symm, -complex.of_real_mul] at *
end

@[simp] lemma abs_cpow_inv_nat (x : ℂ) (n : ℕ) : abs (x ^ (n⁻¹ : ℂ)) = x.abs ^ (n⁻¹ : ℝ) :=
by rw ← abs_cpow_real; simp [-abs_cpow_real]

end complex

namespace real

variables {x y z : ℝ}

@[simp] lemma rpow_zero (x : ℝ) : x ^ (0 : ℝ) = 1 := by simp [rpow_def]

@[simp] lemma zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ) ^ x = 0 :=
by simp [rpow_def, *]

@[simp] lemma rpow_one (x : ℝ) : x ^ (1 : ℝ) = x := by simp [rpow_def]

@[simp] lemma one_rpow (x : ℝ) : (1 : ℝ) ^ x = 1 := by simp [rpow_def]

lemma zero_rpow_le_one (x : ℝ) : (0 : ℝ) ^ x ≤ 1 :=
by { by_cases h : x = 0; simp [h, zero_le_one] }

lemma zero_rpow_nonneg (x : ℝ) : 0 ≤ (0 : ℝ) ^ x :=
by { by_cases h : x = 0; simp [h, zero_le_one] }

lemma rpow_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y :=
by rw [rpow_def_of_nonneg hx];
  split_ifs; simp only [zero_le_one, le_refl, le_of_lt (exp_pos _)]

lemma rpow_add {x : ℝ} (hx : 0 < x) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z :=
by simp only [rpow_def_of_pos hx, mul_add, exp_add]

lemma rpow_add' {x : ℝ} (hx : 0 ≤ x) {y z : ℝ} (h : y + z ≠ 0) : x ^ (y + z) = x ^ y * x ^ z :=
begin
  rcases le_iff_eq_or_lt.1 hx with H|pos,
  { simp only [← H, h, rpow_eq_zero_iff_of_nonneg, true_and, zero_rpow, eq_self_iff_true, ne.def,
               not_false_iff, zero_eq_mul],
    by_contradiction F,
    push_neg at F,
    apply h,
    simp [F] },
  { exact rpow_add pos _ _ }
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

lemma rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
by rw [← complex.of_real_inj, complex.of_real_cpow (rpow_nonneg_of_nonneg hx _),
    complex.of_real_cpow hx, complex.of_real_mul, complex.cpow_mul, complex.of_real_cpow hx];
  simp only [(complex.of_real_mul _ _).symm, (complex.of_real_log hx).symm,
    complex.of_real_im, neg_lt_zero, pi_pos, le_of_lt pi_pos]

lemma rpow_neg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ -y = (x ^ y)⁻¹ :=
by simp only [rpow_def_of_nonneg hx]; split_ifs; simp [*, exp_neg] at *

lemma rpow_sub {x : ℝ} (hx : 0 < x) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z :=
by simp only [sub_eq_add_neg, rpow_add hx, rpow_neg (le_of_lt hx), div_eq_mul_inv]

lemma rpow_sub' {x : ℝ} (hx : 0 ≤ x) {y z : ℝ} (h : y - z ≠ 0) :
  x ^ (y - z) = x ^ y / x ^ z :=
by simp only [sub_eq_add_neg, rpow_add' hx h, rpow_neg hx, div_eq_mul_inv]

@[simp] lemma rpow_nat_cast (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
by simp only [rpow_def, (complex.of_real_pow _ _).symm, complex.cpow_nat_cast,
  complex.of_real_nat_cast, complex.of_real_re]

@[simp] lemma rpow_int_cast (x : ℝ) (n : ℤ) : x ^ (n : ℝ) = x ^ n :=
by simp only [rpow_def, (complex.of_real_fpow _ _).symm, complex.cpow_int_cast,
  complex.of_real_int_cast, complex.of_real_re]

lemma rpow_neg_one (x : ℝ) : x ^ (-1 : ℝ) = x⁻¹ :=
begin
  suffices H : x ^ ((-1 : ℤ) : ℝ) = x⁻¹, by exact_mod_cast H,
  simp only [rpow_int_cast, fpow_one, fpow_neg],
end

lemma mul_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : 0 ≤ y) : (x*y)^z = x^z * y^z :=
begin
  iterate 3 { rw real.rpow_def_of_nonneg }, split_ifs; simp * at *,
  { have hx : 0 < x, cases lt_or_eq_of_le h with h₂ h₂, exact h₂, exfalso, apply h_2, exact eq.symm h₂,
    have hy : 0 < y, cases lt_or_eq_of_le h₁ with h₂ h₂, exact h₂, exfalso, apply h_3, exact eq.symm h₂,
    rw [log_mul (ne_of_gt hx) (ne_of_gt hy), add_mul, exp_add]},
  { exact h₁},
  { exact h},
  { exact mul_nonneg h h₁},
end

lemma inv_rpow (hx : 0 ≤ x) (y : ℝ) : (x⁻¹)^y = (x^y)⁻¹ :=
begin
  by_cases hy0 : y = 0, { simp [*] },
  by_cases hx0 : x = 0, { simp [*] },
  simp only [real.rpow_def_of_nonneg hx, real.rpow_def_of_nonneg (inv_nonneg.2 hx), if_false,
    hx0, mt inv_eq_zero.1 hx0, log_inv, ← neg_mul_eq_neg_mul, exp_neg]
end

lemma div_rpow (hx : 0 ≤ x) (hy : 0 ≤ y) (z : ℝ) : (x / y) ^ z = x^z / y^z :=
by simp only [div_eq_mul_inv, mul_rpow hx (inv_nonneg.2 hy), inv_rpow hy]

lemma one_le_rpow (h : 1 ≤ x) (h₁ : 0 ≤ z) : 1 ≤ x^z :=
begin
  rw real.rpow_def_of_nonneg, split_ifs with h₂ h₃,
  { refl},
  { simp [*, not_le_of_gt zero_lt_one] at *},
  { have hx : 0 < x, exact lt_of_lt_of_le zero_lt_one h,
    rw [←log_le_log zero_lt_one hx, log_one] at h,
    have pos : 0 ≤ log x * z, exact mul_nonneg h h₁,
      rwa [←exp_le_exp, exp_zero] at pos},
  { exact le_trans zero_le_one h},
end

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

lemma rpow_le_one {x z : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ 1) (hz : 0 ≤ z) : x^z ≤ 1 :=
by rw ←one_rpow z; apply rpow_le_rpow; assumption

lemma one_lt_rpow (hx : 1 < x) (hz : 0 < z) : 1 < x^z :=
by { rw ← one_rpow z, exact rpow_lt_rpow zero_le_one hx hz }

lemma rpow_lt_one (hx : 0 < x) (hx1 : x < 1) (hz : 0 < z) : x^z < 1 :=
by { rw ← one_rpow z, exact rpow_lt_rpow (le_of_lt hx) hx1 hz }

lemma pow_nat_rpow_nat_inv {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 0 < n) :
  (x ^ n) ^ (n⁻¹ : ℝ) = x :=
have hn0 : (n : ℝ) ≠ 0, by simpa [nat.pos_iff_ne_zero] using hn,
by rw [← rpow_nat_cast, ← rpow_mul hx, mul_inv_cancel hn0, rpow_one]

lemma rpow_nat_inv_pow_nat {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 0 < n) :
  (x ^ (n⁻¹ : ℝ)) ^ n = x :=
have hn0 : (n : ℝ) ≠ 0, by simpa [nat.pos_iff_ne_zero] using hn,
by rw [← rpow_nat_cast, ← rpow_mul hx, inv_mul_cancel hn0, rpow_one]

section prove_rpow_is_continuous

lemma continuous_rpow_aux1 : continuous (λp : {p:ℝ×ℝ // 0 < p.1}, p.val.1 ^ p.val.2) :=
suffices h : continuous (λ p : {p:ℝ×ℝ // 0 < p.1 }, exp (log p.val.1 * p.val.2)),
  by { convert h, ext p, rw rpow_def_of_pos p.2 },
continuous_exp.comp $
  (show continuous ((λp:{p:ℝ//0 < p}, log (p.val)) ∘ (λp:{p:ℝ×ℝ//0<p.fst}, ⟨p.val.1, p.2⟩)), from
    continuous_log'.comp $ continuous_subtype_mk _ $ continuous_fst.comp continuous_subtype_val).mul
  (continuous_snd.comp $ continuous_subtype_val.comp continuous_id)

lemma continuous_rpow_aux2 : continuous (λ p : {p:ℝ×ℝ // p.1 < 0}, p.val.1 ^ p.val.2) :=
suffices h : continuous (λp:{p:ℝ×ℝ // p.1 < 0}, exp (log (-p.val.1) * p.val.2) * cos (p.val.2 * π)),
  by { convert h, ext p, rw [rpow_def_of_neg p.2, log_neg_eq_log] },
  (continuous_exp.comp $
    (show continuous $ (λp:{p:ℝ//0<p},
            log (p.val))∘(λp:{p:ℝ×ℝ//p.1<0}, ⟨-p.val.1, neg_pos_of_neg p.2⟩),
     from continuous_log'.comp $ continuous_subtype_mk _ $ continuous_neg.comp $
            continuous_fst.comp continuous_subtype_val).mul
    (continuous_snd.comp $ continuous_subtype_val.comp continuous_id)).mul
  (continuous_cos.comp $
    (continuous_snd.comp $ continuous_subtype_val.comp continuous_id).mul continuous_const)

lemma continuous_at_rpow_of_ne_zero (hx : x ≠ 0) (y : ℝ) :
  continuous_at (λp:ℝ×ℝ, p.1^p.2) (x, y) :=
begin
  cases lt_trichotomy 0 x,
  exact continuous_within_at.continuous_at
    (continuous_on_iff_continuous_restrict.2 continuous_rpow_aux1 _ h)
    (mem_nhds_sets (by { convert is_open_prod (is_open_lt' (0:ℝ)) is_open_univ, ext, finish }) h),
  cases h,
  { exact absurd h.symm hx },
  exact continuous_within_at.continuous_at
    (continuous_on_iff_continuous_restrict.2 continuous_rpow_aux2 _ h)
    (mem_nhds_sets (by { convert is_open_prod (is_open_gt' (0:ℝ)) is_open_univ, ext, finish }) h)
end

lemma continuous_rpow_aux3 : continuous (λ p : {p:ℝ×ℝ // 0 < p.2}, p.val.1 ^ p.val.2) :=
continuous_iff_continuous_at.2 $ λ ⟨(x₀, y₀), hy₀⟩,
begin
  by_cases hx₀ : x₀ = 0,
  { simp only [continuous_at, hx₀, zero_rpow (ne_of_gt hy₀), metric.tendsto_nhds_nhds],
    assume ε ε0,
    rcases exists_pos_rat_lt (half_pos hy₀) with ⟨q, q_pos, q_lt⟩,
    let q := (q:ℝ), replace q_pos : 0 < q := rat.cast_pos.2 q_pos,
    let δ := min (min q (ε ^ (1 / q))) (1/2),
    have δ0 : 0 < δ := lt_min (lt_min q_pos (rpow_pos_of_pos ε0 _)) (by norm_num),
    have : δ ≤ q := le_trans (min_le_left _ _) (min_le_left _ _),
    have : δ ≤ ε ^ (1 / q) := le_trans (min_le_left _ _) (min_le_right _ _),
    have : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num),
    use δ, use δ0, rintros ⟨⟨x, y⟩, hy⟩,
    simp only [subtype.dist_eq, real.dist_eq, prod.dist_eq, sub_zero, subtype.coe_mk],
    assume h, rw max_lt_iff at h, cases h with xδ yy₀,
    have qy : q < y, calc q < y₀ / 2 : q_lt
      ... = y₀ - y₀ / 2 : (sub_half _).symm
      ... ≤ y₀ - δ : by linarith
      ... < y : sub_lt_of_abs_sub_lt_left yy₀,
    calc abs(x^y) ≤ abs(x)^y : abs_rpow_le_abs_rpow _ _
      ... < δ ^ y : rpow_lt_rpow (abs_nonneg _) xδ hy
      ... < δ ^ q : by { refine rpow_lt_rpow_of_exponent_gt _ _ _, repeat {linarith} }
      ... ≤ (ε ^ (1 / q)) ^ q : by { refine rpow_le_rpow _ _ _, repeat {linarith} }
      ... = ε : by { rw [← rpow_mul, div_mul_cancel, rpow_one], exact ne_of_gt q_pos, linarith }},
  { exact (continuous_within_at_iff_continuous_at_restrict (λp:ℝ×ℝ, p.1^p.2) _).1
      (continuous_at_rpow_of_ne_zero hx₀ _).continuous_within_at }
end

lemma continuous_at_rpow_of_pos (hy : 0 < y) (x : ℝ) :
  continuous_at (λp:ℝ×ℝ, p.1^p.2) (x, y) :=
continuous_within_at.continuous_at
  (continuous_on_iff_continuous_restrict.2 continuous_rpow_aux3 _ hy)
  (mem_nhds_sets (by { convert is_open_prod is_open_univ (is_open_lt' (0:ℝ)), ext, finish }) hy)

lemma continuous_at_rpow {x y : ℝ} (h : x ≠ 0 ∨ 0 < y) :
  continuous_at (λp:ℝ×ℝ, p.1^p.2) (x, y) :=
by { cases h, exact continuous_at_rpow_of_ne_zero h _, exact continuous_at_rpow_of_pos h x }

variables {α : Type*} [topological_space α] {f g : α → ℝ}

/--
`real.rpow` is continuous at all points except for the lower half of the y-axis.
In other words, the function `λp:ℝ×ℝ, p.1^p.2` is continuous at `(x, y)` if `x ≠ 0` or `y > 0`.

Multiple forms of the claim is provided in the current section.
-/
lemma continuous_rpow (h : ∀a, f a ≠ 0 ∨ 0 < g a) (hf : continuous f) (hg : continuous g):
  continuous (λa:α, (f a) ^ (g a)) :=
continuous_iff_continuous_at.2 $ λ a,
begin
  show continuous_at ((λp:ℝ×ℝ, p.1^p.2) ∘ (λa, (f a, g a))) a,
  refine continuous_at.comp _ (continuous_iff_continuous_at.1 (hf.prod_mk hg) _),
  { replace h := h a, cases h,
    { exact continuous_at_rpow_of_ne_zero h _ },
    { exact continuous_at_rpow_of_pos h _ }},
end

lemma continuous_rpow_of_ne_zero (h : ∀a, f a ≠ 0) (hf : continuous f) (hg : continuous g):
  continuous (λa:α, (f a) ^ (g a)) := continuous_rpow (λa, or.inl $ h a) hf hg

lemma continuous_rpow_of_pos (h : ∀a, 0 < g a) (hf : continuous f) (hg : continuous g):
  continuous (λa:α, (f a) ^ (g a)) := continuous_rpow (λa, or.inr $ h a) hf hg

end prove_rpow_is_continuous

section prove_rpow_is_differentiable

lemma has_deriv_at_rpow_of_pos {x : ℝ} (h : 0 < x) (p : ℝ) :
  has_deriv_at (λ x, x^p) (p * x^(p-1)) x :=
begin
  have : has_deriv_at (λ x, exp (log x * p)) (p * x^(p-1)) x,
  { convert (has_deriv_at_exp _).comp x ((has_deriv_at_log (ne_of_gt h)).mul_const p) using 1,
    field_simp [rpow_def_of_pos h, mul_sub, exp_sub, exp_log h, ne_of_gt h],
    ring },
  apply this.congr_of_mem_nhds,
  have : set.Ioi (0 : ℝ) ∈ 𝓝 x := mem_nhds_sets is_open_Ioi h,
  exact filter.eventually_of_mem this (λ y hy, rpow_def_of_pos hy _)
end

lemma has_deriv_at_rpow_of_neg {x : ℝ} (h : x < 0) (p : ℝ) :
  has_deriv_at (λ x, x^p) (p * x^(p-1)) x :=
begin
  have : has_deriv_at (λ x, exp (log x * p) * cos (p * π)) (p * x^(p-1)) x,
  { convert ((has_deriv_at_exp _).comp x ((has_deriv_at_log (ne_of_lt h)).mul_const p)).mul_const _
      using 1,
    field_simp [rpow_def_of_neg h, mul_sub, exp_sub, sub_mul, cos_sub, exp_log_of_neg h, ne_of_lt h],
    ring },
  apply this.congr_of_mem_nhds,
  have : set.Iio (0 : ℝ) ∈ 𝓝 x := mem_nhds_sets is_open_Iio h,
  exact filter.eventually_of_mem this (λ y hy, rpow_def_of_neg hy _)
end

lemma has_deriv_at_rpow {x : ℝ} (h : x ≠ 0) (p : ℝ) :
  has_deriv_at (λ x, x^p) (p * x^(p-1)) x :=
begin
  rcases lt_trichotomy x 0 with H|H|H,
  { exact has_deriv_at_rpow_of_neg H p },
  { exact (h H).elim },
  { exact has_deriv_at_rpow_of_pos H p },
end

lemma has_deriv_at_rpow_zero_of_one_le {p : ℝ} (h : 1 ≤ p) :
  has_deriv_at (λ x, x^p) (p * (0 : ℝ)^(p-1)) 0 :=
begin
  apply has_deriv_at_of_has_deriv_at_of_ne (λ x hx, has_deriv_at_rpow hx p),
  { exact (continuous_rpow_of_pos (λ _, (lt_of_lt_of_le zero_lt_one h))
      continuous_id continuous_const).continuous_at },
  { rcases le_iff_eq_or_lt.1 h with rfl|h,
    { simp [continuous_const.continuous_at] },
    { exact (continuous_const.mul (continuous_rpow_of_pos (λ _, sub_pos_of_lt h)
        continuous_id continuous_const)).continuous_at } }
end

lemma has_deriv_at_rpow_of_one_le (x : ℝ) {p : ℝ} (h : 1 ≤ p) :
  has_deriv_at (λ x, x^p) (p * x^(p-1)) x :=
begin
  by_cases hx : x = 0,
  { rw hx, exact has_deriv_at_rpow_zero_of_one_le h },
  { exact has_deriv_at_rpow hx p }
end

end prove_rpow_is_differentiable

section sqrt

lemma sqrt_eq_rpow : sqrt = λx:ℝ, x ^ (1/(2:ℝ)) :=
begin
  funext, by_cases h : 0 ≤ x,
  { rw [← mul_self_inj_of_nonneg, mul_self_sqrt h, ← pow_two, ← rpow_nat_cast, ← rpow_mul h],
    norm_num, exact sqrt_nonneg _, exact rpow_nonneg_of_nonneg h _ },
  { replace h : x < 0 := lt_of_not_ge h,
    have : 1 / (2:ℝ) * π = π / (2:ℝ), ring,
    rw [sqrt_eq_zero_of_nonpos (le_of_lt h), rpow_def_of_neg h, this, cos_pi_div_two, mul_zero] }
end

lemma continuous_sqrt : continuous sqrt :=
by rw sqrt_eq_rpow; exact continuous_rpow_of_pos (λa, by norm_num) continuous_id continuous_const

end sqrt

end real

section differentiability
open real

variables {f : ℝ → ℝ} {x f' : ℝ} {s : set ℝ} (p : ℝ)
/- Differentiability statements for the power of a function, when the function does not vanish
and the exponent is arbitrary-/

lemma has_deriv_within_at.rpow (hf : has_deriv_within_at f f' s x) (hx : f x ≠ 0) :
  has_deriv_within_at (λ y, (f y)^p) (f' * p * (f x)^(p-1)) s x :=
begin
  convert (has_deriv_at_rpow hx p).comp_has_deriv_within_at x hf using 1,
  ring
end

lemma has_deriv_at.rpow (hf : has_deriv_at f f' x) (hx : f x ≠ 0) :
  has_deriv_at (λ y, (f y)^p) (f' * p * (f x)^(p-1)) x :=
begin
  rw ← has_deriv_within_at_univ at *,
  exact hf.rpow p hx
end

lemma differentiable_within_at.rpow (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0) :
  differentiable_within_at ℝ (λx, (f x)^p) s x :=
(hf.has_deriv_within_at.rpow p hx).differentiable_within_at

@[simp] lemma differentiable_at.rpow (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  differentiable_at ℝ (λx, (f x)^p) x :=
(hf.has_deriv_at.rpow p hx).differentiable_at

lemma differentiable_on.rpow (hf : differentiable_on ℝ f s) (hx : ∀ x ∈ s, f x ≠ 0) :
  differentiable_on ℝ (λx, (f x)^p) s :=
λx h, (hf x h).rpow p (hx x h)

@[simp] lemma differentiable.rpow (hf : differentiable ℝ f) (hx : ∀ x, f x ≠ 0) :
  differentiable ℝ (λx, (f x)^p) :=
λx, (hf x).rpow p (hx x)

lemma deriv_within_rpow (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, (f x)^p) s x = (deriv_within f s x) * p * (f x)^(p-1) :=
(hf.has_deriv_within_at.rpow p hx).deriv_within hxs

@[simp] lemma deriv_rpow (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  deriv (λx, (f x)^p) x = (deriv f x) * p * (f x)^(p-1) :=
(hf.has_deriv_at.rpow p hx).deriv

/- Differentiability statements for the power of a function, when the function may vanish
but the exponent is at least one. -/

variable {p}

lemma has_deriv_within_at.rpow_of_one_le (hf : has_deriv_within_at f f' s x) (hp : 1 ≤ p) :
  has_deriv_within_at (λ y, (f y)^p) (f' * p * (f x)^(p-1)) s x :=
begin
  convert (has_deriv_at_rpow_of_one_le (f x) hp).comp_has_deriv_within_at x hf using 1,
  ring
end

lemma has_deriv_at.rpow_of_one_le (hf : has_deriv_at f f' x) (hp : 1 ≤ p) :
  has_deriv_at (λ y, (f y)^p) (f' * p * (f x)^(p-1)) x :=
begin
  rw ← has_deriv_within_at_univ at *,
  exact hf.rpow_of_one_le hp
end

lemma differentiable_within_at.rpow_of_one_le (hf : differentiable_within_at ℝ f s x) (hp : 1 ≤ p) :
  differentiable_within_at ℝ (λx, (f x)^p) s x :=
(hf.has_deriv_within_at.rpow_of_one_le hp).differentiable_within_at

@[simp] lemma differentiable_at.rpow_of_one_le (hf : differentiable_at ℝ f x) (hp : 1 ≤ p) :
  differentiable_at ℝ (λx, (f x)^p) x :=
(hf.has_deriv_at.rpow_of_one_le hp).differentiable_at

lemma differentiable_on.rpow_of_one_le (hf : differentiable_on ℝ f s) (hp : 1 ≤ p) :
  differentiable_on ℝ (λx, (f x)^p) s :=
λx h, (hf x h).rpow_of_one_le hp

@[simp] lemma differentiable.rpow_of_one_le (hf : differentiable ℝ f) (hp : 1 ≤ p) :
  differentiable ℝ (λx, (f x)^p) :=
λx, (hf x).rpow_of_one_le hp

lemma deriv_within_rpow_of_one_le (hf : differentiable_within_at ℝ f s x) (hp : 1 ≤ p)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, (f x)^p) s x = (deriv_within f s x) * p * (f x)^(p-1) :=
(hf.has_deriv_within_at.rpow_of_one_le hp).deriv_within hxs

@[simp] lemma deriv_rpow_of_one_le (hf : differentiable_at ℝ f x) (hp : 1 ≤ p) :
  deriv (λx, (f x)^p) x = (deriv f x) * p * (f x)^(p-1) :=
(hf.has_deriv_at.rpow_of_one_le hp).deriv

/- Differentiability statements for the square root of a function, when the function does not
vanish -/

lemma has_deriv_within_at.sqrt (hf : has_deriv_within_at f f' s x) (hx : f x ≠ 0) :
  has_deriv_within_at (λ y, sqrt (f y)) (f' / (2 * sqrt (f x))) s x :=
begin
  simp only [sqrt_eq_rpow],
  convert hf.rpow (1/2) hx,
  rcases lt_trichotomy (f x) 0 with H|H|H,
  { have A : (f x)^((1:ℝ)/2) = 0,
    { rw rpow_def_of_neg H,
      have : cos (1/2 * π) = 0, by { convert cos_pi_div_two using 2, ring },
      rw [this],
      simp },
    have B : f x ^ ((1:ℝ) / 2 - 1) = 0,
    { rw rpow_def_of_neg H,
      have : cos (π/2 - π) = 0, by simp [cos_sub],
      have : cos (((1:ℝ)/2 - 1) * π) = 0, by { convert this using 2, ring },
      rw this,
      simp },
    rw [A, B],
    simp },
  { exact (hx H).elim },
  { have A : 0 < (f x)^((1:ℝ)/2) := rpow_pos_of_pos H _,
    have B : (f x) ^ (-(1:ℝ)) = (f x)^(-((1:ℝ)/2)) * (f x)^(-((1:ℝ)/2)),
    { rw [← rpow_add H],
      congr,
      norm_num },
    rw [sub_eq_add_neg, rpow_add H, B, rpow_neg (le_of_lt H)],
    field_simp [hx, ne_of_gt A],
    ring }
end

lemma has_deriv_at.sqrt (hf : has_deriv_at f f' x) (hx : f x ≠ 0) :
  has_deriv_at (λ y, sqrt (f y)) (f' / (2 * sqrt(f x))) x :=
begin
  rw ← has_deriv_within_at_univ at *,
  exact hf.sqrt hx
end

lemma differentiable_within_at.sqrt (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0) :
  differentiable_within_at ℝ (λx, sqrt (f x)) s x :=
(hf.has_deriv_within_at.sqrt hx).differentiable_within_at

@[simp] lemma differentiable_at.sqrt (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  differentiable_at ℝ (λx, sqrt (f x)) x :=
(hf.has_deriv_at.sqrt hx).differentiable_at

lemma differentiable_on.sqrt (hf : differentiable_on ℝ f s) (hx : ∀ x ∈ s, f x ≠ 0) :
  differentiable_on ℝ (λx, sqrt (f x)) s :=
λx h, (hf x h).sqrt (hx x h)

@[simp] lemma differentiable.sqrt (hf : differentiable ℝ f) (hx : ∀ x, f x ≠ 0) :
  differentiable ℝ (λx, sqrt (f x)) :=
λx, (hf x).sqrt (hx x)

lemma deriv_within_sqrt (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, sqrt (f x)) s x = (deriv_within f s x) / (2 * sqrt (f x)) :=
(hf.has_deriv_within_at.sqrt hx).deriv_within hxs

@[simp] lemma deriv_sqrt (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  deriv (λx, sqrt (f x)) x = (deriv f x) / (2 * sqrt (f x)) :=
(hf.has_deriv_at.sqrt hx).deriv

end differentiability

namespace nnreal

/-- The nonnegative real power function `x^y`, defined for `x : ℝ≥0` and `y : ℝ ` as the
restriction of the real power function. For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`,
one sets `0 ^ 0 = 1` and `0 ^ y = 0` for `y ≠ 0`. -/
noncomputable def rpow (x : ℝ≥0) (y : ℝ) : ℝ≥0 :=
⟨(x : ℝ) ^ y, real.rpow_nonneg_of_nonneg x.2 y⟩

noncomputable instance : has_pow ℝ≥0 ℝ := ⟨rpow⟩

@[simp] lemma rpow_eq_pow (x : ℝ≥0) (y : ℝ) : rpow x y = x ^ y := rfl

@[simp, norm_cast] lemma coe_rpow (x : ℝ≥0) (y : ℝ) : ((x ^ y : ℝ≥0) : ℝ) = (x : ℝ) ^ y := rfl

@[simp] lemma rpow_zero (x : ℝ≥0) : x ^ (0 : ℝ) = 1 :=
nnreal.eq $ real.rpow_zero _

@[simp] lemma rpow_eq_zero_iff {x : ℝ≥0} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 :=
begin
  rw [← nnreal.coe_eq, coe_rpow, ← nnreal.coe_eq_zero],
  exact real.rpow_eq_zero_iff_of_nonneg x.2
end

@[simp] lemma zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ≥0) ^ x = 0 :=
nnreal.eq $ real.zero_rpow h

@[simp] lemma rpow_one (x : ℝ≥0) : x ^ (1 : ℝ) = x :=
nnreal.eq $ real.rpow_one _

@[simp] lemma one_rpow (x : ℝ) : (1 : ℝ≥0) ^ x = 1 :=
nnreal.eq $ real.one_rpow _

lemma rpow_add {x : ℝ≥0} (hx : x ≠ 0) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z :=
nnreal.eq $ real.rpow_add (zero_lt_iff_ne_zero.2 hx) _ _

lemma rpow_add' (x : ℝ≥0) {y z : ℝ} (h : y + z ≠ 0) : x ^ (y + z) = x ^ y * x ^ z :=
nnreal.eq $ real.rpow_add' x.2 h

lemma rpow_mul (x : ℝ≥0) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
nnreal.eq $ real.rpow_mul x.2 y z

lemma rpow_neg (x : ℝ≥0) (y : ℝ) : x ^ -y = (x ^ y)⁻¹ :=
nnreal.eq $ real.rpow_neg x.2 _

lemma rpow_neg_one (x : ℝ≥0) : x ^ (-1 : ℝ) = x ⁻¹ :=
by simp [rpow_neg]

lemma rpow_sub {x : ℝ≥0} (hx : x ≠ 0) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z :=
nnreal.eq $ real.rpow_sub (zero_lt_iff_ne_zero.2 hx) y z

lemma rpow_sub' (x : ℝ≥0) {y z : ℝ} (h : y - z ≠ 0) :
  x ^ (y - z) = x ^ y / x ^ z :=
nnreal.eq $ real.rpow_sub' x.2 h

lemma inv_rpow (x : ℝ≥0) (y : ℝ) : (x⁻¹) ^ y = (x ^ y)⁻¹ :=
nnreal.eq $ real.inv_rpow x.2 y

lemma div_rpow (x y : ℝ≥0) (z : ℝ) : (x / y) ^ z = x ^ z / y ^ z :=
nnreal.eq $ real.div_rpow x.2 y.2 z

@[simp, norm_cast] lemma rpow_nat_cast (x : ℝ≥0) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
nnreal.eq $ by simpa only [coe_rpow, coe_pow] using real.rpow_nat_cast x n

lemma mul_rpow {x y : ℝ≥0} {z : ℝ}  : (x*y)^z = x^z * y^z :=
nnreal.eq $ real.mul_rpow x.2 y.2

lemma one_le_rpow {x : ℝ≥0} {z : ℝ} (h : 1 ≤ x) (h₁ : 0 ≤ z) : 1 ≤ x^z :=
real.one_le_rpow h h₁

lemma rpow_le_rpow {x y : ℝ≥0} {z: ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x^z ≤ y^z :=
real.rpow_le_rpow x.2 h₁ h₂

lemma rpow_lt_rpow {x y : ℝ≥0} {z: ℝ} (h₁ : x < y) (h₂ : 0 < z) : x^z < y^z :=
real.rpow_lt_rpow x.2 h₁ h₂

lemma rpow_lt_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
real.rpow_lt_rpow_iff x.2 y.2 hz

lemma rpow_le_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
real.rpow_le_rpow_iff x.2 y.2 hz

lemma rpow_lt_rpow_of_exponent_lt {x : ℝ≥0} {y z : ℝ} (hx : 1 < x) (hyz : y < z) : x^y < x^z :=
real.rpow_lt_rpow_of_exponent_lt hx hyz

lemma rpow_le_rpow_of_exponent_le {x : ℝ≥0} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) : x^y ≤ x^z :=
real.rpow_le_rpow_of_exponent_le hx hyz

lemma rpow_lt_rpow_of_exponent_gt {x : ℝ≥0} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
  x^y < x^z :=
real.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz

lemma rpow_le_rpow_of_exponent_ge {x : ℝ≥0} {y z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) :
  x^y ≤ x^z :=
real.rpow_le_rpow_of_exponent_ge hx0 hx1 hyz

lemma rpow_le_one {x : ℝ≥0} {z : ℝ} (hx2 : x ≤ 1) (hz : 0 ≤ z) : x^z ≤ 1 :=
real.rpow_le_one x.2 hx2 hz

lemma one_lt_rpow {x : ℝ≥0} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x^z :=
real.one_lt_rpow hx hz

lemma rpow_lt_one {x : ℝ≥0} {z : ℝ} (hx : 0 < x) (hx1 : x < 1) (hz : 0 < z) : x^z < 1 :=
real.rpow_lt_one hx hx1 hz

lemma pow_nat_rpow_nat_inv (x : ℝ≥0) {n : ℕ} (hn : 0 < n) :
  (x ^ n) ^ (n⁻¹ : ℝ) = x :=
by { rw [← nnreal.coe_eq, coe_rpow, nnreal.coe_pow], exact real.pow_nat_rpow_nat_inv x.2 hn }

lemma rpow_nat_inv_pow_nat (x : ℝ≥0) {n : ℕ} (hn : 0 < n) :
  (x ^ (n⁻¹ : ℝ)) ^ n = x :=
by { rw [← nnreal.coe_eq, nnreal.coe_pow, coe_rpow], exact real.rpow_nat_inv_pow_nat x.2 hn }

lemma continuous_at_rpow {x : ℝ≥0} {y : ℝ} (h : x ≠ 0 ∨ 0 < y) :
  continuous_at (λp:ℝ≥0×ℝ, p.1^p.2) (x, y) :=
begin
  have : (λp:ℝ≥0×ℝ, p.1^p.2) = nnreal.of_real ∘ (λp:ℝ×ℝ, p.1^p.2) ∘ (λp:ℝ≥0 × ℝ, (p.1.1, p.2)),
  { ext p,
    rw [coe_rpow, nnreal.coe_of_real _ (real.rpow_nonneg_of_nonneg p.1.2 _)],
    refl },
  rw this,
  refine nnreal.continuous_of_real.continuous_at.comp (continuous_at.comp _ _),
  { apply real.continuous_at_rpow,
    simp at h,
    rw ← (nnreal.coe_eq_zero x) at h,
    exact h },
  { exact ((continuous_subtype_val.comp continuous_fst).prod_mk continuous_snd).continuous_at }
end

end nnreal

open filter

lemma filter.tendsto.nnrpow {α : Type*} {f : filter α} {u : α → ℝ≥0} {v : α → ℝ} {x : ℝ≥0} {y : ℝ}
  (hx : tendsto u f (𝓝 x)) (hy : tendsto v f (𝓝 y)) (h : x ≠ 0 ∨ 0 < y) :
  tendsto (λ a, (u a) ^ (v a)) f (𝓝 (x ^ y)) :=
tendsto.comp (nnreal.continuous_at_rpow h) (tendsto.prod_mk_nhds hx hy)

namespace ennreal

/-- The real power function `x^y` on extended nonnegative reals, defined for `x : ennreal` and
`y : ℝ` as the restriction of the real power function if `0 < x < ⊤`, and with the natural values
for `0` and `⊤` (i.e., `0 ^ x = 0` for `x > 0`, `1` for `x = 0` and `⊤` for `x < 0`, and
`⊤ ^ x = 1 / 0 ^ x`). -/
noncomputable def rpow : ennreal → ℝ → ennreal
| (some x) y := if x = 0 ∧ y < 0 then ⊤ else (x ^ y : ℝ≥0)
| none     y := if 0 < y then ⊤ else if y = 0 then 1 else 0

noncomputable instance : has_pow ennreal ℝ := ⟨rpow⟩

@[simp] lemma rpow_eq_pow (x : ennreal) (y : ℝ) : rpow x y = x ^ y := rfl

@[simp] lemma rpow_zero {x : ennreal} : x ^ (0 : ℝ) = 1 :=
by cases x; { dsimp only [(^), rpow], simp [lt_irrefl] }

lemma top_rpow_def (y : ℝ) : (⊤ : ennreal) ^ y = if 0 < y then ⊤ else if y = 0 then 1 else 0 :=
rfl

@[simp] lemma top_rpow_of_pos {y : ℝ} (h : 0 < y) : (⊤ : ennreal) ^ y = ⊤ :=
by simp [top_rpow_def, h]

@[simp] lemma top_rpow_of_neg {y : ℝ} (h : y < 0) : (⊤ : ennreal) ^ y = 0 :=
by simp [top_rpow_def, asymm h, ne_of_lt h]

@[simp] lemma zero_rpow_of_pos {y : ℝ} (h : 0 < y) : (0 : ennreal) ^ y = 0 :=
begin
  rw [← ennreal.coe_zero, ← ennreal.some_eq_coe],
  dsimp only [(^), rpow],
  simp [h, asymm h, ne_of_gt h],
end

@[simp] lemma zero_rpow_of_neg {y : ℝ} (h : y < 0) : (0 : ennreal) ^ y = ⊤ :=
begin
  rw [← ennreal.coe_zero, ← ennreal.some_eq_coe],
  dsimp only [(^), rpow],
  simp [h, ne_of_gt h],
end

lemma zero_rpow_def (y : ℝ) : (0 : ennreal) ^ y = if 0 < y then 0 else if y = 0 then 1 else ⊤ :=
begin
  rcases lt_trichotomy 0 y with H|rfl|H,
  { simp [H, ne_of_gt, zero_rpow_of_pos, lt_irrefl] },
  { simp [lt_irrefl] },
  { simp [H, asymm H, ne_of_lt, zero_rpow_of_neg] }
end

@[norm_cast] lemma coe_rpow_of_ne_zero {x : ℝ≥0} (h : x ≠ 0) (y : ℝ) :
  (x : ennreal) ^ y = (x ^ y : ℝ≥0) :=
begin
  rw [← ennreal.some_eq_coe],
  dsimp only [(^), rpow],
  simp [h]
end

@[norm_cast] lemma coe_rpow_of_nonneg (x : ℝ≥0) {y : ℝ} (h : 0 ≤ y) :
  (x : ennreal) ^ y = (x ^ y : ℝ≥0) :=
begin
  by_cases hx : x = 0,
  { rcases le_iff_eq_or_lt.1 h with H|H,
    { simp [hx, H.symm] },
    { simp [hx, zero_rpow_of_pos H, nnreal.zero_rpow (ne_of_gt H)] } },
  { exact coe_rpow_of_ne_zero hx _ }
end

@[simp] lemma rpow_one (x : ennreal) : x ^ (1 : ℝ) = x :=
by cases x; dsimp only [(^), rpow]; simp [zero_lt_one, not_lt_of_le zero_le_one]

@[simp] lemma one_rpow (x : ℝ) : (1 : ennreal) ^ x = 1 :=
by { rw [← coe_one, coe_rpow_of_ne_zero one_ne_zero], simp }

@[simp] lemma rpow_eq_zero_iff {x : ennreal} {y : ℝ} :
  x ^ y = 0 ↔ (x = 0 ∧ 0 < y) ∨ (x = ⊤ ∧ y < 0) :=
begin
  cases x,
  { rcases lt_trichotomy y 0 with H|H|H;
    simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt] },
  { by_cases h : x = 0,
    { rcases lt_trichotomy y 0 with H|H|H;
      simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt] },
    { simp [coe_rpow_of_ne_zero h, h] } }
end

@[simp] lemma rpow_eq_top_iff {x : ennreal} {y : ℝ} :
  x ^ y = ⊤ ↔ (x = 0 ∧ y < 0) ∨ (x = ⊤ ∧ 0 < y) :=
begin
  cases x,
  { rcases lt_trichotomy y 0 with H|H|H;
    simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt] },
  { by_cases h : x = 0,
    { rcases lt_trichotomy y 0 with H|H|H;
      simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt] },
    { simp [coe_rpow_of_ne_zero h, h] } }
end

lemma rpow_add {x : ennreal} (y z : ℝ) (hx : x ≠ 0) (h'x : x ≠ ⊤) : x ^ (y + z) = x ^ y * x ^ z :=
begin
  cases x, { exact (h'x rfl).elim },
  have : x ≠ 0 := λ h, by simpa [h] using hx,
  simp [coe_rpow_of_ne_zero this, nnreal.rpow_add this]
end

lemma rpow_neg (x : ennreal) (y : ℝ) : x ^ -y = (x ^ y)⁻¹ :=
begin
  cases x,
  { rcases lt_trichotomy y 0 with H|H|H;
    simp [top_rpow_of_pos, top_rpow_of_neg, H, neg_pos.mpr] },
  { by_cases h : x = 0,
    { rcases lt_trichotomy y 0 with H|H|H;
      simp [h, zero_rpow_of_pos, zero_rpow_of_neg, H, neg_pos.mpr] },
    { have A : x ^ y ≠ 0, by simp [h],
      simp [coe_rpow_of_ne_zero h, ← coe_inv A, nnreal.rpow_neg] } }
end

lemma rpow_neg_one (x : ennreal) : x ^ (-1 : ℝ) = x ⁻¹ :=
by simp [rpow_neg]

lemma rpow_mul (x : ennreal) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
begin
  cases x,
  { rcases lt_trichotomy y 0 with Hy|Hy|Hy;
    rcases lt_trichotomy z 0 with Hz|Hz|Hz;
    simp [Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
          mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg] },
  { by_cases h : x = 0,
    { rcases lt_trichotomy y 0 with Hy|Hy|Hy;
      rcases lt_trichotomy z 0 with Hz|Hz|Hz;
      simp [h, Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
            mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg] },
    { have : x ^ y ≠ 0, by simp [h],
      simp [coe_rpow_of_ne_zero h, coe_rpow_of_ne_zero this, nnreal.rpow_mul] } }
end

@[simp, norm_cast] lemma rpow_nat_cast (x : ennreal) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
begin
  cases x,
  { cases n;
    simp [top_rpow_of_pos (nat.cast_add_one_pos _), top_pow (nat.succ_pos _)] },
  { simp [coe_rpow_of_nonneg _ (nat.cast_nonneg n)] }
end

@[norm_cast] lemma coe_mul_rpow (x y : ℝ≥0) (z : ℝ) :
  ((x : ennreal) * y) ^ z = x^z * y^z :=
begin
  rcases lt_trichotomy z 0 with H|H|H,
  { by_cases hx : x = 0; by_cases hy : y = 0,
    { simp [hx, hy, zero_rpow_of_neg, H] },
    { have : (y : ennreal) ^ z ≠ 0, by simp [rpow_eq_zero_iff, hy],
      simp [hx, hy, zero_rpow_of_neg, H, with_top.top_mul this] },
    { have : (x : ennreal) ^ z ≠ 0, by simp [rpow_eq_zero_iff, hx],
      simp [hx, hy, zero_rpow_of_neg H, with_top.mul_top this] },
    { rw [← coe_mul, coe_rpow_of_ne_zero, nnreal.mul_rpow, coe_mul,
          coe_rpow_of_ne_zero hx, coe_rpow_of_ne_zero hy],
      simp [hx, hy] } },
  { simp [H] },
  { by_cases hx : x = 0; by_cases hy : y = 0,
    { simp [hx, hy, zero_rpow_of_pos, H] },
    { have : (y : ennreal) ^ z ≠ 0, by simp [rpow_eq_zero_iff, hy],
      simp [hx, hy, zero_rpow_of_pos H, with_top.top_mul this] },
    { have : (x : ennreal) ^ z ≠ 0, by simp [rpow_eq_zero_iff, hx],
      simp [hx, hy, zero_rpow_of_pos H, with_top.mul_top this] },
    { rw [← coe_mul, coe_rpow_of_ne_zero, nnreal.mul_rpow, coe_mul,
          coe_rpow_of_ne_zero hx, coe_rpow_of_ne_zero hy],
      simp [hx, hy] } },
end

lemma mul_rpow_of_ne_top {x y : ennreal} (hx : x ≠ ⊤) (hy : y ≠ ⊤) (z : ℝ) :
  (x * y) ^ z = x^z * y^z :=
begin
  lift x to ℝ≥0 using hx,
  lift y to ℝ≥0 using hy,
  exact coe_mul_rpow x y z
end

lemma mul_rpow_of_ne_zero {x y : ennreal} (hx : x ≠ 0) (hy : y ≠ 0) (z : ℝ) :
  (x * y) ^ z = x ^ z * y ^ z :=
begin
  rcases lt_trichotomy z 0 with H|H|H,
  { cases x; cases y,
    { simp [hx, hy, top_rpow_of_neg, H] },
    { have : y ≠ 0, by simpa using hy,
      simp [hx, hy, top_rpow_of_neg, H, rpow_eq_zero_iff, this] },
    { have : x ≠ 0, by simpa using hx,
      simp [hx, hy, top_rpow_of_neg, H, rpow_eq_zero_iff, this] },
    { have hx' : x ≠ 0, by simpa using hx,
      have hy' : y ≠ 0, by simpa using hy,
      simp only [some_eq_coe],
      rw [← coe_mul, coe_rpow_of_ne_zero, nnreal.mul_rpow, coe_mul,
          coe_rpow_of_ne_zero hx', coe_rpow_of_ne_zero hy'],
      simp [hx', hy'] } },
  { simp [H] },
  { cases x; cases y,
    { simp [hx, hy, top_rpow_of_pos, H] },
    { have : y ≠ 0, by simpa using hy,
      simp [hx, hy, top_rpow_of_pos, H, rpow_eq_zero_iff, this] },
    { have : x ≠ 0, by simpa using hx,
      simp [hx, hy, top_rpow_of_pos, H, rpow_eq_zero_iff, this] },
    { have hx' : x ≠ 0, by simpa using hx,
      have hy' : y ≠ 0, by simpa using hy,
      simp only [some_eq_coe],
      rw [← coe_mul, coe_rpow_of_ne_zero, nnreal.mul_rpow, coe_mul,
          coe_rpow_of_ne_zero hx', coe_rpow_of_ne_zero hy'],
      simp [hx', hy'] } }
end

lemma mul_rpow_of_nonneg (x y : ennreal) {z : ℝ} (hz : 0 ≤ z) :
  (x * y) ^ z = x ^ z * y ^ z :=
begin
  rcases le_iff_eq_or_lt.1 hz with H|H, { simp [← H] },
  by_cases h : x = 0 ∨ y = 0,
  { cases h; simp [h, zero_rpow_of_pos H] },
  push_neg at h,
  exact mul_rpow_of_ne_zero h.1 h.2 z
end

lemma one_le_rpow {x : ennreal} {z : ℝ} (h : 1 ≤ x) (h₁ : 0 ≤ z) : 1 ≤ x^z :=
begin
  cases x,
  { rcases le_iff_eq_or_lt.1 h₁ with H|H,
    { simp [← H, le_refl] },
    { simp [top_rpow_of_pos H] } },
  { simp only [one_le_coe_iff, some_eq_coe] at h,
    simp [coe_rpow_of_nonneg _ h₁, nnreal.one_le_rpow h h₁] }
end

lemma rpow_le_rpow {x y : ennreal} {z : ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x^z ≤ y^z :=
begin
  rcases le_iff_eq_or_lt.1 h₂ with H|H, { simp [← H, le_refl] },
  cases y, { simp [top_rpow_of_pos H] },
  cases x, { exact (not_top_le_coe h₁).elim },
  simp at h₁,
  simp [coe_rpow_of_nonneg _ h₂, nnreal.rpow_le_rpow h₁ h₂]
end

lemma rpow_lt_rpow {x y : ennreal} {z : ℝ} (h₁ : x < y) (h₂ : 0 < z) : x^z < y^z :=
begin
  cases x, { exact (not_top_lt h₁).elim },
  cases y, { simp [top_rpow_of_pos h₂, coe_rpow_of_nonneg _ (le_of_lt h₂)] },
  simp at h₁,
  simp [coe_rpow_of_nonneg _ (le_of_lt h₂), nnreal.rpow_lt_rpow h₁ h₂]
end

lemma rpow_lt_rpow_of_exponent_lt {x : ennreal} {y z : ℝ} (hx : 1 < x) (hx' : x ≠ ⊤) (hyz : y < z) :
  x^y < x^z :=
begin
  lift x to ℝ≥0 using hx',
  rw [one_lt_coe_iff] at hx,
  simp [coe_rpow_of_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)),
        nnreal.rpow_lt_rpow_of_exponent_lt hx hyz]
end

lemma rpow_le_rpow_of_exponent_le {x : ennreal} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) : x^y ≤ x^z :=
begin
  cases x,
  { rcases lt_trichotomy y 0 with Hy|Hy|Hy;
    rcases lt_trichotomy z 0 with Hz|Hz|Hz;
    simp [Hy, Hz, top_rpow_of_neg, top_rpow_of_pos, le_refl];
    linarith },
  { simp only [one_le_coe_iff, some_eq_coe] at hx,
    simp [coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
          nnreal.rpow_le_rpow_of_exponent_le hx hyz] }
end

lemma rpow_lt_rpow_of_exponent_gt {x : ennreal} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
  x^y < x^z :=
begin
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx1 le_top),
  simp at hx0 hx1,
  simp [coe_rpow_of_ne_zero (ne_of_gt hx0), nnreal.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz]
end

lemma rpow_le_rpow_of_exponent_ge {x : ennreal} {y z : ℝ} (hx1 : x ≤ 1) (hyz : z ≤ y) :
  x^y ≤ x^z :=
begin
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx1 coe_lt_top),
  by_cases h : x = 0,
  { rcases lt_trichotomy y 0 with Hy|Hy|Hy;
    rcases lt_trichotomy z 0 with Hz|Hz|Hz;
    simp [Hy, Hz, h, zero_rpow_of_neg, zero_rpow_of_pos, le_refl];
    linarith },
  { simp at hx1,
    simp [coe_rpow_of_ne_zero h,
          nnreal.rpow_le_rpow_of_exponent_ge (bot_lt_iff_ne_bot.mpr h) hx1 hyz] }
end

lemma rpow_le_one {x : ennreal} {z : ℝ} (hx2 : x ≤ 1) (hz : 0 ≤ z) : x^z ≤ 1 :=
begin
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx2 coe_lt_top),
  simp at hx2,
  simp [coe_rpow_of_nonneg _ hz, nnreal.rpow_le_one hx2 hz]
end

lemma one_lt_rpow {x : ennreal} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x^z :=
begin
  cases x,
  { simp [top_rpow_of_pos hz],
    exact coe_lt_top },
  { simp at hx,
    simp [coe_rpow_of_nonneg _ (le_of_lt hz), nnreal.one_lt_rpow hx hz] }
end

lemma rpow_lt_one {x : ennreal} {z : ℝ} (hx1 : x < 1) (hz : 0 < z) : x^z < 1 :=
begin
  by_cases h : x = 0,
  { simp [h, zero_rpow_of_pos hz, ennreal.zero_lt_one] },
  { lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx1 le_top),
    simp at h hx1,
    have : 0 < x := bot_lt_iff_ne_bot.mpr h,
    simp [coe_rpow_of_nonneg _ (le_of_lt hz), nnreal.rpow_lt_one this hx1 hz] }
end

lemma to_real_rpow (x : ennreal) (z : ℝ) :
  (x.to_real) ^ z = (x ^ z).to_real :=
begin
  rcases lt_trichotomy z 0 with H|H|H,
  { cases x, { simp [H, ne_of_lt] },
    by_cases hx : x = 0,
    { simp [hx, H, ne_of_lt] },
    { simp [coe_rpow_of_ne_zero hx] } },
  { simp [H] },
  { cases x, { simp [H, ne_of_gt] },
    simp [coe_rpow_of_nonneg _ (le_of_lt H)] }
end

end ennreal
