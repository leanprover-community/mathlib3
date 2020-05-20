/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel
-/
import analysis.special_functions.trigonometric

/-!
# Power function on `ℂ`, `ℝ` and `ℝ⁺`

We construct the power functions `x ^ y` where `x` and `y` are complex numbers, or `x` and `y` are
real numbers, or `x` is a nonnegative real and `y` is real, and prove their basic properties.
-/

noncomputable theory

open_locale classical real topological_space

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
else by rw [cpow_def, if_neg (@one_ne_zero ℂ _), if_neg hx, mul_one, exp_log hx]

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

@[simp] lemma cpow_nat_cast (x : ℂ) : ∀ (n : ℕ), x ^ (n : ℂ) = x ^ n
| 0       := by simp
| (n + 1) := if hx : x = 0 then by simp only [hx, pow_succ,
    complex.zero_cpow (nat.cast_ne_zero.2 (nat.succ_ne_zero _)), zero_mul]
  else by simp [cpow_def, hx, mul_comm, mul_add, exp_add, pow_succ, (cpow_nat_cast n).symm,
    exp_log hx]

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

lemma rpow_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y :=
by rw [rpow_def_of_nonneg hx];
  split_ifs; simp only [zero_le_one, le_refl, le_of_lt (exp_pos _)]

lemma rpow_add {x : ℝ} (y z : ℝ) (hx : 0 < x) : x ^ (y + z) = x ^ y * x ^ z :=
by simp only [rpow_def_of_pos hx, mul_add, exp_add]

lemma rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
by rw [← complex.of_real_inj, complex.of_real_cpow (rpow_nonneg_of_nonneg hx _),
    complex.of_real_cpow hx, complex.of_real_mul, complex.cpow_mul, complex.of_real_cpow hx];
  simp only [(complex.of_real_mul _ _).symm, (complex.of_real_log hx).symm,
    complex.of_real_im, neg_lt_zero, pi_pos, le_of_lt pi_pos]

lemma rpow_neg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ -y = (x ^ y)⁻¹ :=
by simp only [rpow_def_of_nonneg hx]; split_ifs; simp [*, exp_neg] at *

@[simp] lemma rpow_nat_cast (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
by simp only [rpow_def, (complex.of_real_pow _ _).symm, complex.cpow_nat_cast,
  complex.of_real_nat_cast, complex.of_real_re]

@[simp] lemma rpow_int_cast (x : ℝ) (n : ℤ) : x ^ (n : ℝ) = x ^ n :=
by simp only [rpow_def, (complex.of_real_fpow _ _).symm, complex.cpow_int_cast,
  complex.of_real_int_cast, complex.of_real_re]

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

lemma one_le_rpow {x z : ℝ} (h : 1 ≤ x) (h₁ : 0 ≤ z) : 1 ≤ x^z :=
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

lemma rpow_le_rpow {x y z: ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x^z ≤ y^z :=
begin
  rw le_iff_eq_or_lt at h h₂, cases h₂,
  { rw [←h₂, rpow_zero, rpow_zero]},
  { cases h,
    { rw [←h, zero_rpow], rw real.rpow_def_of_nonneg, split_ifs,
      { exact zero_le_one},
      { refl},
      { exact le_of_lt (exp_pos (log y * z))},
      { rwa ←h at h₁},
      { exact ne.symm (ne_of_lt h₂)}},
    { have one_le : 1 ≤ y / x, rw one_le_div_iff_le h, exact h₁,
      have one_le_pow : 1 ≤ (y / x)^z, exact one_le_rpow one_le (le_of_lt h₂),
      rw [←mul_div_cancel y (ne.symm (ne_of_lt h)), mul_comm, mul_div_assoc],
      rw [mul_rpow (le_of_lt h) (le_trans zero_le_one one_le), mul_comm],
      exact (le_mul_of_ge_one_left (rpow_nonneg_of_nonneg (le_of_lt h) z) one_le_pow) } }
end

lemma rpow_lt_rpow (hx : 0 ≤ x) (hxy : x < y) (hz : 0 < z) : x^z < y^z :=
begin
  rw le_iff_eq_or_lt at hx, cases hx,
  { rw [← hx, zero_rpow (ne_of_gt hz)], exact rpow_pos_of_pos (by rwa ← hx at hxy) _ },
  rw [rpow_def_of_pos hx, rpow_def_of_pos (lt_trans hx hxy), exp_lt_exp],
  exact mul_lt_mul_of_pos_right (log_lt_log hx hxy) hz
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

lemma rpow_le_one {x e : ℝ} (he : 0 ≤ e) (hx : 0 ≤ x) (hx2 : x ≤ 1) : x^e ≤ 1 :=
by rw ←one_rpow e; apply rpow_le_rpow; assumption

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

namespace nnreal

/-- The nonnegative real power function `x^y`, defined for `x : nnreal` and `y : ℝ ` as the
restriction of the real power function. For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`,
one sets `0 ^ 0 = 1` and `0 ^ y = 0` for `y ≠ 0`. -/
noncomputable def rpow (x : nnreal) (y : ℝ) : nnreal :=
⟨(x : ℝ) ^ y, real.rpow_nonneg_of_nonneg x.2 y⟩

noncomputable instance : has_pow nnreal ℝ := ⟨rpow⟩

@[simp] lemma rpow_eq_pow (x : nnreal) (y : ℝ) : rpow x y = x ^ y := rfl

@[simp, norm_cast] lemma coe_rpow (x : nnreal) (y : ℝ) : ((x ^ y : nnreal) : ℝ) = (x : ℝ) ^ y := rfl

@[simp] lemma rpow_zero (x : nnreal) : x ^ (0 : ℝ) = 1 :=
by { rw ← nnreal.coe_eq, exact real.rpow_zero _ }

@[simp] lemma rpow_eq_zero_iff {x : nnreal} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 :=
begin
  rw [← nnreal.coe_eq, coe_rpow, ← nnreal.coe_eq_zero],
  exact real.rpow_eq_zero_iff_of_nonneg x.2
end

@[simp] lemma zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : nnreal) ^ x = 0 :=
by { rw ← nnreal.coe_eq, exact real.zero_rpow h }

@[simp] lemma rpow_one (x : nnreal) : x ^ (1 : ℝ) = x :=
by { rw ← nnreal.coe_eq, exact real.rpow_one _ }

@[simp] lemma one_rpow (x : ℝ) : (1 : nnreal) ^ x = 1 :=
by { rw ← nnreal.coe_eq, exact real.one_rpow _ }

lemma rpow_add {x : nnreal} (y z : ℝ) (hx : 0 < x) : x ^ (y + z) = x ^ y * x ^ z :=
by { rw ← nnreal.coe_eq, exact real.rpow_add _ _ hx }

lemma rpow_mul (x : nnreal) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
by { rw ← nnreal.coe_eq, exact real.rpow_mul x.2 y z }

lemma rpow_neg (x : nnreal) (y : ℝ) : x ^ -y = (x ^ y)⁻¹ :=
by { rw ← nnreal.coe_eq, exact real.rpow_neg x.2 _ }

@[simp] lemma rpow_nat_cast (x : nnreal) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
by { rw [← nnreal.coe_eq, nnreal.coe_pow], exact real.rpow_nat_cast (x : ℝ) n }

lemma mul_rpow {x y : nnreal} {z : ℝ}  : (x*y)^z = x^z * y^z :=
by { rw ← nnreal.coe_eq, exact real.mul_rpow x.2 y.2 }

lemma one_le_rpow {x : nnreal} {z : ℝ} (h : 1 ≤ x) (h₁ : 0 ≤ z) : 1 ≤ x^z :=
real.one_le_rpow h h₁

lemma rpow_le_rpow {x y : nnreal} {z: ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x^z ≤ y^z :=
real.rpow_le_rpow x.2 h₁ h₂

lemma rpow_lt_rpow {x y : nnreal} {z: ℝ} (h₁ : x < y) (h₂ : 0 < z) : x^z < y^z :=
real.rpow_lt_rpow x.2 h₁ h₂

lemma rpow_lt_rpow_of_exponent_lt {x : nnreal} {y z : ℝ} (hx : 1 < x) (hyz : y < z) : x^y < x^z :=
real.rpow_lt_rpow_of_exponent_lt hx hyz

lemma rpow_le_rpow_of_exponent_le {x : nnreal} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) : x^y ≤ x^z :=
real.rpow_le_rpow_of_exponent_le hx hyz

lemma rpow_lt_rpow_of_exponent_gt {x : nnreal} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
  x^y < x^z :=
real.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz

lemma rpow_le_rpow_of_exponent_ge {x : nnreal} {y z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) :
  x^y ≤ x^z :=
real.rpow_le_rpow_of_exponent_ge hx0 hx1 hyz

lemma rpow_le_one {x : nnreal} {e : ℝ} (he : 0 ≤ e) (hx2 : x ≤ 1) : x^e ≤ 1 :=
real.rpow_le_one he x.2 hx2

lemma one_lt_rpow {x : nnreal} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x^z :=
real.one_lt_rpow hx hz

lemma rpow_lt_one {x : nnreal} {z : ℝ} (hx : 0 < x) (hx1 : x < 1) (hz : 0 < z) : x^z < 1 :=
real.rpow_lt_one hx hx1 hz

lemma pow_nat_rpow_nat_inv (x : nnreal) {n : ℕ} (hn : 0 < n) :
  (x ^ n) ^ (n⁻¹ : ℝ) = x :=
by { rw [← nnreal.coe_eq, coe_rpow, nnreal.coe_pow], exact real.pow_nat_rpow_nat_inv x.2 hn }

lemma rpow_nat_inv_pow_nat (x : nnreal) {n : ℕ} (hn : 0 < n) :
  (x ^ (n⁻¹ : ℝ)) ^ n = x :=
by { rw [← nnreal.coe_eq, nnreal.coe_pow, coe_rpow], exact real.rpow_nat_inv_pow_nat x.2 hn }

lemma continuous_at_rpow {x : nnreal} {y : ℝ} (h : x ≠ 0 ∨ 0 < y) :
  continuous_at (λp:nnreal×ℝ, p.1^p.2) (x, y) :=
begin
  have : (λp:nnreal×ℝ, p.1^p.2) = nnreal.of_real ∘ (λp:ℝ×ℝ, p.1^p.2) ∘ (λp:nnreal × ℝ, (p.1.1, p.2)),
  { ext p,
    rw [← nnreal.coe_eq, coe_rpow, nnreal.coe_of_real _ (real.rpow_nonneg_of_nonneg p.1.2 _)],
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

lemma filter.tendsto.nnrpow {α : Type*} {f : filter α} {u : α → nnreal} {v : α → ℝ} {x : nnreal} {y : ℝ}
  (hx : tendsto u f (𝓝 x)) (hy : tendsto v f (𝓝 y)) (h : x ≠ 0 ∨ 0 < y) :
  tendsto (λ a, (u a) ^ (v a)) f (𝓝 (x ^ y)) :=
tendsto.comp (nnreal.continuous_at_rpow h) (tendsto.prod_mk_nhds hx hy)
