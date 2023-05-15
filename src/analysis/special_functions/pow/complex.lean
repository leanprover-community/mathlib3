/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
import analysis.special_functions.complex.log

/-! # Power function on `ℂ`

We construct the power functions `x ^ y`, where `x` and `y` are complex numbers.
-/

open_locale classical real topology filter complex_conjugate
open filter finset set

namespace complex

/-- The complex power function `x ^ y`, given by `x ^ y = exp(y log x)` (where `log` is the
principal determination of the logarithm), unless `x = 0` where one sets `0 ^ 0 = 1` and
`0 ^ y = 0` for `y ≠ 0`. -/
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

lemma cpow_def_of_ne_zero {x : ℂ} (hx : x ≠ 0) (y : ℂ) : x ^ y = exp (log x * y) := if_neg hx

@[simp] lemma cpow_zero (x : ℂ) : x ^ (0 : ℂ) = 1 := by simp [cpow_def]

@[simp] lemma cpow_eq_zero_iff (x y : ℂ) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 :=
by { simp only [cpow_def], split_ifs; simp [*, exp_ne_zero] }

@[simp] lemma zero_cpow {x : ℂ} (h : x ≠ 0) : (0 : ℂ) ^ x = 0 :=
by simp [cpow_def, *]

lemma zero_cpow_eq_iff {x : ℂ} {a : ℂ} : 0 ^ x = a ↔ (x ≠ 0 ∧ a = 0) ∨ (x = 0 ∧ a = 1) :=
begin
  split,
  { intros hyp,
    simp only [cpow_def, eq_self_iff_true, if_true] at hyp,
    by_cases x = 0,
    { subst h, simp only [if_true, eq_self_iff_true] at hyp, right, exact ⟨rfl, hyp.symm⟩},
    { rw if_neg h at hyp, left, exact ⟨h, hyp.symm⟩, }, },
  { rintro (⟨h, rfl⟩|⟨rfl,rfl⟩),
    { exact zero_cpow h, },
    { exact cpow_zero _, }, },
end

lemma eq_zero_cpow_iff {x : ℂ} {a : ℂ} : a = 0 ^ x ↔ (x ≠ 0 ∧ a = 0) ∨ (x = 0 ∧ a = 1) :=
by rw [←zero_cpow_eq_iff, eq_comm]

@[simp] lemma cpow_one (x : ℂ) : x ^ (1 : ℂ) = x :=
if hx : x = 0 then by simp [hx, cpow_def]
else by rw [cpow_def, if_neg (one_ne_zero : (1 : ℂ) ≠ 0), if_neg hx, mul_one, exp_log hx]

@[simp] lemma one_cpow (x : ℂ) : (1 : ℂ) ^ x = 1 :=
by rw cpow_def; split_ifs; simp [one_ne_zero, *] at *

lemma cpow_add {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y + z) = x ^ y * x ^ z :=
by simp only [cpow_def, ite_mul, boole_mul, mul_ite, mul_boole]; simp [*, exp_add, mul_add] at *

lemma cpow_mul {x y : ℂ} (z : ℂ) (h₁ : -π < (log x * y).im) (h₂ : (log x * y).im ≤ π) :
  x ^ (y * z) = (x ^ y) ^ z :=
begin
  simp only [cpow_def],
  split_ifs;
  simp [*, exp_ne_zero, log_exp h₁ h₂, mul_assoc] at *
end

lemma cpow_neg (x y : ℂ) : x ^ -y = (x ^ y)⁻¹ :=
by simp only [cpow_def, neg_eq_zero, mul_neg]; split_ifs; simp [exp_neg]

lemma cpow_sub {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y - z) = x ^ y / x ^ z :=
by rw [sub_eq_add_neg, cpow_add _ _ hx, cpow_neg, div_eq_mul_inv]

lemma cpow_neg_one (x : ℂ) : x ^ (-1 : ℂ) = x⁻¹ :=
by simpa using cpow_neg x 1

@[simp, norm_cast] lemma cpow_nat_cast (x : ℂ) : ∀ (n : ℕ), x ^ (n : ℂ) = x ^ n
| 0       := by simp
| (n + 1) := if hx : x = 0 then by simp only [hx, pow_succ,
    complex.zero_cpow (nat.cast_ne_zero.2 (nat.succ_ne_zero _)), zero_mul]
  else by simp [cpow_add, hx, pow_add, cpow_nat_cast n]

@[simp] lemma cpow_two (x : ℂ) : x ^ (2 : ℂ) = x ^ 2 :=
by { rw ← cpow_nat_cast, simp only [nat.cast_bit0, nat.cast_one] }

@[simp, norm_cast] lemma cpow_int_cast (x : ℂ) : ∀ (n : ℤ), x ^ (n : ℂ) = x ^ n
| (n : ℕ) := by simp
| -[1+ n] := by rw zpow_neg_succ_of_nat;
  simp only [int.neg_succ_of_nat_coe, int.cast_neg, complex.cpow_neg, inv_eq_one_div,
    int.cast_coe_nat, cpow_nat_cast]

lemma cpow_nat_inv_pow (x : ℂ) {n : ℕ} (hn : n ≠ 0) : (x ^ (n⁻¹ : ℂ)) ^ n = x :=
begin
  suffices : im (log x * n⁻¹) ∈ Ioc (-π) π,
  { rw [← cpow_nat_cast, ← cpow_mul _ this.1 this.2, inv_mul_cancel, cpow_one],
    exact_mod_cast hn },
  rw [mul_comm, ← of_real_nat_cast, ← of_real_inv, of_real_mul_im, ← div_eq_inv_mul],
  rw [← pos_iff_ne_zero] at hn,
  have hn' : 0 < (n : ℝ), by assumption_mod_cast,
  have hn1 : 1 ≤ (n : ℝ), by exact_mod_cast (nat.succ_le_iff.2 hn),
  split,
  { rw lt_div_iff hn',
    calc -π * n ≤ -π * 1 : mul_le_mul_of_nonpos_left hn1 (neg_nonpos.2 real.pi_pos.le)
    ... = -π : mul_one _
    ... < im (log x) : neg_pi_lt_log_im _ },
  { rw div_le_iff hn',
    calc im (log x) ≤ π : log_im_le_pi _
    ... = π * 1 : (mul_one π).symm
    ... ≤ π * n : mul_le_mul_of_nonneg_left hn1 real.pi_pos.le }
end

lemma mul_cpow_of_real_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℂ) :
  ((a : ℂ) * (b : ℂ)) ^ r = (a : ℂ) ^ r * (b : ℂ) ^ r :=
begin
  rcases eq_or_ne r 0 with rfl | hr,
  { simp only [cpow_zero, mul_one] },
  rcases eq_or_lt_of_le ha with rfl | ha',
  { rw [of_real_zero, zero_mul, zero_cpow hr, zero_mul] },
  rcases eq_or_lt_of_le hb with rfl | hb',
  { rw [of_real_zero, mul_zero, zero_cpow hr, mul_zero] },
  have ha'' : (a : ℂ) ≠ 0 := of_real_ne_zero.mpr ha'.ne',
  have hb'' : (b : ℂ) ≠ 0 := of_real_ne_zero.mpr hb'.ne',
  rw [cpow_def_of_ne_zero (mul_ne_zero ha'' hb''), log_of_real_mul ha' hb'', of_real_log ha,
    add_mul, exp_add, ←cpow_def_of_ne_zero ha'', ←cpow_def_of_ne_zero hb'']
end

lemma inv_cpow_eq_ite (x : ℂ) (n : ℂ) :
  x⁻¹ ^ n = if x.arg = π then conj (x ^ conj n)⁻¹ else (x ^ n)⁻¹ :=
begin
  simp_rw [complex.cpow_def, log_inv_eq_ite, inv_eq_zero, map_eq_zero, ite_mul, neg_mul,
    is_R_or_C.conj_inv, apply_ite conj, apply_ite exp, apply_ite has_inv.inv, map_zero, map_one,
    exp_neg, inv_one, inv_zero, ←exp_conj, map_mul, conj_conj],
  split_ifs with hx hn ha ha; refl,
end

lemma inv_cpow (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : x⁻¹ ^ n = (x ^ n)⁻¹ :=
by rw [inv_cpow_eq_ite, if_neg hx]

/-- `complex.inv_cpow_eq_ite` with the `ite` on the other side. -/
lemma inv_cpow_eq_ite' (x : ℂ) (n : ℂ) :
  (x ^ n)⁻¹ = if x.arg = π then conj (x⁻¹ ^ conj n) else x⁻¹ ^ n :=
begin
  rw [inv_cpow_eq_ite, apply_ite conj, conj_conj, conj_conj],
  split_ifs,
  { refl },
  { rw inv_cpow _ _ h }
end

lemma conj_cpow_eq_ite (x : ℂ) (n : ℂ) :
  conj x ^ n = if x.arg = π then x ^ n else conj (x ^ conj n) :=
begin
  simp_rw [cpow_def, map_eq_zero, apply_ite conj, map_one, map_zero, ←exp_conj, map_mul,
    conj_conj, log_conj_eq_ite],
  split_ifs with hcx hn hx; refl
end

lemma conj_cpow (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : conj x ^ n = conj (x ^ conj n) :=
by rw [conj_cpow_eq_ite, if_neg hx]

lemma cpow_conj (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : x ^ conj n = conj (conj x ^ n) :=
by rw [conj_cpow _ _ hx, conj_conj]

end complex
