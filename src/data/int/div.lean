/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import data.int.dvd.basic
import data.nat.order.lemmas
import algebra.ring.regular

/-!
# Lemmas relating `/` in `ℤ` with the ordering.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open nat

namespace int

theorem eq_mul_div_of_mul_eq_mul_of_dvd_left {a b c d : ℤ} (hb : b ≠ 0) (hbc : b ∣ c)
    (h : b * a = c * d) :
  a = c / b * d :=
begin
  cases hbc with k hk,
  subst hk,
  rw [int.mul_div_cancel_left _ hb],
  rw mul_assoc at h,
  apply mul_left_cancel₀ hb h
end

/-- If an integer with larger absolute value divides an integer, it is
zero. -/
lemma eq_zero_of_dvd_of_nat_abs_lt_nat_abs {a b : ℤ} (w : a ∣ b) (h : nat_abs b < nat_abs a) :
  b = 0 :=
begin
  rw [←nat_abs_dvd, ←dvd_nat_abs, coe_nat_dvd] at w,
  rw ←nat_abs_eq_zero,
  exact eq_zero_of_dvd_of_lt w h
end

lemma eq_zero_of_dvd_of_nonneg_of_lt {a b : ℤ} (w₁ : 0 ≤ a) (w₂ : a < b) (h : b ∣ a) : a = 0 :=
eq_zero_of_dvd_of_nat_abs_lt_nat_abs h (nat_abs_lt_nat_abs_of_nonneg_of_lt w₁ w₂)

/-- If two integers are congruent to a sufficiently large modulus,
they are equal. -/
lemma eq_of_mod_eq_of_nat_abs_sub_lt_nat_abs {a b c : ℤ} (h1 : a % b = c)
    (h2 : nat_abs (a - c) < nat_abs b) :
  a = c :=
eq_of_sub_eq_zero (eq_zero_of_dvd_of_nat_abs_lt_nat_abs (dvd_sub_of_mod_eq h1) h2)

theorem of_nat_add_neg_succ_of_nat_of_ge {m n : ℕ}
  (h : n.succ ≤ m) : of_nat m + -[1+n] = of_nat (m - n.succ) :=
begin
  change sub_nat_nat _ _ = _,
  have h' : n.succ - m = 0,
  apply tsub_eq_zero_iff_le.mpr h,
  simp [*, sub_nat_nat]
end

lemma nat_abs_le_of_dvd_ne_zero {s t : ℤ} (hst : s ∣ t) (ht : t ≠ 0) : nat_abs s ≤ nat_abs t :=
not_lt.mp (mt (eq_zero_of_dvd_of_nat_abs_lt_nat_abs hst) ht)

end int
