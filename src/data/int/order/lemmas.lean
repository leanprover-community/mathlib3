/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import data.int.order.basic
import algebra.group_with_zero.divisibility
import algebra.order.ring.abs

/-!
# Further lemmas about the integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
The distinction between this file and `data.int.order.basic` is not particularly clear.
They are separated by now to minimize the porting requirements for tactics during the transition to
mathlib4. After `data.rat.order` has been ported, please feel free to reorganize these two files.
-/

open nat


namespace int


/-! ### nat abs -/

variables {a b : ℤ} {n : ℕ}

lemma nat_abs_eq_iff_mul_self_eq {a b : ℤ} : a.nat_abs = b.nat_abs ↔ a * a = b * b :=
begin
  rw [← abs_eq_iff_mul_self_eq, abs_eq_nat_abs, abs_eq_nat_abs],
  exact int.coe_nat_inj'.symm
end

lemma eq_nat_abs_iff_mul_eq_zero : a.nat_abs = n ↔ (a - n) * (a + n) = 0 :=
by rw [nat_abs_eq_iff, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

lemma nat_abs_lt_iff_mul_self_lt {a b : ℤ} : a.nat_abs < b.nat_abs ↔ a * a < b * b :=
begin
  rw [← abs_lt_iff_mul_self_lt, abs_eq_nat_abs, abs_eq_nat_abs],
  exact int.coe_nat_lt.symm
end

lemma nat_abs_le_iff_mul_self_le {a b : ℤ} : a.nat_abs ≤ b.nat_abs ↔ a * a ≤ b * b :=
begin
  rw [← abs_le_iff_mul_self_le, abs_eq_nat_abs, abs_eq_nat_abs],
  exact int.coe_nat_le.symm
end

lemma dvd_div_of_mul_dvd {a b c : ℤ} (h : a * b ∣ c) : b ∣ c / a :=
begin
  rcases eq_or_ne a 0 with rfl | ha,
  { simp only [int.div_zero, dvd_zero] },
  rcases h with ⟨d, rfl⟩,
  refine ⟨d, _⟩,
  rw [mul_assoc, int.mul_div_cancel_left _ ha],
end

/-! ### units -/

lemma eq_zero_of_abs_lt_dvd {m x : ℤ} (h1 : m ∣ x) (h2 : | x | < m) : x = 0 :=
begin
  by_cases hm : m = 0, { subst m, exact zero_dvd_iff.mp h1, },
  rcases h1 with ⟨d, rfl⟩,
  apply mul_eq_zero_of_right,
  rw [←abs_lt_one_iff, ←mul_lt_iff_lt_one_right (abs_pos.mpr hm), ←abs_mul],
  exact lt_of_lt_of_le h2 (le_abs_self m),
end

end int
