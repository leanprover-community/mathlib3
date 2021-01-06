/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin, Patrick Massot
-/

import algebra.ordered_group
import algebra.group_with_zero
import algebra.group_with_zero.power
import algebra.linear_ordered_comm_monoid_with_zero
import tactic.abel

/-!
# Linearly ordered commutative groups with a zero element adjoined

This file is an extension of `linear_ordered_comm_monoid_with_zero` for groups.
The files are separated to avoid import cycles
-/

set_option old_structure_cmd true

/-- A linearly ordered commutative group with a zero element. -/
class linear_ordered_comm_group_with_zero (α : Type*)
  extends linear_ordered_comm_monoid_with_zero α, comm_group_with_zero α

variables {α : Type*}
variables {a b c d x y z : α}

variables [linear_ordered_comm_group_with_zero α]

lemma zero_lt_one'' : (0 : α) < 1 :=
lt_of_le_of_ne zero_le_one' zero_ne_one

lemma le_of_le_mul_right (h : c ≠ 0) (hab : a * c ≤ b * c) : a ≤ b :=
by simpa only [mul_inv_cancel_right' h] using (mul_le_mul_right' hab c⁻¹)

lemma le_mul_inv_of_mul_le (h : c ≠ 0) (hab : a * c ≤ b) : a ≤ b * c⁻¹ :=
le_of_le_mul_right h (by simpa [h] using hab)

lemma mul_inv_le_of_le_mul (h : c ≠ 0) (hab : a ≤ b * c) : a * c⁻¹ ≤ b :=
le_of_le_mul_right h (by simpa [h] using hab)

lemma div_le_div' (a b c d : α) (hb : b ≠ 0) (hd : d ≠ 0) :
  a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b :=
begin
  by_cases ha : a = 0, { simp [ha] },
  by_cases hc : c = 0, { simp [inv_ne_zero hb, hc, hd], },
  exact @div_le_div_iff' _ _ (units.mk0 a ha) (units.mk0 b hb) (units.mk0 c hc) (units.mk0 d hd)
end

@[simp] lemma units.zero_lt (u : units α) : (0 : α) < u :=
zero_lt_iff.2 $ u.ne_zero

lemma mul_lt_mul'''' (hab : a < b) (hcd : c < d) : a * c < b * d :=
have hb : b ≠ 0 := ne_zero_of_lt hab,
have hd : d ≠ 0 := ne_zero_of_lt hcd,
if ha : a = 0 then by { rw [ha, zero_mul, zero_lt_iff], exact mul_ne_zero hb hd } else
if hc : c = 0 then by { rw [hc, mul_zero, zero_lt_iff], exact mul_ne_zero hb hd } else
@mul_lt_mul''' _ _ (units.mk0 a ha) (units.mk0 b hb) (units.mk0 c hc) (units.mk0 d hd) hab hcd

lemma mul_inv_lt_of_lt_mul' (h : x < y * z) : x * z⁻¹ < y :=
have hz : z ≠ 0 := (mul_ne_zero_iff.1 $ ne_zero_of_lt h).2,
by { contrapose! h, simpa only [inv_inv'] using mul_inv_le_of_le_mul (inv_ne_zero hz) h }

lemma mul_lt_right' (c : α) (h : a < b) (hc : c ≠ 0) : a * c < b * c :=
by { contrapose! h, exact le_of_le_mul_right hc h }

lemma pow_lt_pow_succ {x : α} {n : ℕ} (hx : 1 < x) : x ^ n < x ^ n.succ :=
by { rw ← one_mul (x ^ n),
exact mul_lt_right' _ hx (pow_ne_zero _ $ ne_of_gt (lt_trans zero_lt_one'' hx)) }

lemma pow_lt_pow' {x : α} {m n : ℕ} (hx : 1 < x) (hmn : m < n) : x ^ m < x ^ n :=
by { induction hmn with n hmn ih, exacts [pow_lt_pow_succ hx, lt_trans ih (pow_lt_pow_succ hx)] }

lemma inv_lt_inv'' (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ < b⁻¹ ↔ b < a :=
@inv_lt_inv_iff _ _ (units.mk0 a ha) (units.mk0 b hb)

lemma inv_le_inv'' (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
@inv_le_inv_iff _ _ (units.mk0 a ha) (units.mk0 b hb)

namespace monoid_hom

variables {R : Type*} [ring R] (f : R →* α)

theorem map_neg_one : f (-1) = 1 :=
begin
  apply eq_one_of_pow_eq_one (nat.succ_ne_zero 1) (_ : _ ^ 2 = _),
  rw [pow_two, ← f.map_mul, neg_one_mul, neg_neg, f.map_one],
end

@[simp] lemma map_neg (x : R) : f (-x) = f x :=
calc f (-x) = f (-1 * x)   : by rw [neg_one_mul]
        ... = f (-1) * f x : map_mul _ _ _
        ... = f x          : by rw [f.map_neg_one, one_mul]

lemma map_sub_swap (x y : R) : f (x - y) = f (y - x) :=
calc f (x - y) = f (-(y - x)) : by rw show x - y = -(y-x), by abel
           ... = _ : map_neg _ _

end monoid_hom
