/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import algebra.ordered_group
import algebra.group_with_zero
import algebra.group_with_zero_power

/-!
# Ordered commutative groups with a zero element adjoined

This file sets up a class of ordered commutative groups with zero adjoined, for
instance the fractional ideals of a Dedekind domain.
-/

set_option old_structure_cmd true

/-- A linearly ordered commutative group with a zero element. -/
class ordered_comm_group_with_zero (G : Type*)
  extends comm_group_with_zero G, ordered_comm_monoid G :=
(zero_le_one : (0:G) ≤ 1)

variables {G : Type*} [ordered_comm_group_with_zero G]
variables {a b c d x y z : G}

local attribute [instance] classical.prop_decidable

section ordered_comm_monoid

/-
The following facts are true more generally in a (linearly) ordered commutative monoid.
-/

lemma one_le_pow_of_one_le' {n : ℕ} (H : 1 ≤ x) : 1 ≤ x^n :=
begin
  induction n with n ih,
  { exact le_refl 1 },
  { exact one_le_mul H ih }
end

lemma pow_le_one_of_le_one {n : ℕ} (H : x ≤ 1) : x^n ≤ 1 :=
begin
  induction n with n ih,
  { exact le_refl 1 },
  { exact mul_le_one' H ih }
end

end ordered_comm_monoid

lemma zero_le_one' : (0 : G) ≤ 1 :=
ordered_comm_group_with_zero.zero_le_one

lemma zero_lt_one'' : (0 : G) < 1 :=
lt_of_le_of_ne zero_le_one' zero_ne_one

@[simp] lemma zero_le' : 0 ≤ a :=
by simpa only [mul_zero, mul_one] using mul_le_mul_left' (@zero_le_one' G _) a

@[simp] lemma not_lt_zero' : ¬a < 0 :=
not_lt_of_le zero_le'

@[simp] lemma le_zero_iff : a ≤ 0 ↔ a = 0 :=
⟨λ h, le_antisymm h zero_le', λ h, h ▸ le_refl _⟩

lemma zero_lt_iff : 0 < a ↔ a ≠ 0 :=
⟨ne_of_gt, λ h, lt_of_le_of_ne zero_le' h.symm⟩

lemma le_of_le_mul_right (h : c ≠ 0) (hab : a * c ≤ b * c) : a ≤ b :=
by simpa only [mul_inv_cancel_right' h] using (mul_le_mul_right' hab c⁻¹)

lemma le_mul_inv_of_mul_le (h : c ≠ 0) (hab : a * c ≤ b) : a ≤ b * c⁻¹ :=
le_of_le_mul_right h (by simpa [h] using hab)

lemma mul_inv_le_of_le_mul (h : c ≠ 0) (hab : a ≤ b * c) : a * c⁻¹ ≤ b :=
le_of_le_mul_right h (by simpa [h] using hab)

lemma div_le_div' (a b c d : G) (hb : b ≠ 0) (hd : d ≠ 0) :
  a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b :=
begin
  by_cases ha : a = 0, { simp [ha] },
  by_cases hc : c = 0, { simp [inv_ne_zero hb, hc, hd], },
  exact @div_le_div_iff' _ _ (units.mk0 a ha) (units.mk0 b hb) (units.mk0 c hc) (units.mk0 d hd)
end

lemma ne_zero_of_lt (h : b < a) : a ≠ 0 :=
λ h1, not_lt_zero' $ show b < 0, from h1 ▸ h

@[simp] lemma units.zero_lt (u : units G) : (0 : G) < u :=
zero_lt_iff.2 $ u.ne_zero

lemma mul_lt_mul'''' (hab : a < b) (hcd : c < d) : a * c < b * d :=
have hb : b ≠ 0 := ne_zero_of_lt hab,
have hd : d ≠ 0 := ne_zero_of_lt hcd,
if ha : a = 0 then by { rw [ha, zero_mul, zero_lt_iff], exact mul_ne_zero hb hd } else
if hc : c = 0 then by { rw [hc, mul_zero, zero_lt_iff], exact mul_ne_zero hb hd } else
@mul_lt_mul''' _ _ (units.mk0 a ha) (units.mk0 b hb) (units.mk0 c hc) (units.mk0 d hd) hab hcd

lemma inv_lt_inv'' (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ < b⁻¹ ↔ b < a :=
@inv_lt_inv_iff _ _ (units.mk0 a ha) (units.mk0 b hb)

lemma inv_le_inv'' (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
@inv_le_inv_iff _ _ (units.mk0 a ha) (units.mk0 b hb)
