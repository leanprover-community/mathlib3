/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

Integer power operation on fields.
-/

import algebra.group_power tactic.wlog 

universe u

section field_power
open int nat 
variables {α : Type u} [division_ring α]

@[simp] lemma zero_gpow : ∀ z : ℕ, z ≠ 0 → (0 : α)^z = 0
| 0 h := absurd rfl h 
| (k+1) h := zero_mul _ 

def fpow (a : α) : ℤ → α 
| (of_nat n) := a ^ n 
| -[1+n] := 1/(a ^ (n+1))

lemma unit_pow {a : α} (ha : a ≠ 0) : ∀ n : ℕ, a ^ n = ↑((units.mk0 a ha)^n)
| 0 := by simp; refl
| (k+1) := by simp [_root_.pow_add]; congr; apply unit_pow 

lemma fpow_eq_gpow {a : α} (h : a ≠ 0) : ∀ (z : ℤ), fpow a z = ↑(gpow (units.mk0 a h) z)
| (of_nat k) := by simp only [fpow, gpow]; apply unit_pow 
| -[1+k] := by simp [fpow, gpow]; congr; apply unit_pow 

lemma fpow_inv (a : α) : fpow a (-1) = a⁻¹ := 
begin change fpow a -[1+0] = a⁻¹, simp [fpow] end 

lemma fpow_ne_zero_of_ne_zero {a : α} (ha : a ≠ 0) : ∀ (z : ℤ), fpow a z ≠ 0
| (of_nat n) := pow_ne_zero _ ha
| -[1+n] := one_div_ne_zero $ pow_ne_zero _ ha

@[simp] lemma fpow_zero {a : α} : fpow a 0 = 1 :=
pow_zero _ 

lemma fpow_add {a : α} (ha : a ≠ 0) (z1 z2 : ℤ) : fpow a (z1 + z2) = fpow a z1 * fpow a z2 := 
begin simp only [fpow_eq_gpow ha], rw ←units.mul_coe, congr, apply gpow_add end 

end field_power

section discrete_field_power
open int nat 
variables {α : Type u} [discrete_field α]

lemma zero_fpow : ∀ z : ℤ, z ≠ 0 → fpow (0 : α) z = 0
| (of_nat n) h :=
  have h2 : n ≠ 0, from assume : n = 0, by simpa [this] using h,
  by simp [h, h2, fpow]
| -[1+n] h := 
  have h1 : (0 : α) ^ (n+1) = 0, from zero_mul _,
  by simp [fpow, h1]

end discrete_field_power

section ordered_field_power
open int 

variables {α : Type u} [discrete_linear_ordered_field α]

lemma fpow_nonneg_of_nonneg {a : α} (ha : a ≥ 0) : ∀ (z : ℤ), fpow a z ≥ 0
| (of_nat n) := pow_nonneg ha _
| -[1+n] := div_nonneg' zero_le_one $ pow_nonneg ha _


lemma fpow_le_of_le {x : α} (hx : 1 ≤ x) {a b : ℤ} (h : a ≤ b) : fpow x a ≤ fpow x b :=
begin 
  induction a with a a; induction b with b b,
  { simp only [fpow], 
    apply pow_le_pow hx, 
    apply le_of_coe_nat_le_coe_nat h },
  { apply absurd h, 
    apply not_le_of_gt,
    exact lt_of_lt_of_le (neg_succ_lt_zero _) (of_nat_nonneg _) },
  { simp only [fpow, one_div_eq_inv], 
    apply le_trans (inv_le_one _); apply one_le_pow_of_one_le hx },
  { simp only [fpow],
    apply (one_div_le_one_div _ _).2,
    { apply pow_le_pow hx,
      have : -(↑(a+1) : ℤ) ≤ -(↑(b+1) : ℤ), from h,
      have h' := le_of_neg_le_neg this,
      apply le_of_coe_nat_le_coe_nat h' },
    repeat { apply pow_pos (lt_of_lt_of_le zero_lt_one hx) } }
end

lemma pow_le_max_of_min_le {x : α} (hx : x ≥ 1) {a b c : ℤ} (h : min a b ≤ c) : 
      fpow x (-c) ≤ max (fpow x (-a)) (fpow x (-b)) :=
begin 
  wlog hle : a ≤ b,
  have hnle : -b ≤ -a, from neg_le_neg hle,
  have hfle : fpow x (-b) ≤ fpow x (-a), from fpow_le_of_le hx hnle,
  have : fpow x (-c) ≤ fpow x (-a), 
  { apply fpow_le_of_le hx,
    simpa [hle, min_eq_left] using h },
  simpa [hfle, max_eq_left] using this 
end 

end ordered_field_power 