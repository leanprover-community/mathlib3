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
| 0 := units.coe_one.symm
| (k+1) := by simp only [_root_.pow_succ, units.coe_mul, units.mk0_val]; rw unit_pow

lemma fpow_eq_gpow {a : α} (h : a ≠ 0) : ∀ (z : ℤ), fpow a z = ↑(gpow (units.mk0 a h) z)
| (of_nat k) := unit_pow _ _
| -[1+k] := by rw [fpow, gpow, one_div_eq_inv, units.inv_eq_inv, unit_pow]

lemma fpow_inv (a : α) : fpow a (-1) = a⁻¹ :=
show 1*(a*1)⁻¹ = a⁻¹, by rw [one_mul, mul_one]

lemma fpow_ne_zero_of_ne_zero {a : α} (ha : a ≠ 0) : ∀ (z : ℤ), fpow a z ≠ 0
| (of_nat n) := pow_ne_zero _ ha
| -[1+n] := one_div_ne_zero $ pow_ne_zero _ ha

@[simp] lemma fpow_zero {a : α} : fpow a 0 = 1 :=
pow_zero _

lemma fpow_add {a : α} (ha : a ≠ 0) (z1 z2 : ℤ) : fpow a (z1 + z2) = fpow a z1 * fpow a z2 :=
begin simp only [fpow_eq_gpow ha], rw ← units.coe_mul, congr, apply gpow_add end

end field_power

section discrete_field_power
open int nat
variables {α : Type u} [discrete_field α]

lemma zero_fpow : ∀ z : ℤ, z ≠ 0 → fpow (0 : α) z = 0
| (of_nat n) h := zero_gpow _ $ by rintro rfl; exact h rfl
| -[1+n] h := show 1/(0*0^n)=(0:α), by rw [zero_mul, one_div_zero]

lemma fpow_neg (a : α) : ∀ n, fpow a (-n) = 1 / fpow a n
| (of_nat 0) := by simp [of_nat_zero]
| (of_nat (n+1)) := rfl
| -[1+n] := show fpow a (n+1) = 1 / (1 / fpow a (n+1)), by rw one_div_one_div

lemma fpow_sub {a : α} (ha : a ≠ 0) (z1 z2 : ℤ) : fpow a (z1 - z2) = fpow a z1 / fpow a z2 :=
by rw [sub_eq_add_neg, fpow_add ha, fpow_neg, ←div_eq_mul_one_div]

end discrete_field_power

section ordered_field_power
open int

variables {α : Type u} [discrete_linear_ordered_field α]

lemma fpow_nonneg_of_nonneg {a : α} (ha : a ≥ 0) : ∀ (z : ℤ), fpow a z ≥ 0
| (of_nat n) := pow_nonneg ha _
| -[1+n] := div_nonneg' zero_le_one $ pow_nonneg ha _

lemma fpow_pos_of_pos {a : α} (ha : a > 0) : ∀ (z : ℤ), fpow a z > 0
| (of_nat n) := pow_pos ha _
| -[1+n] := div_pos zero_lt_one $ pow_pos ha _

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
    simpa only [min_eq_left hle, neg_le_neg_iff] using h },
  simpa only [max_eq_left hfle]
end

lemma fpow_le_one_of_nonpos {p : α} (hp : p ≥ 1) {z : ℤ} (hz : z ≤ 0) : fpow p z ≤ 1 :=
calc fpow p z ≤ fpow p 0 : fpow_le_of_le hp hz
          ... = 1        : by simp

lemma fpow_ge_one_of_nonneg {p : α} (hp : p ≥ 1) {z : ℤ} (hz : z ≥ 0) : fpow p z ≥ 1 :=
calc fpow p z ≥ fpow p 0 : fpow_le_of_le hp hz
          ... = 1        : by simp

end ordered_field_power

lemma one_lt_pow {α} [linear_ordered_semiring α] {p : α} (hp : p > 1) : ∀ {n : ℕ}, 1 ≤ n → 1 < p ^ n
| 1 h := by simp; assumption
| (k+2) h :=
  begin
    rw ←one_mul (1 : α),
    apply mul_lt_mul,
    { assumption },
    { apply le_of_lt, simpa using one_lt_pow (nat.le_add_left 1 k)},
    { apply zero_lt_one },
    { apply le_of_lt (lt_trans zero_lt_one hp) }
  end

lemma one_lt_fpow {α}  [discrete_linear_ordered_field α] {p : α} (hp : p > 1) :
  ∀ z : ℤ, z > 0 → 1 < fpow p z
| (int.of_nat n) h := one_lt_pow hp (nat.succ_le_of_lt (int.lt_of_coe_nat_lt_coe_nat h))
