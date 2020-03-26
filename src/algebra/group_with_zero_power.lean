/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import algebra.group_with_zero
import algebra.group_power
import algebra.field

/-!
# Powers of elements of groups with an adjoined zero element

In this file we define integer power functions for groups with an adjoined zero element.
This generalises the integer power function on a division ring.
-/

@[simp] lemma gwz.zero_pow {M : Type*} [monoid_with_zero M] :
  ∀ n : ℕ, n ≠ 0 → (0 : M)^n = 0
| 0     h := absurd rfl h
| (k+1) h := zero_mul _

namespace gwz
variables {G : Type*} [group_with_zero G]

section nat_pow

@[field_simps] theorem inv_pow (a : G) (n : ℕ) : (a⁻¹)^n = (a^n)⁻¹ :=
by induction n with n ih; [exact inv_one.symm,
  rw [pow_succ', pow_succ, ih, mul_inv_rev]]

theorem pow_eq_zero {g : G} {n : ℕ} (H : g^n = 0) : g = 0 :=
begin
  induction n with n ih,
  { rw pow_zero at H,
    rw [← mul_one g, H, mul_zero] },
  exact or.cases_on (mul_eq_zero _ _ H) id ih
end

@[field_simps] theorem pow_ne_zero {g : G} (n : ℕ) (h : g ≠ 0) : g ^ n ≠ 0 :=
mt pow_eq_zero h

theorem pow_sub (a : G) {m n : ℕ} (ha : a ≠ 0) (h : n ≤ m) : a^(m - n) = a^m * (a^n)⁻¹ :=
have h1 : m - n + n = m, from nat.sub_add_cancel h,
have h2 : a^(m - n) * a^n = a^m, by rw [←pow_add, h1],
eq_mul_inv_of_mul_eq (pow_ne_zero _ ha) h2

theorem pow_inv_comm (a : G) (m n : ℕ) : (a⁻¹)^m * a^n = a^n * (a⁻¹)^m :=
by rw inv_pow; exact inv_comm_of_comm (pow_mul_comm _ _ _)

end nat_pow

end gwz

section int_pow
open gwz int
variables {G : Type*} [group_with_zero G]

/--
The power operation in a group with zero.
This extends `monoid.pow` to negative integers
with the definition `a^(-n) = (a^n)⁻¹`.
-/
def fpow (a : G) : ℤ → G
| (of_nat n) := a^n
| -[1+n]     := (a^(nat.succ n))⁻¹

@[priority 10] instance : has_pow G ℤ := ⟨fpow⟩

@[simp] theorem fpow_coe_nat (a : G) (n : ℕ) : a ^ (n:ℤ) = a ^ n := rfl

theorem fpow_of_nat (a : G) (n : ℕ) : a ^ of_nat n = a ^ n := rfl

@[simp] theorem fpow_neg_succ (a : G) (n : ℕ) : a ^ -[1+n] = (a ^ n.succ)⁻¹ := rfl

local attribute [ematch] le_of_lt

@[simp] theorem fpow_zero (a : G) : a ^ (0:ℤ) = 1 := rfl

@[simp] theorem fpow_one (a : G) : a ^ (1:ℤ) = a := mul_one _

@[simp] theorem one_fpow : ∀ (n : ℤ), (1 : G) ^ n = 1
| (n : ℕ) := one_pow _
| -[1+ n] := show _⁻¹=(1:G), by rw [one_pow, gwz.inv_one]

lemma zero_fpow : ∀ z : ℤ, z ≠ 0 → (0 : G) ^ z = 0
| (of_nat n) h := gwz.zero_pow _ $ by rintro rfl; exact h rfl
| -[1+n]     h := show (0*0^n)⁻¹ = (0 : G), by simp

@[simp] theorem fpow_neg (a : G) : ∀ (n : ℤ), a ^ -n = (a ^ n)⁻¹
| (n+1:ℕ) := rfl
| 0       := gwz.inv_one.symm
| -[1+ n] := (gwz.inv_inv _).symm

theorem fpow_neg_one (x : G) : x ^ (-1:ℤ) = x⁻¹ := congr_arg has_inv.inv $ pow_one x

theorem inv_fpow (a : G) : ∀n:ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
| (n : ℕ) := inv_pow a n
| -[1+ n] := congr_arg has_inv.inv $ inv_pow a (n+1)

private lemma fpow_add_aux (a : G) (h : a ≠ 0) (m n : nat) :
  a ^ ((of_nat m) + -[1+n]) = a ^ of_nat m * a ^ -[1+n] :=
or.elim (nat.lt_or_ge m (nat.succ n))
 (assume h1 : m < n.succ,
  have h2 : m ≤ n, from nat.le_of_lt_succ h1,
  suffices a ^ -[1+ n-m] = a ^ of_nat m * a ^ -[1+n],
    by rwa [of_nat_add_neg_succ_of_nat_of_lt h1],
  show (a ^ nat.succ (n - m))⁻¹ = a ^ of_nat m * a ^ -[1+n],
  by rw [← nat.succ_sub h2, pow_sub _ h (le_of_lt h1), gwz.mul_inv_rev, gwz.inv_inv]; refl)
 (assume : m ≥ n.succ,
  suffices a ^ (of_nat (m - n.succ)) = (a ^ (of_nat m)) * (a ^ -[1+ n]),
    by rw [of_nat_add_neg_succ_of_nat_of_ge]; assumption,
  suffices a ^ (m - n.succ) = a ^ m * (a ^ n.succ)⁻¹, from this,
  by rw gwz.pow_sub; assumption)

theorem fpow_add {a : G} (h : a ≠ 0) : ∀ (i j : ℤ), a ^ (i + j) = a ^ i * a ^ j
| (of_nat m) (of_nat n) := pow_add _ _ _
| (of_nat m) -[1+n]     := fpow_add_aux _ h _ _
| -[1+m]     (of_nat n) := by rw [add_comm, fpow_add_aux _ h,
  fpow_neg_succ, fpow_of_nat, ← gwz.inv_pow, ← gwz.pow_inv_comm]
| -[1+m]     -[1+n]     :=
  suffices (a ^ (m + n.succ.succ))⁻¹ = (a ^ m.succ)⁻¹ * (a ^ n.succ)⁻¹, from this,
  by rw [← nat.succ_add_eq_succ_add, add_comm, pow_add, gwz.mul_inv_rev]

theorem fpow_add_one (a : G) (h : a ≠ 0) (i : ℤ) : a ^ (i + 1) = a ^ i * a :=
by rw [fpow_add h, fpow_one]

theorem fpow_one_add (a : G) (h : a ≠ 0) (i : ℤ) : a ^ (1 + i) = a * a ^ i :=
by rw [fpow_add h, fpow_one]

theorem fpow_mul_comm (a : G) (h : a ≠ 0) (i j : ℤ) : a ^ i * a ^ j = a ^ j * a ^ i :=
by rw [← fpow_add h, ← fpow_add h, add_comm]

theorem fpow_mul (a : G) : ∀ m n : ℤ, a ^ (m * n) = (a ^ m) ^ n
| (m : ℕ) (n : ℕ) := pow_mul _ _ _
| (m : ℕ) -[1+ n] := (fpow_neg _ (m * n.succ)).trans $
  show (a ^ (m * n.succ))⁻¹ = _, by rw pow_mul; refl
| -[1+ m] (n : ℕ) := (fpow_neg _ (m.succ * n)).trans $
  show (a ^ (m.succ * n))⁻¹ = _, by rw [pow_mul, ← gwz.inv_pow]; refl
| -[1+ m] -[1+ n] := (pow_mul a m.succ n.succ).trans $
  show _ = (_⁻¹^_)⁻¹, by rw [gwz.inv_pow, gwz.inv_inv]

theorem fpow_mul' (a : G) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m :=
by rw [mul_comm, fpow_mul]

lemma fpow_inv (a : G) : a ^ (-1 : ℤ) = a⁻¹ :=
show (a*1)⁻¹ = a⁻¹, by rw [mul_one]

@[simp] lemma unit_pow {a : G} (ha : a ≠ 0) :
  ∀ n : ℕ, (((units.mk0 a ha)^n : units G) : G) = a ^ n
| 0     := units.coe_one.symm
| (k+1) := by { simp only [pow_succ, units.coe_mul, units.coe_mk0], rw unit_pow }

lemma fpow_neg_succ_of_nat (a : G) (n : ℕ) : a ^ (-[1+ n]) = (a ^ (n + 1))⁻¹ := rfl

@[simp] lemma unit_gpow {a : G} (h : a ≠ 0) :
  ∀ (z : ℤ), (((units.mk0 a h)^z : units G) : G) = a ^ z
| (of_nat k) := unit_pow _ _
| -[1+k] := by rw [fpow_neg_succ_of_nat, gpow_neg_succ, units.inv_eq_inv, unit_pow]

lemma fpow_ne_zero_of_ne_zero {a : G} (ha : a ≠ 0) : ∀ (z : ℤ), a ^ z ≠ 0
| (of_nat n) := pow_ne_zero _ ha
| -[1+n]     := inv_ne_zero $ pow_ne_zero _ ha

lemma fpow_sub {a : G} (ha : a ≠ 0) (z1 z2 : ℤ) : a ^ (z1 - z2) = a ^ z1 / a ^ z2 :=
by rw [sub_eq_add_neg, fpow_add ha, fpow_neg]; refl

lemma mul_fpow {G : Type*} [comm_group_with_zero G] (a b : G) :
  ∀ (i : ℤ), (a * b) ^ i = (a ^ i) * (b ^ i)
| (int.of_nat n) := mul_pow a b n
| -[1+n] :=
  by rw [fpow_neg_succ_of_nat, fpow_neg_succ_of_nat, fpow_neg_succ_of_nat,
      mul_pow, gwz.mul_inv]

lemma fpow_eq_zero {x : G} {n : ℤ} (h : x^n = 0) : x = 0 :=
classical.by_contradiction $ λ hx, fpow_ne_zero_of_ne_zero hx n h

lemma fpow_ne_zero {x : G} (n : ℤ) : x ≠ 0 → x^n ≠ 0 :=
mt fpow_eq_zero

theorem fpow_neg_mul_fpow_self (n : ℤ) {x : G} (h : x ≠ 0) :
  x^(-n) * x^n = 1 :=
begin
  rw [fpow_neg],
  exact gwz.inv_mul_cancel _ (fpow_ne_zero n h)
end

theorem one_div_pow {a : G} (n : ℕ) :
  (1 / a) ^ n = 1 / a ^ n :=
by simp only [gwz.one_div, gwz.inv_pow]

theorem one_div_fpow {a : G} (n : ℤ) :
  (1 / a) ^ n = 1 / a ^ n :=
by simp only [gwz.one_div, inv_fpow]

end int_pow

section
variables {G : Type*} [comm_group_with_zero G]

@[simp] theorem div_pow (a b : G) (n : ℕ) :
  (a / b) ^ n = a ^ n / b ^ n :=
by simp only [div_eq_mul_inv, mul_pow, gwz.inv_pow]

@[simp] theorem div_fpow (a : G) {b : G} (n : ℤ) :
  (a / b) ^ n = a ^ n / b ^ n :=
by simp only [div_eq_mul_inv, mul_fpow, inv_fpow]

lemma div_sq_cancel {a : G} (ha : a ≠ 0) (b : G) : a^2 * b / a = a * b :=
by rw [pow_two, mul_assoc, gwz.mul_div_cancel_left _ ha]

end
