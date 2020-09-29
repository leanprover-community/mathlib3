/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import algebra.group_power

/-!
# Powers of elements of groups with an adjoined zero element

In this file we define integer power functions for groups with an adjoined zero element.
This generalises the integer power function on a division ring.
-/

@[simp] lemma zero_pow' {M : Type*} [monoid_with_zero M] :
  ∀ n : ℕ, n ≠ 0 → (0 : M) ^ n = 0
| 0     h := absurd rfl h
| (k+1) h := zero_mul _

@[simp] lemma zero_pow_eq_zero {M : Type*} [monoid_with_zero M] [nontrivial M] {n : ℕ} :
  (0 : M) ^ n = 0 ↔ 0 < n :=
begin
  split; intro h,
  { rw [nat.pos_iff_ne_zero], rintro rfl, simpa using h },
  { exact zero_pow' n h.ne.symm }
end

theorem pow_eq_zero' {M : Type*} [monoid_with_zero M] [no_zero_divisors M]
  {a : M} {n : ℕ} (H : a ^ n = 0) : a = 0 :=
begin
  induction n with n ih,
  { rw pow_zero at H,
    rw [← mul_one a, H, mul_zero] },
  exact or.cases_on (mul_eq_zero.1 H) id ih
end

@[field_simps] theorem pow_ne_zero' {M : Type*} [monoid_with_zero M] [no_zero_divisors M]
  {a : M} (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 :=
mt pow_eq_zero' h

section group_with_zero
variables {G₀ : Type*} [group_with_zero G₀]

section nat_pow

@[simp, field_simps] theorem inv_pow' (a : G₀) (n : ℕ) : (a⁻¹) ^ n = (a ^ n)⁻¹ :=
by induction n with n ih; [exact inv_one.symm,
  rw [pow_succ', pow_succ, ih, mul_inv_rev']]

theorem pow_sub' (a : G₀) {m n : ℕ} (ha : a ≠ 0) (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ :=
have h1 : m - n + n = m, from nat.sub_add_cancel h,
have h2 : a ^ (m - n) * a ^ n = a ^ m, by rw [←pow_add, h1],
eq_div_of_mul_eq (pow_ne_zero' _ ha) h2

theorem pow_inv_comm' (a : G₀) (m n : ℕ) : (a⁻¹) ^ m * a ^ n = a ^ n * (a⁻¹) ^ m :=
(commute.refl a).inv_left'.pow_pow m n

end nat_pow

end group_with_zero

section int_pow
open int
variables {G₀ : Type*} [group_with_zero G₀]

/--
The power operation in a group with zero.
This extends `monoid.pow` to negative integers
with the definition `a ^ (-n) = (a ^ n)⁻¹`.
-/
def fpow (a : G₀) : ℤ → G₀
| (of_nat n) := a ^ n
| -[1+n]     := (a ^ (nat.succ n))⁻¹

@[priority 10] instance : has_pow G₀ ℤ := ⟨fpow⟩

@[simp] theorem fpow_coe_nat (a : G₀) (n : ℕ) : a ^ (n:ℤ) = a ^ n := rfl

theorem fpow_of_nat (a : G₀) (n : ℕ) : a ^ of_nat n = a ^ n := rfl

@[simp] theorem fpow_neg_succ_of_nat (a : G₀) (n : ℕ) : a ^ -[1+n] = (a ^ n.succ)⁻¹ := rfl

local attribute [ematch] le_of_lt

@[simp] theorem fpow_zero (a : G₀) : a ^ (0:ℤ) = 1 := rfl

@[simp] theorem fpow_one (a : G₀) : a ^ (1:ℤ) = a := mul_one _

@[simp] theorem one_fpow : ∀ (n : ℤ), (1 : G₀) ^ n = 1
| (n : ℕ) := one_pow _
| -[1+ n] := show _⁻¹=(1:G₀), by rw [one_pow, inv_one]

lemma zero_fpow : ∀ z : ℤ, z ≠ 0 → (0 : G₀) ^ z = 0
| (of_nat n) h := zero_pow' _ $ by rintro rfl; exact h rfl
| -[1+n]     h := show (0*0 ^ n)⁻¹ = (0 : G₀), by simp

@[simp] theorem fpow_neg (a : G₀) : ∀ (n : ℤ), a ^ -n = (a ^ n)⁻¹
| (n+1:ℕ) := rfl
| 0       := inv_one.symm
| -[1+ n] := (inv_inv' _).symm

theorem fpow_neg_one (x : G₀) : x ^ (-1:ℤ) = x⁻¹ := congr_arg has_inv.inv $ pow_one x

theorem inv_fpow (a : G₀) : ∀n:ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
| (n : ℕ) := inv_pow' a n
| -[1+ n] := congr_arg has_inv.inv $ inv_pow' a (n+1)

lemma fpow_add_one {a : G₀} (ha : a ≠ 0) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
| (of_nat n) := by simp [← int.coe_nat_succ, pow_succ']
| -[1+0]     := by simp [int.neg_succ_of_nat_eq, ha]
| -[1+(n+1)] := by rw [int.neg_succ_of_nat_eq, fpow_neg, neg_add, neg_add_cancel_right, fpow_neg,
  ← int.coe_nat_succ, fpow_coe_nat, fpow_coe_nat, pow_succ _ (n + 1), mul_inv_rev', mul_assoc,
  inv_mul_cancel ha, mul_one]

lemma fpow_sub_one {a : G₀} (ha : a ≠ 0) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
calc a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ : by rw [mul_assoc, mul_inv_cancel ha, mul_one]
             ... = a^n * a⁻¹             : by rw [← fpow_add_one ha, sub_add_cancel]

lemma fpow_add {a : G₀} (ha : a ≠ 0) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n :=
begin
  induction n using int.induction_on with n ihn n ihn,
  case hz : { simp },
  { simp only [← add_assoc, fpow_add_one ha, ihn, mul_assoc] },
  { rw [fpow_sub_one ha, ← mul_assoc, ← ihn, ← fpow_sub_one ha, add_sub_assoc] }
end

theorem fpow_one_add {a : G₀} (h : a ≠ 0) (i : ℤ) : a ^ (1 + i) = a * a ^ i :=
by rw [fpow_add h, fpow_one]

theorem semiconj_by.fpow_right {a x y : G₀} (h : semiconj_by a x y) :
  ∀ m : ℤ, semiconj_by a (x^m) (y^m)
| (n : ℕ) := h.pow_right n
| -[1+n]  := (h.pow_right (n + 1)).inv_right'

theorem commute.fpow_right {a b : G₀} (h : commute a b) : ∀ m : ℤ, commute a (b^m) :=
h.fpow_right

theorem commute.fpow_left {a b : G₀} (h : commute a b) (m : ℤ) : commute (a^m) b :=
(h.symm.fpow_right m).symm

theorem commute.fpow_fpow {a b : G₀} (h : commute a b) (m n : ℤ) : commute (a^m) (b^n) :=
(h.fpow_left m).fpow_right n

theorem commute.fpow_self (a : G₀) (n : ℤ) : commute (a^n) a := (commute.refl a).fpow_left n

theorem commute.self_fpow (a : G₀) (n : ℤ) : commute a (a^n) := (commute.refl a).fpow_right n

theorem commute.fpow_fpow_self (a : G₀) (m n : ℤ) : commute (a^m) (a^n) := (commute.refl a).fpow_fpow m n

theorem fpow_mul (a : G₀) : ∀ m n : ℤ, a ^ (m * n) = (a ^ m) ^ n
| (m : ℕ) (n : ℕ) := pow_mul _ _ _
| (m : ℕ) -[1+ n] := (fpow_neg _ (m * n.succ)).trans $
  show (a ^ (m * n.succ))⁻¹ = _, by rw pow_mul; refl
| -[1+ m] (n : ℕ) := (fpow_neg _ (m.succ * n)).trans $
  show (a ^ (m.succ * n))⁻¹ = _, by rw [pow_mul, ← inv_pow']; refl
| -[1+ m] -[1+ n] := (pow_mul a m.succ n.succ).trans $
  show _ = (_⁻¹ ^ _)⁻¹, by rw [inv_pow', inv_inv']

theorem fpow_mul' (a : G₀) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m :=
by rw [mul_comm, fpow_mul]

@[simp, norm_cast] lemma units.coe_gpow' (u : units G₀) :
  ∀ (n : ℤ), ((u ^ n : units G₀) : G₀) = u ^ n
| (n : ℕ) := u.coe_pow n
| -[1+k] := by rw [gpow_neg_succ_of_nat, fpow_neg_succ_of_nat, units.coe_inv', u.coe_pow]

lemma fpow_ne_zero_of_ne_zero {a : G₀} (ha : a ≠ 0) : ∀ (z : ℤ), a ^ z ≠ 0
| (of_nat n) := pow_ne_zero' _ ha
| -[1+n]     := inv_ne_zero $ pow_ne_zero' _ ha

lemma fpow_sub {a : G₀} (ha : a ≠ 0) (z1 z2 : ℤ) : a ^ (z1 - z2) = a ^ z1 / a ^ z2 :=
by rw [sub_eq_add_neg, fpow_add ha, fpow_neg]; refl

lemma commute.mul_fpow {a b : G₀} (h : commute a b) :
  ∀ (i : ℤ), (a * b) ^ i = (a ^ i) * (b ^ i)
| (n : ℕ) := h.mul_pow n
| -[1+n]  := by simp [h.mul_pow, (h.pow_pow _ _).eq, mul_inv_rev']

lemma mul_fpow {G₀ : Type*} [comm_group_with_zero G₀] (a b : G₀) (m : ℤ):
  (a * b) ^ m = (a ^ m) * (b ^ m) :=
(commute.all a b).mul_fpow m

lemma fpow_eq_zero {x : G₀} {n : ℤ} (h : x ^ n = 0) : x = 0 :=
classical.by_contradiction $ λ hx, fpow_ne_zero_of_ne_zero hx n h

lemma fpow_ne_zero {x : G₀} (n : ℤ) : x ≠ 0 → x ^ n ≠ 0 :=
mt fpow_eq_zero

theorem fpow_neg_mul_fpow_self (n : ℤ) {x : G₀} (h : x ≠ 0) :
  x ^ (-n) * x ^ n = 1 :=
begin
  rw [fpow_neg],
  exact inv_mul_cancel (fpow_ne_zero n h)
end

theorem one_div_pow {a : G₀} (n : ℕ) :
  (1 / a) ^ n = 1 / a ^ n :=
by simp only [one_div, inv_pow']

theorem one_div_fpow {a : G₀} (n : ℤ) :
  (1 / a) ^ n = 1 / a ^ n :=
by simp only [one_div, inv_fpow]

end int_pow

section
variables {G₀ : Type*} [comm_group_with_zero G₀]

@[simp] theorem div_pow (a b : G₀) (n : ℕ) :
  (a / b) ^ n = a ^ n / b ^ n :=
by simp only [div_eq_mul_inv, mul_pow, inv_pow']

@[simp] theorem div_fpow (a : G₀) {b : G₀} (n : ℤ) :
  (a / b) ^ n = a ^ n / b ^ n :=
by simp only [div_eq_mul_inv, mul_fpow, inv_fpow]

lemma div_sq_cancel {a : G₀} (ha : a ≠ 0) (b : G₀) : a ^ 2 * b / a = a * b :=
by rw [pow_two, mul_assoc, mul_div_cancel_left _ ha]

end

/-- If a monoid homomorphism `f` between two `group_with_zero`s maps `0` to `0`, then it maps `x^n`,
`n : ℤ`, to `(f x)^n`. -/
lemma monoid_hom.map_fpow {G₀ G₀' : Type*} [group_with_zero G₀] [group_with_zero G₀']
  (f : G₀ →* G₀') (h0 : f 0 = 0) (x : G₀) :
  ∀ n : ℤ, f (x ^ n) = f x ^ n
| (n : ℕ) := f.map_pow x n
| -[1+n] := (f.map_inv' h0 _).trans $ congr_arg _ $ f.map_pow x _
