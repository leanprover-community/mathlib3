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

section zero
variables {M : Type*} [monoid_with_zero M]

@[simp] lemma zero_pow' : ∀ n : ℕ, n ≠ 0 → (0 : M) ^ n = 0
| 0     h := absurd rfl h
| (k+1) h := by { rw [pow_succ], exact zero_mul _ }

lemma ne_zero_pow {a : M} {n : ℕ} (hn : n ≠ 0) : a ^ n ≠ 0 → a ≠ 0 :=
by { contrapose!, rintro rfl, exact zero_pow' n hn }

@[simp] lemma zero_pow_eq_zero [nontrivial M] {n : ℕ} : (0 : M) ^ n = 0 ↔ 0 < n :=
begin
  split; intro h,
  { rw [pos_iff_ne_zero], rintro rfl, simpa using h },
  { exact zero_pow' n h.ne.symm }
end

end zero

section group_with_zero
variables {G₀ : Type*} [group_with_zero G₀]

section nat_pow

@[simp, field_simps] theorem inv_pow₀ (a : G₀) (n : ℕ) : (a⁻¹) ^ n = (a ^ n)⁻¹ :=
begin
  induction n with n ih,
  { rw [pow_zero, pow_zero], exact inv_one.symm },
  { rw [pow_succ', pow_succ, ih, mul_inv_rev₀] }
end

theorem pow_sub₀ (a : G₀) {m n : ℕ} (ha : a ≠ 0) (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ :=
have h1 : m - n + n = m, from tsub_add_cancel_of_le h,
have h2 : a ^ (m - n) * a ^ n = a ^ m, by rw [←pow_add, h1],
by simpa only [div_eq_mul_inv] using eq_div_of_mul_eq (pow_ne_zero _ ha) h2

theorem pow_inv_comm₀ (a : G₀) (m n : ℕ) : (a⁻¹) ^ m * a ^ n = a ^ n * (a⁻¹) ^ m :=
(commute.refl a).inv_left₀.pow_pow m n

end nat_pow

end group_with_zero

section int_pow
open int
variables {G₀ : Type*} [group_with_zero G₀]

local attribute [ematch] le_of_lt

@[simp] theorem one_fpow : ∀ (n : ℤ), (1 : G₀) ^ n = 1
| (n : ℕ) := by rw [gpow_coe_nat, one_pow]
| -[1+ n] := by rw [gpow_neg_succ_of_nat, one_pow, inv_one]

lemma zero_fpow : ∀ z : ℤ, z ≠ 0 → (0 : G₀) ^ z = 0
| (n : ℕ) h := by { rw [gpow_coe_nat, zero_pow'], simpa using h }
| -[1+n]  h := by simp

lemma fzero_pow_eq (n : ℤ) : (0 : G₀) ^ n = if n = 0 then 1 else 0 :=
begin
  split_ifs with h,
  { rw [h, gpow_zero] },
  { rw [zero_fpow _ h] }
end

@[simp] theorem fpow_neg (a : G₀) : ∀ (n : ℤ), a ^ -n = (a ^ n)⁻¹
| (n+1:ℕ) := div_inv_monoid.gpow_neg' _ _
| 0       := by { change a ^ (0 : ℤ) = (a ^ (0 : ℤ))⁻¹, simp }
| -[1+ n] := by { rw [gpow_neg_succ_of_nat, inv_inv₀, ← gpow_coe_nat], refl }

theorem fpow_neg_one (x : G₀) : x ^ (-1:ℤ) = x⁻¹ :=
by { rw [← congr_arg has_inv.inv (pow_one x), fpow_neg, ← gpow_coe_nat], refl }

theorem inv_fpow (a : G₀) : ∀n:ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
| (n : ℕ) := by rw [gpow_coe_nat, gpow_coe_nat, inv_pow₀]
| -[1+ n] := by rw [gpow_neg_succ_of_nat, gpow_neg_succ_of_nat, inv_pow₀]

lemma fpow_add_one {a : G₀} (ha : a ≠ 0) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
| (n : ℕ)    := by simp [← int.coe_nat_succ, pow_succ']
| -[1+0]     := by simp [int.neg_succ_of_nat_eq, ha]
| -[1+(n+1)] := by rw [int.neg_succ_of_nat_eq, fpow_neg, neg_add, neg_add_cancel_right, fpow_neg,
  ← int.coe_nat_succ, gpow_coe_nat, gpow_coe_nat, pow_succ _ (n + 1), mul_inv_rev₀, mul_assoc,
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

lemma fpow_add' {a : G₀} {m n : ℤ} (h : a ≠ 0 ∨ m + n ≠ 0 ∨ m = 0 ∧ n = 0) :
  a ^ (m + n) = a ^ m * a ^ n :=
begin
  by_cases hm : m = 0, { simp [hm] },
  by_cases hn : n = 0, { simp [hn] },
  by_cases ha : a = 0,
  { subst a,
    simp only [false_or, eq_self_iff_true, not_true, ne.def, hm, hn, false_and, or_false] at h,
    rw [zero_fpow _ h, zero_fpow _ hm, zero_mul] },
  { exact fpow_add ha m n }
end

theorem fpow_one_add {a : G₀} (h : a ≠ 0) (i : ℤ) : a ^ (1 + i) = a * a ^ i :=
by rw [fpow_add h, gpow_one]

theorem semiconj_by.fpow_right {a x y : G₀} (h : semiconj_by a x y) :
  ∀ m : ℤ, semiconj_by a (x^m) (y^m)
| (n : ℕ) := by simp [h.pow_right n]
| -[1+n]  := by simp [(h.pow_right (n + 1)).inv_right₀]

theorem commute.fpow_right {a b : G₀} (h : commute a b) : ∀ m : ℤ, commute a (b^m) :=
h.fpow_right

theorem commute.fpow_left {a b : G₀} (h : commute a b) (m : ℤ) : commute (a^m) b :=
(h.symm.fpow_right m).symm

theorem commute.fpow_fpow {a b : G₀} (h : commute a b) (m n : ℤ) : commute (a^m) (b^n) :=
(h.fpow_left m).fpow_right n

theorem commute.fpow_self (a : G₀) (n : ℤ) : commute (a^n) a := (commute.refl a).fpow_left n

theorem commute.self_fpow (a : G₀) (n : ℤ) : commute a (a^n) := (commute.refl a).fpow_right n

theorem commute.fpow_fpow_self (a : G₀) (m n : ℤ) : commute (a^m) (a^n) :=
(commute.refl a).fpow_fpow m n

theorem fpow_bit0 (a : G₀) (n : ℤ) : a ^ bit0 n = a ^ n * a ^ n :=
begin
  apply fpow_add', right,
  by_cases hn : n = 0,
  { simp [hn] },
  { simp [← two_mul, hn, two_ne_zero] }
end

theorem fpow_bit1 (a : G₀) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a :=
begin
  rw [← fpow_bit0, bit1, fpow_add', gpow_one],
  right, left,
  apply bit1_ne_zero
end

theorem fpow_mul (a : G₀) : ∀ m n : ℤ, a ^ (m * n) = (a ^ m) ^ n
| (m : ℕ) (n : ℕ) := by { rw [gpow_coe_nat, gpow_coe_nat, ← pow_mul, ← gpow_coe_nat], refl }
| (m : ℕ) -[1+ n] := by { rw [gpow_coe_nat, gpow_neg_succ_of_nat, ← pow_mul, coe_nat_mul_neg_succ,
    fpow_neg, inv_inj₀, ← gpow_coe_nat], refl }
| -[1+ m] (n : ℕ) := by { rw [gpow_coe_nat, gpow_neg_succ_of_nat, ← inv_pow₀, ← pow_mul,
    neg_succ_mul_coe_nat, fpow_neg, inv_pow₀, inv_inj₀, ← gpow_coe_nat], refl }
| -[1+ m] -[1+ n] := by { rw [gpow_neg_succ_of_nat, gpow_neg_succ_of_nat, neg_succ_mul_neg_succ,
    inv_pow₀, inv_inv₀, ← pow_mul, ← gpow_coe_nat], refl }

theorem fpow_mul' (a : G₀) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m :=
by rw [mul_comm, fpow_mul]

@[simp, norm_cast] lemma units.coe_gpow₀ (u : units G₀) :
  ∀ (n : ℤ), ((u ^ n : units G₀) : G₀) = u ^ n
| (n : ℕ) := by { rw [gpow_coe_nat, gpow_coe_nat], exact u.coe_pow n }
| -[1+k] := by rw [gpow_neg_succ_of_nat, gpow_neg_succ_of_nat, units.coe_inv', u.coe_pow]

lemma fpow_ne_zero_of_ne_zero {a : G₀} (ha : a ≠ 0) : ∀ (z : ℤ), a ^ z ≠ 0
| (n : ℕ) := by { rw gpow_coe_nat, exact pow_ne_zero _ ha }
| -[1+n]  := by { rw gpow_neg_succ_of_nat, exact inv_ne_zero (pow_ne_zero _ ha) }

lemma fpow_sub {a : G₀} (ha : a ≠ 0) (z1 z2 : ℤ) : a ^ (z1 - z2) = a ^ z1 / a ^ z2 :=
by rw [sub_eq_add_neg, fpow_add ha, fpow_neg, div_eq_mul_inv]

lemma commute.mul_fpow {a b : G₀} (h : commute a b) :
  ∀ (i : ℤ), (a * b) ^ i = (a ^ i) * (b ^ i)
| (n : ℕ) := by simp [h.mul_pow n]
| -[1+n]  := by simp [h.mul_pow, (h.pow_pow _ _).eq, mul_inv_rev₀]

lemma mul_fpow {G₀ : Type*} [comm_group_with_zero G₀] (a b : G₀) (m : ℤ):
  (a * b) ^ m = (a ^ m) * (b ^ m) :=
(commute.all a b).mul_fpow m

theorem fpow_bit0' (a : G₀) (n : ℤ) : a ^ bit0 n = (a * a) ^ n :=
(fpow_bit0 a n).trans ((commute.refl a).mul_fpow n).symm

theorem fpow_bit1' (a : G₀) (n : ℤ) : a ^ bit1 n = (a * a) ^ n * a :=
by rw [fpow_bit1, (commute.refl a).mul_fpow]

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
by simp only [one_div, inv_pow₀]

theorem one_div_fpow {a : G₀} (n : ℤ) :
  (1 / a) ^ n = 1 / a ^ n :=
by simp only [one_div, inv_fpow]

@[simp] lemma inv_fpow' {a : G₀} (n : ℤ) :
  (a ⁻¹) ^ n = a ^ (-n) :=
by { rw [inv_fpow, ← fpow_neg_one, ← fpow_mul], simp }

end int_pow

section
variables {G₀ : Type*} [comm_group_with_zero G₀]

@[simp] theorem div_pow (a b : G₀) (n : ℕ) :
  (a / b) ^ n = a ^ n / b ^ n :=
by simp only [div_eq_mul_inv, mul_pow, inv_pow₀]

@[simp] theorem div_fpow (a : G₀) {b : G₀} (n : ℤ) :
  (a / b) ^ n = a ^ n / b ^ n :=
by simp only [div_eq_mul_inv, mul_fpow, inv_fpow]

lemma div_sq_cancel {a : G₀} (ha : a ≠ 0) (b : G₀) : a ^ 2 * b / a = a * b :=
by rw [sq, mul_assoc, mul_div_cancel_left _ ha]

end

/-- If a monoid homomorphism `f` between two `group_with_zero`s maps `0` to `0`, then it maps `x^n`,
`n : ℤ`, to `(f x)^n`. -/
lemma monoid_with_zero_hom.map_fpow {G₀ G₀' : Type*} [group_with_zero G₀] [group_with_zero G₀']
  (f : monoid_with_zero_hom G₀ G₀') (x : G₀) :
  ∀ n : ℤ, f (x ^ n) = f x ^ n
| (n : ℕ) := by { rw [gpow_coe_nat, gpow_coe_nat], exact f.to_monoid_hom.map_pow x n }
| -[1+n] := begin
    rw [gpow_neg_succ_of_nat, gpow_neg_succ_of_nat],
    exact ((f.map_inv _).trans $ congr_arg _ $ f.to_monoid_hom.map_pow x _)
  end

-- I haven't been able to find a better home for this:
-- it belongs with other lemmas on `linear_ordered_field`, but
-- we need to wait until `fpow` has been defined in this file.
section
variables {R : Type*} [linear_ordered_field R] {a : R}

lemma pow_minus_two_nonneg : 0 ≤ a^(-2 : ℤ) :=
begin
  simp only [inv_nonneg, fpow_neg],
  change 0 ≤ a ^ ((2 : ℕ) : ℤ),
  rw gpow_coe_nat,
  apply sq_nonneg,
end

end
