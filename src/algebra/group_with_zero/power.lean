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

@[simp] theorem one_fzpow : ∀ (n : ℤ), (1 : G₀) ^ n = 1
| (n : ℕ) := by rw [zpow_coe_nat, one_pow]
| -[1+ n] := by rw [zpow_neg_succ_of_nat, one_pow, inv_one]

lemma zero_fzpow : ∀ z : ℤ, z ≠ 0 → (0 : G₀) ^ z = 0
| (n : ℕ) h := by { rw [zpow_coe_nat, zero_pow'], simpa using h }
| -[1+n]  h := by simp

lemma fzero_pow_eq (n : ℤ) : (0 : G₀) ^ n = if n = 0 then 1 else 0 :=
begin
  split_ifs with h,
  { rw [h, zpow_zero] },
  { rw [zero_fzpow _ h] }
end

@[simp] theorem fzpow_neg (a : G₀) : ∀ (n : ℤ), a ^ -n = (a ^ n)⁻¹
| (n+1:ℕ) := div_inv_monoid.zpow_neg' _ _
| 0       := by { change a ^ (0 : ℤ) = (a ^ (0 : ℤ))⁻¹, simp }
| -[1+ n] := by { rw [zpow_neg_succ_of_nat, inv_inv₀, ← zpow_coe_nat], refl }

theorem fzpow_neg_one (x : G₀) : x ^ (-1:ℤ) = x⁻¹ :=
by { rw [← congr_arg has_inv.inv (pow_one x), fzpow_neg, ← zpow_coe_nat], refl }

theorem inv_fzpow (a : G₀) : ∀n:ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
| (n : ℕ) := by rw [zpow_coe_nat, zpow_coe_nat, inv_pow₀]
| -[1+ n] := by rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat, inv_pow₀]

lemma fzpow_add_one {a : G₀} (ha : a ≠ 0) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
| (n : ℕ)    := by simp [← int.coe_nat_succ, pow_succ']
| -[1+0]     := by simp [int.neg_succ_of_nat_eq, ha]
| -[1+(n+1)] := by rw [int.neg_succ_of_nat_eq, fzpow_neg, neg_add, neg_add_cancel_right, fzpow_neg,
  ← int.coe_nat_succ, zpow_coe_nat, zpow_coe_nat, pow_succ _ (n + 1), mul_inv_rev₀, mul_assoc,
  inv_mul_cancel ha, mul_one]

lemma fzpow_sub_one {a : G₀} (ha : a ≠ 0) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
calc a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ : by rw [mul_assoc, mul_inv_cancel ha, mul_one]
             ... = a^n * a⁻¹             : by rw [← fzpow_add_one ha, sub_add_cancel]

lemma fzpow_add {a : G₀} (ha : a ≠ 0) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n :=
begin
  induction n using int.induction_on with n ihn n ihn,
  case hz : { simp },
  { simp only [← add_assoc, fzpow_add_one ha, ihn, mul_assoc] },
  { rw [fzpow_sub_one ha, ← mul_assoc, ← ihn, ← fzpow_sub_one ha, add_sub_assoc] }
end

lemma fzpow_add' {a : G₀} {m n : ℤ} (h : a ≠ 0 ∨ m + n ≠ 0 ∨ m = 0 ∧ n = 0) :
  a ^ (m + n) = a ^ m * a ^ n :=
begin
  by_cases hm : m = 0, { simp [hm] },
  by_cases hn : n = 0, { simp [hn] },
  by_cases ha : a = 0,
  { subst a,
    simp only [false_or, eq_self_iff_true, not_true, ne.def, hm, hn, false_and, or_false] at h,
    rw [zero_fzpow _ h, zero_fzpow _ hm, zero_mul] },
  { exact fzpow_add ha m n }
end

theorem fzpow_one_add {a : G₀} (h : a ≠ 0) (i : ℤ) : a ^ (1 + i) = a * a ^ i :=
by rw [fzpow_add h, zpow_one]

theorem semiconj_by.fzpow_right {a x y : G₀} (h : semiconj_by a x y) :
  ∀ m : ℤ, semiconj_by a (x^m) (y^m)
| (n : ℕ) := by simp [h.pow_right n]
| -[1+n]  := by simp [(h.pow_right (n + 1)).inv_right₀]

theorem commute.fzpow_right {a b : G₀} (h : commute a b) : ∀ m : ℤ, commute a (b^m) :=
h.fzpow_right

theorem commute.fzpow_left {a b : G₀} (h : commute a b) (m : ℤ) : commute (a^m) b :=
(h.symm.fzpow_right m).symm

theorem commute.fzpow_fzpow {a b : G₀} (h : commute a b) (m n : ℤ) : commute (a^m) (b^n) :=
(h.fzpow_left m).fzpow_right n

theorem commute.fzpow_self (a : G₀) (n : ℤ) : commute (a^n) a := (commute.refl a).fzpow_left n

theorem commute.self_fzpow (a : G₀) (n : ℤ) : commute a (a^n) := (commute.refl a).fzpow_right n

theorem commute.fzpow_fzpow_self (a : G₀) (m n : ℤ) : commute (a^m) (a^n) :=
(commute.refl a).fzpow_fzpow m n

theorem fzpow_bit0 (a : G₀) (n : ℤ) : a ^ bit0 n = a ^ n * a ^ n :=
begin
  apply fzpow_add', right,
  by_cases hn : n = 0,
  { simp [hn] },
  { simp [← two_mul, hn, two_ne_zero] }
end

theorem fzpow_bit1 (a : G₀) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a :=
begin
  rw [← fzpow_bit0, bit1, fzpow_add', zpow_one],
  right, left,
  apply bit1_ne_zero
end

theorem fzpow_mul (a : G₀) : ∀ m n : ℤ, a ^ (m * n) = (a ^ m) ^ n
| (m : ℕ) (n : ℕ) := by { rw [zpow_coe_nat, zpow_coe_nat, ← pow_mul, ← zpow_coe_nat], refl }
| (m : ℕ) -[1+ n] := by { rw [zpow_coe_nat, zpow_neg_succ_of_nat, ← pow_mul, coe_nat_mul_neg_succ,
    fzpow_neg, inv_inj₀, ← zpow_coe_nat], refl }
| -[1+ m] (n : ℕ) := by { rw [zpow_coe_nat, zpow_neg_succ_of_nat, ← inv_pow₀, ← pow_mul,
    neg_succ_mul_coe_nat, fzpow_neg, inv_pow₀, inv_inj₀, ← zpow_coe_nat], refl }
| -[1+ m] -[1+ n] := by { rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat, neg_succ_mul_neg_succ,
    inv_pow₀, inv_inv₀, ← pow_mul, ← zpow_coe_nat], refl }

theorem fzpow_mul' (a : G₀) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m :=
by rw [mul_comm, fzpow_mul]

@[simp, norm_cast] lemma units.coe_zpow₀ (u : units G₀) :
  ∀ (n : ℤ), ((u ^ n : units G₀) : G₀) = u ^ n
| (n : ℕ) := by { rw [zpow_coe_nat, zpow_coe_nat], exact u.coe_pow n }
| -[1+k] := by rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat, units.coe_inv', u.coe_pow]

lemma fzpow_ne_zero_of_ne_zero {a : G₀} (ha : a ≠ 0) : ∀ (z : ℤ), a ^ z ≠ 0
| (n : ℕ) := by { rw zpow_coe_nat, exact pow_ne_zero _ ha }
| -[1+n]  := by { rw zpow_neg_succ_of_nat, exact inv_ne_zero (pow_ne_zero _ ha) }

lemma fzpow_sub {a : G₀} (ha : a ≠ 0) (z1 z2 : ℤ) : a ^ (z1 - z2) = a ^ z1 / a ^ z2 :=
by rw [sub_eq_add_neg, fzpow_add ha, fzpow_neg, div_eq_mul_inv]

lemma commute.mul_fzpow {a b : G₀} (h : commute a b) :
  ∀ (i : ℤ), (a * b) ^ i = (a ^ i) * (b ^ i)
| (n : ℕ) := by simp [h.mul_pow n]
| -[1+n]  := by simp [h.mul_pow, (h.pow_pow _ _).eq, mul_inv_rev₀]

lemma mul_fzpow {G₀ : Type*} [comm_group_with_zero G₀] (a b : G₀) (m : ℤ):
  (a * b) ^ m = (a ^ m) * (b ^ m) :=
(commute.all a b).mul_fzpow m

theorem fzpow_bit0' (a : G₀) (n : ℤ) : a ^ bit0 n = (a * a) ^ n :=
(fzpow_bit0 a n).trans ((commute.refl a).mul_fzpow n).symm

theorem fzpow_bit1' (a : G₀) (n : ℤ) : a ^ bit1 n = (a * a) ^ n * a :=
by rw [fzpow_bit1, (commute.refl a).mul_fzpow]

lemma fzpow_eq_zero {x : G₀} {n : ℤ} (h : x ^ n = 0) : x = 0 :=
classical.by_contradiction $ λ hx, fzpow_ne_zero_of_ne_zero hx n h

lemma fzpow_ne_zero {x : G₀} (n : ℤ) : x ≠ 0 → x ^ n ≠ 0 :=
mt fzpow_eq_zero

theorem fzpow_neg_mul_fzpow_self (n : ℤ) {x : G₀} (h : x ≠ 0) :
  x ^ (-n) * x ^ n = 1 :=
begin
  rw [fzpow_neg],
  exact inv_mul_cancel (fzpow_ne_zero n h)
end

theorem one_div_pow {a : G₀} (n : ℕ) :
  (1 / a) ^ n = 1 / a ^ n :=
by simp only [one_div, inv_pow₀]

theorem one_div_fzpow {a : G₀} (n : ℤ) :
  (1 / a) ^ n = 1 / a ^ n :=
by simp only [one_div, inv_fzpow]

@[simp] lemma inv_fzpow' {a : G₀} (n : ℤ) :
  (a ⁻¹) ^ n = a ^ (-n) :=
by { rw [inv_fzpow, ← fzpow_neg_one, ← fzpow_mul], simp }

end int_pow

section
variables {G₀ : Type*} [comm_group_with_zero G₀]

@[simp] theorem div_pow (a b : G₀) (n : ℕ) :
  (a / b) ^ n = a ^ n / b ^ n :=
by simp only [div_eq_mul_inv, mul_pow, inv_pow₀]

@[simp] theorem div_fzpow (a : G₀) {b : G₀} (n : ℤ) :
  (a / b) ^ n = a ^ n / b ^ n :=
by simp only [div_eq_mul_inv, mul_fzpow, inv_fzpow]

lemma div_sq_cancel {a : G₀} (ha : a ≠ 0) (b : G₀) : a ^ 2 * b / a = a * b :=
by rw [sq, mul_assoc, mul_div_cancel_left _ ha]

end

/-- If a monoid homomorphism `f` between two `group_with_zero`s maps `0` to `0`, then it maps `x^n`,
`n : ℤ`, to `(f x)^n`. -/
lemma monoid_with_zero_hom.map_fzpow {G₀ G₀' : Type*} [group_with_zero G₀] [group_with_zero G₀']
  (f : monoid_with_zero_hom G₀ G₀') (x : G₀) :
  ∀ n : ℤ, f (x ^ n) = f x ^ n
| (n : ℕ) := by { rw [zpow_coe_nat, zpow_coe_nat], exact f.to_monoid_hom.map_pow x n }
| -[1+n] := begin
    rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat],
    exact ((f.map_inv _).trans $ congr_arg _ $ f.to_monoid_hom.map_pow x _)
  end

-- I haven't been able to find a better home for this:
-- it belongs with other lemmas on `linear_ordered_field`, but
-- we need to wait until `fzpow` has been defined in this file.
section
variables {R : Type*} [linear_ordered_field R] {a : R}

lemma pow_minus_two_nonneg : 0 ≤ a^(-2 : ℤ) :=
begin
  simp only [inv_nonneg, fzpow_neg],
  change 0 ≤ a ^ ((2 : ℕ) : ℤ),
  rw zpow_coe_nat,
  apply sq_nonneg,
end

end
