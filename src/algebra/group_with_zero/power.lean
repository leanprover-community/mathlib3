/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import algebra.group_power.lemmas

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

lemma ring.inverse_pow (r : M) : ∀ (n : ℕ), ring.inverse r ^ n = ring.inverse (r ^ n)
| 0 := by rw [pow_zero, pow_zero, ring.inverse_one]
| (n + 1) := by rw [pow_succ, pow_succ', ring.mul_inverse_rev' ((commute.refl r).pow_left n),
                    ring.inverse_pow]

end zero

section group_with_zero
variables {G₀ : Type*} [group_with_zero G₀] {a : G₀} {m n : ℕ}

section nat_pow

theorem pow_sub₀ (a : G₀) {m n : ℕ} (ha : a ≠ 0) (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ :=
have h1 : m - n + n = m, from tsub_add_cancel_of_le h,
have h2 : a ^ (m - n) * a ^ n = a ^ m, by rw [←pow_add, h1],
by simpa only [div_eq_mul_inv] using eq_div_of_mul_eq (pow_ne_zero _ ha) h2

lemma pow_sub_of_lt (a : G₀) {m n : ℕ} (h : n < m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ :=
begin
  obtain rfl | ha := eq_or_ne a 0,
  { rw [zero_pow (tsub_pos_of_lt h), zero_pow (n.zero_le.trans_lt h), zero_mul] },
  { exact pow_sub₀ _ ha h.le }
end

theorem pow_inv_comm₀ (a : G₀) (m n : ℕ) : (a⁻¹) ^ m * a ^ n = a ^ n * (a⁻¹) ^ m :=
(commute.refl a).inv_left₀.pow_pow m n

lemma inv_pow_sub₀ (ha : a ≠ 0) (h : n ≤ m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n :=
by rw [pow_sub₀ _ (inv_ne_zero ha) h, inv_pow, inv_pow, inv_inv]

lemma inv_pow_sub_of_lt (a : G₀) (h : n < m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n :=
by rw [pow_sub_of_lt a⁻¹ h, inv_pow, inv_pow, inv_inv]

end nat_pow

end group_with_zero

section zpow
open int
variables {G₀ : Type*} [group_with_zero G₀]

local attribute [ematch] le_of_lt

lemma zero_zpow : ∀ z : ℤ, z ≠ 0 → (0 : G₀) ^ z = 0
| (n : ℕ) h := by { rw [zpow_coe_nat, zero_pow'], simpa using h }
| -[1+n]  h := by simp

lemma zero_zpow_eq (n : ℤ) : (0 : G₀) ^ n = if n = 0 then 1 else 0 :=
begin
  split_ifs with h,
  { rw [h, zpow_zero] },
  { rw [zero_zpow _ h] }
end

lemma zpow_add_one₀ {a : G₀} (ha : a ≠ 0) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
| (n : ℕ)    := by simp [← int.coe_nat_succ, pow_succ']
| -[1+n] := by rw [int.neg_succ_of_nat_eq, zpow_neg, neg_add, neg_add_cancel_right, zpow_neg,
  ← int.coe_nat_succ, zpow_coe_nat, zpow_coe_nat, pow_succ _ n, mul_inv_rev, mul_assoc,
  inv_mul_cancel ha, mul_one]

lemma zpow_sub_one₀ {a : G₀} (ha : a ≠ 0) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
calc a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ : by rw [mul_assoc, mul_inv_cancel ha, mul_one]
             ... = a^n * a⁻¹             : by rw [← zpow_add_one₀ ha, sub_add_cancel]

lemma zpow_add₀ {a : G₀} (ha : a ≠ 0) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n :=
begin
  induction n using int.induction_on with n ihn n ihn,
  case hz : { simp },
  { simp only [← add_assoc, zpow_add_one₀ ha, ihn, mul_assoc] },
  { rw [zpow_sub_one₀ ha, ← mul_assoc, ← ihn, ← zpow_sub_one₀ ha, add_sub_assoc] }
end

lemma zpow_add' {a : G₀} {m n : ℤ} (h : a ≠ 0 ∨ m + n ≠ 0 ∨ m = 0 ∧ n = 0) :
  a ^ (m + n) = a ^ m * a ^ n :=
begin
  by_cases hm : m = 0, { simp [hm] },
  by_cases hn : n = 0, { simp [hn] },
  by_cases ha : a = 0,
  { subst a,
    simp only [false_or, eq_self_iff_true, not_true, ne.def, hm, hn, false_and, or_false] at h,
    rw [zero_zpow _ h, zero_zpow _ hm, zero_mul] },
  { exact zpow_add₀ ha m n }
end

theorem zpow_one_add₀ {a : G₀} (h : a ≠ 0) (i : ℤ) : a ^ (1 + i) = a * a ^ i :=
by rw [zpow_add₀ h, zpow_one]

theorem semiconj_by.zpow_right₀ {a x y : G₀} (h : semiconj_by a x y) :
  ∀ m : ℤ, semiconj_by a (x^m) (y^m)
| (n : ℕ) := by simp [h.pow_right n]
| -[1+n]  := by simp [(h.pow_right (n + 1)).inv_right₀]

theorem commute.zpow_right₀ {a b : G₀} (h : commute a b) : ∀ m : ℤ, commute a (b^m) :=
h.zpow_right₀

theorem commute.zpow_left₀ {a b : G₀} (h : commute a b) (m : ℤ) : commute (a^m) b :=
(h.symm.zpow_right₀ m).symm

theorem commute.zpow_zpow₀ {a b : G₀} (h : commute a b) (m n : ℤ) : commute (a^m) (b^n) :=
(h.zpow_left₀ m).zpow_right₀ n

theorem commute.zpow_self₀ (a : G₀) (n : ℤ) : commute (a^n) a := (commute.refl a).zpow_left₀ n

theorem commute.self_zpow₀ (a : G₀) (n : ℤ) : commute a (a^n) := (commute.refl a).zpow_right₀ n

theorem commute.zpow_zpow_self₀ (a : G₀) (m n : ℤ) : commute (a^m) (a^n) :=
(commute.refl a).zpow_zpow₀ m n

theorem zpow_bit1₀ (a : G₀) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a :=
begin
  rw [← zpow_bit0, bit1, zpow_add', zpow_one],
  right, left,
  apply bit1_ne_zero
end

@[simp, norm_cast] lemma units.coe_zpow₀ (u : G₀ˣ) :
  ∀ (n : ℤ), ((u ^ n : G₀ˣ) : G₀) = u ^ n
| (n : ℕ) := by { rw [zpow_coe_nat, zpow_coe_nat], exact u.coe_pow n }
| -[1+k] := by rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat, units.coe_inv', u.coe_pow]

lemma zpow_ne_zero_of_ne_zero {a : G₀} (ha : a ≠ 0) : ∀ (z : ℤ), a ^ z ≠ 0
| (n : ℕ) := by { rw zpow_coe_nat, exact pow_ne_zero _ ha }
| -[1+n]  := by { rw zpow_neg_succ_of_nat, exact inv_ne_zero (pow_ne_zero _ ha) }

lemma zpow_sub₀ {a : G₀} (ha : a ≠ 0) (z1 z2 : ℤ) : a ^ (z1 - z2) = a ^ z1 / a ^ z2 :=
by rw [sub_eq_add_neg, zpow_add₀ ha, zpow_neg, div_eq_mul_inv]

theorem zpow_bit1' (a : G₀) (n : ℤ) : a ^ bit1 n = (a * a) ^ n * a :=
by rw [zpow_bit1₀, (commute.refl a).mul_zpow]

lemma zpow_eq_zero {x : G₀} {n : ℤ} (h : x ^ n = 0) : x = 0 :=
classical.by_contradiction $ λ hx, zpow_ne_zero_of_ne_zero hx n h

lemma zpow_eq_zero_iff {a : G₀} {n : ℤ} (hn : 0 < n) :
  a ^ n = 0 ↔ a = 0 :=
begin
  refine ⟨zpow_eq_zero, _⟩,
  rintros rfl,
  exact zero_zpow _ hn.ne'
end

lemma zpow_ne_zero {x : G₀} (n : ℤ) : x ≠ 0 → x ^ n ≠ 0 :=
mt zpow_eq_zero

theorem zpow_neg_mul_zpow_self (n : ℤ) {x : G₀} (h : x ≠ 0) :
  x ^ (-n) * x ^ n = 1 :=
begin
  rw [zpow_neg],
  exact inv_mul_cancel (zpow_ne_zero n h)
end

end zpow

section
variables {G₀ : Type*} [comm_group_with_zero G₀]

lemma div_sq_cancel (a b : G₀) : a ^ 2 * b / a = a * b :=
begin
  by_cases ha : a = 0,
  { simp [ha] },
  rw [sq, mul_assoc, mul_div_cancel_left _ ha]
end

end

/-- If a monoid homomorphism `f` between two `group_with_zero`s maps `0` to `0`, then it maps `x^n`,
`n : ℤ`, to `(f x)^n`. -/
lemma monoid_with_zero_hom.map_zpow {G₀ G₀' : Type*} [group_with_zero G₀] [group_with_zero G₀']
  (f : G₀ →*₀ G₀') (x : G₀) :
  ∀ n : ℤ, f (x ^ n) = f x ^ n
| (n : ℕ) := by { rw [zpow_coe_nat, zpow_coe_nat], exact f.to_monoid_hom.map_pow x n }
| -[1+n] := begin
    rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat],
    exact ((f.map_inv _).trans $ congr_arg _ $ f.to_monoid_hom.map_pow x _)
  end

-- I haven't been able to find a better home for this:
-- it belongs with other lemmas on `linear_ordered_field`, but
-- we need to wait until `zpow` has been defined in this file.
section
variables {R : Type*} [linear_ordered_field R] {a : R}

lemma pow_minus_two_nonneg : 0 ≤ a^(-2 : ℤ) :=
begin
  simp only [inv_nonneg, zpow_neg],
  change 0 ≤ a ^ ((2 : ℕ) : ℤ),
  rw zpow_coe_nat,
  apply sq_nonneg,
end

end
