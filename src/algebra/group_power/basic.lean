/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import algebra.divisibility.basic
import algebra.group.commute
import algebra.group.type_tags

/-!
# Power operations on monoids and groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The power operation on monoids and groups.
We separate this from group, because it depends on `ℕ`,
which in turn depends on other parts of algebra.

This module contains lemmas about `a ^ n` and `n • a`, where `n : ℕ` or `n : ℤ`.
Further lemmas can be found in `algebra.group_power.lemmas`.

The analogous results for groups with zero can be found in `algebra.group_with_zero.power`.

## Notation

- `a ^ n` is used as notation for `has_pow.pow a n`; in this file `n : ℕ` or `n : ℤ`.
- `n • a` is used as notation for `has_smul.smul n a`; in this file `n : ℕ` or `n : ℤ`.

## Implementation details

We adopt the convention that `0^0 = 1`.
-/

universes u v w x y z u₁ u₂

variables {α : Type*} {M : Type u} {N : Type v} {G : Type w} {H : Type x} {A : Type y} {B : Type z}
  {R : Type u₁} {S : Type u₂}

/-!
### Commutativity

First we prove some facts about `semiconj_by` and `commute`. They do not require any theory about
`pow` and/or `nsmul` and will be useful later in this file.
-/

section has_pow
variables [has_pow M ℕ]

@[simp] lemma pow_ite (P : Prop) [decidable P] (a : M) (b c : ℕ) :
  a ^ (if P then b else c) = if P then a ^ b else a ^ c :=
by split_ifs; refl

@[simp] lemma ite_pow (P : Prop) [decidable P] (a b : M) (c : ℕ) :
  (if P then a else b) ^ c = if P then a ^ c else b ^ c :=
by split_ifs; refl

end has_pow

section monoid
variables [monoid M] [monoid N] [add_monoid A] [add_monoid B]

@[simp, to_additive one_nsmul]
theorem pow_one (a : M) : a^1 = a :=
by rw [pow_succ, pow_zero, mul_one]

/-- Note that most of the lemmas about powers of two refer to it as `sq`. -/
@[to_additive two_nsmul, nolint to_additive_doc]
theorem pow_two (a : M) : a^2 = a * a :=
by rw [pow_succ, pow_one]

alias pow_two ← sq

theorem pow_three' (a : M) : a^3 = a * a * a := by rw [pow_succ', pow_two]

theorem pow_three (a : M) : a^3 = a * (a * a) := by rw [pow_succ, pow_two]

@[to_additive]
theorem pow_mul_comm' (a : M) (n : ℕ) : a^n * a = a * a^n := commute.pow_self a n

@[to_additive add_nsmul]
theorem pow_add (a : M) (m n : ℕ) : a^(m + n) = a^m * a^n :=
by induction n with n ih; [rw [nat.add_zero, pow_zero, mul_one],
  rw [pow_succ', ← mul_assoc, ← ih, ← pow_succ', nat.add_assoc]]

@[simp] lemma pow_boole (P : Prop) [decidable P] (a : M) :
  a ^ (if P then 1 else 0) = if P then a else 1 :=
by simp

-- the attributes are intentionally out of order. `smul_zero` proves `nsmul_zero`.
@[to_additive nsmul_zero, simp] theorem one_pow (n : ℕ) : (1 : M)^n = 1 :=
by induction n with n ih; [exact pow_zero _, rw [pow_succ, ih, one_mul]]

@[to_additive mul_nsmul']
theorem pow_mul (a : M) (m n : ℕ) : a^(m * n) = (a^m)^n :=
begin
  induction n with n ih,
  { rw [nat.mul_zero, pow_zero, pow_zero] },
  { rw [nat.mul_succ, pow_add, pow_succ', ih] }
end

@[to_additive nsmul_left_comm]
lemma pow_right_comm (a : M) (m n : ℕ) : (a^m)^n = (a^n)^m :=
by rw [←pow_mul, nat.mul_comm, pow_mul]

@[to_additive mul_nsmul]
theorem pow_mul' (a : M) (m n : ℕ) : a^(m * n) = (a^n)^m :=
by rw [nat.mul_comm, pow_mul]

@[to_additive nsmul_add_sub_nsmul]
theorem pow_mul_pow_sub (a : M) {m n : ℕ} (h : m ≤ n) : a ^ m * a ^ (n - m) = a ^ n :=
by rw [←pow_add, nat.add_comm, nat.sub_add_cancel h]

@[to_additive sub_nsmul_nsmul_add]
theorem pow_sub_mul_pow (a : M) {m n : ℕ} (h : m ≤ n) : a ^ (n - m) * a ^ m = a ^ n :=
by rw [←pow_add, nat.sub_add_cancel h]

/-- If `x ^ n = 1`, then `x ^ m` is the same as `x ^ (m % n)` -/
@[to_additive nsmul_eq_mod_nsmul "If `n • x = 0`, then `m • x` is the same as `(m % n) • x`"]
lemma pow_eq_pow_mod {M : Type*} [monoid M] {x : M} (m : ℕ) {n : ℕ} (h : x ^ n = 1) :
  x ^ m = x ^ (m % n) :=
begin
  have t := congr_arg (λ a, x ^ a) ((nat.add_comm _ _).trans (nat.mod_add_div _ _)).symm,
  dsimp at t,
  rw [t, pow_add, pow_mul, h, one_pow, one_mul],
end

@[to_additive bit0_nsmul]
theorem pow_bit0 (a : M) (n : ℕ) : a ^ bit0 n = a^n * a^n := pow_add _ _ _

@[to_additive bit1_nsmul]
theorem pow_bit1 (a : M) (n : ℕ) : a ^ bit1 n = a^n * a^n * a :=
by rw [bit1, pow_succ', pow_bit0]

@[to_additive]
theorem pow_mul_comm (a : M) (m n : ℕ) : a^m * a^n = a^n * a^m :=
commute.pow_pow_self a m n

@[to_additive]
lemma commute.mul_pow {a b : M} (h : commute a b) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n :=
nat.rec_on n (by simp only [pow_zero, one_mul]) $ λ n ihn,
by simp only [pow_succ, ihn, ← mul_assoc, (h.pow_left n).right_comm]

@[to_additive bit0_nsmul']
theorem pow_bit0' (a : M) (n : ℕ) : a ^ bit0 n = (a * a) ^ n :=
by rw [pow_bit0, (commute.refl a).mul_pow]

@[to_additive bit1_nsmul']
theorem pow_bit1' (a : M) (n : ℕ) : a ^ bit1 n = (a * a) ^ n * a :=
by rw [bit1, pow_succ', pow_bit0']

@[to_additive]
lemma pow_mul_pow_eq_one {a b : M} (n : ℕ) (h : a * b = 1) :
  a ^ n * b ^ n = 1 :=
begin
  induction n with n hn,
  { simp },
  { calc a ^ n.succ * b ^ n.succ = a ^ n * a * (b * b ^ n) : by rw [pow_succ', pow_succ]
    ... = a ^ n * (a * b) * b ^ n : by simp only [mul_assoc]
    ... = 1 : by simp [h, hn] }
end

lemma dvd_pow {x y : M} (hxy : x ∣ y) :
  ∀ {n : ℕ} (hn : n ≠ 0), x ∣ y^n
| 0       hn := (hn rfl).elim
| (n + 1) hn := by { rw pow_succ, exact hxy.mul_right _ }

alias dvd_pow ← has_dvd.dvd.pow

lemma dvd_pow_self (a : M) {n : ℕ} (hn : n ≠ 0) : a ∣ a^n :=
dvd_rfl.pow hn

end monoid

/-!
### Commutative (additive) monoid
-/

section comm_monoid
variables [comm_monoid M] [add_comm_monoid A]

@[to_additive nsmul_add]
theorem mul_pow (a b : M) (n : ℕ) : (a * b)^n = a^n * b^n :=
(commute.all a b).mul_pow n


/-- The `n`th power map on a commutative monoid for a natural `n`, considered as a morphism of
monoids. -/
@[to_additive "Multiplication by a natural `n` on a commutative additive
monoid, considered as a morphism of additive monoids.", simps]
def pow_monoid_hom (n : ℕ) : M →* M :=
{ to_fun := (^ n),
  map_one' := one_pow _,
  map_mul' := λ a b, mul_pow a b n }

-- the below line causes the linter to complain :-/
-- attribute [simps] pow_monoid_hom nsmul_add_monoid_hom

end comm_monoid

section div_inv_monoid
variable [div_inv_monoid G]

open int

@[simp, to_additive one_zsmul]
theorem zpow_one (a : G) : a ^ (1:ℤ) = a :=
by { convert pow_one a using 1, exact zpow_coe_nat a 1 }

@[to_additive two_zsmul]
theorem zpow_two (a : G) : a ^ (2 : ℤ) = a * a :=
by { convert pow_two a using 1, exact zpow_coe_nat a 2 }

@[to_additive neg_one_zsmul]
theorem zpow_neg_one (x : G) : x ^ (-1:ℤ) = x⁻¹ :=
(zpow_neg_succ_of_nat x 0).trans $ congr_arg has_inv.inv (pow_one x)

@[to_additive]
theorem zpow_neg_coe_of_pos (a : G) : ∀ {n : ℕ}, 0 < n → a ^ -(n:ℤ) = (a ^ n)⁻¹
| (n+1) _ := zpow_neg_succ_of_nat _ _

end div_inv_monoid

section division_monoid
variables [division_monoid α] {a b : α}

@[simp, to_additive] lemma inv_pow (a : α) : ∀ n : ℕ, (a⁻¹) ^ n = (a ^ n)⁻¹
| 0       := by rw [pow_zero, pow_zero, inv_one]
| (n + 1) := by rw [pow_succ', pow_succ, inv_pow, mul_inv_rev]

-- the attributes are intentionally out of order. `smul_zero` proves `zsmul_zero`.
@[to_additive zsmul_zero, simp] lemma one_zpow : ∀ (n : ℤ), (1 : α) ^ n = 1
| (n : ℕ) := by rw [zpow_coe_nat, one_pow]
| -[1+ n] := by rw [zpow_neg_succ_of_nat, one_pow, inv_one]

@[simp, to_additive neg_zsmul] lemma zpow_neg (a : α) : ∀ (n : ℤ), a ^ -n = (a ^ n)⁻¹
| (n+1:ℕ) := div_inv_monoid.zpow_neg' _ _
| 0       := by { change a ^ (0 : ℤ) = (a ^ (0 : ℤ))⁻¹, simp }
| -[1+ n] := by { rw [zpow_neg_succ_of_nat, inv_inv, ← zpow_coe_nat], refl }

@[to_additive neg_one_zsmul_add]
lemma mul_zpow_neg_one (a b : α) : (a * b) ^ (-1 : ℤ) = b ^ (-1 : ℤ) * a ^ (-1 : ℤ) :=
by simp_rw [zpow_neg_one, mul_inv_rev]

@[to_additive zsmul_neg] lemma inv_zpow (a : α) : ∀ n : ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
| (n : ℕ) := by rw [zpow_coe_nat, zpow_coe_nat, inv_pow]
| -[1+ n] := by rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat, inv_pow]

@[simp, to_additive zsmul_neg']
lemma inv_zpow' (a : α) (n : ℤ) : a⁻¹ ^ n = a ^ (-n) := by rw [inv_zpow, zpow_neg]

@[to_additive nsmul_zero_sub]
lemma one_div_pow (a : α) (n : ℕ) : (1 / a) ^ n = 1 / a ^ n := by simp_rw [one_div, inv_pow]

@[to_additive zsmul_zero_sub]
lemma one_div_zpow (a : α) (n : ℤ) :  (1 / a) ^ n = 1 / a ^ n := by simp_rw [one_div, inv_zpow]

@[to_additive add_commute.zsmul_add]
protected lemma commute.mul_zpow (h : commute a b) : ∀ (i : ℤ), (a * b) ^ i = a ^ i * b ^ i
| (n : ℕ) := by simp [h.mul_pow n]
| -[1+n]  := by simp [h.mul_pow, (h.pow_pow _ _).eq, mul_inv_rev]

end division_monoid

section division_comm_monoid
variables [division_comm_monoid α]

@[to_additive zsmul_add] lemma mul_zpow (a b : α) : ∀ n : ℤ, (a * b) ^ n = a ^ n * b ^ n :=
(commute.all a b).mul_zpow

@[simp, to_additive nsmul_sub] lemma div_pow (a b : α) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n :=
by simp only [div_eq_mul_inv, mul_pow, inv_pow]

@[simp, to_additive zsmul_sub] lemma div_zpow (a b : α) (n : ℤ) : (a / b) ^ n = a ^ n / b ^ n :=
by simp only [div_eq_mul_inv, mul_zpow, inv_zpow]

/-- The `n`-th power map (for an integer `n`) on a commutative group, considered as a group
homomorphism. -/
@[to_additive "Multiplication by an integer `n` on a commutative additive group, considered as an
additive group homomorphism.", simps]
def zpow_group_hom (n : ℤ) : α →* α :=
{ to_fun := (^ n),
  map_one' := one_zpow n,
  map_mul' := λ a b, mul_zpow a b n }

end division_comm_monoid

section group
variables [group G] [group H] [add_group A] [add_group B]

@[to_additive sub_nsmul] lemma pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a^(m - n) = a^m * (a^n)⁻¹ :=
eq_mul_inv_of_mul_eq $ by rw [←pow_add, nat.sub_add_cancel h]

@[to_additive] lemma pow_inv_comm (a : G) (m n : ℕ) : (a⁻¹)^m * a^n = a^n * (a⁻¹)^m :=
(commute.refl a).inv_left.pow_pow _ _

@[to_additive sub_nsmul_neg]
lemma inv_pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a⁻¹^(m - n) = (a^m)⁻¹ * a^n :=
by rw [pow_sub a⁻¹ h, inv_pow, inv_pow, inv_inv]

end group

lemma pow_dvd_pow [monoid R] (a : R) {m n : ℕ} (h : m ≤ n) :
  a ^ m ∣ a ^ n := ⟨a ^ (n - m), by rw [← pow_add, nat.add_comm, nat.sub_add_cancel h]⟩

lemma of_add_nsmul [add_monoid A] (x : A) (n : ℕ) :
  multiplicative.of_add (n • x) = (multiplicative.of_add x)^n := rfl

lemma of_add_zsmul [sub_neg_monoid A] (x : A) (n : ℤ) :
  multiplicative.of_add (n • x) = (multiplicative.of_add x)^n := rfl

lemma of_mul_pow [monoid A] (x : A) (n : ℕ) :
  additive.of_mul (x ^ n) = n • (additive.of_mul x) := rfl

lemma of_mul_zpow [div_inv_monoid G] (x : G) (n : ℤ) :
  additive.of_mul (x ^ n) = n • additive.of_mul x :=
rfl

@[simp, to_additive]
lemma semiconj_by.zpow_right [group G] {a x y : G} (h : semiconj_by a x y) :
  ∀ m : ℤ, semiconj_by a (x^m) (y^m)
| (n : ℕ) := by simp [zpow_coe_nat, h.pow_right n]
| -[1+n] := by simp [(h.pow_right n.succ).inv_right]

namespace commute

variables [group G] {a b : G}

@[simp, to_additive] lemma zpow_right (h : commute a b) (m : ℤ) : commute a (b^m) := h.zpow_right m

@[simp, to_additive] lemma zpow_left (h : commute a b) (m : ℤ) : commute (a^m) b :=
(h.symm.zpow_right m).symm

@[to_additive]
lemma zpow_zpow (h : commute a b) (m n : ℤ) : commute (a^m) (b^n) := (h.zpow_left m).zpow_right n

variables (a) (m n : ℤ)

@[simp, to_additive] lemma self_zpow : commute a (a ^ n) := (commute.refl a).zpow_right n
@[simp, to_additive] lemma zpow_self : commute (a ^ n) a := (commute.refl a).zpow_left n
@[simp, to_additive] lemma zpow_zpow_self : commute (a ^ m) (a ^ n) :=
(commute.refl a).zpow_zpow m n

end commute
