/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import data.nat.basic
import tactic.monotonicity.basic
import group_theory.group_action.defs

/-!
# Power operations on monoids and groups

The power operation on monoids and groups.
We separate this from group, because it depends on `ℕ`,
which in turn depends on other parts of algebra.

This module contains lemmas about `a ^ n` and `n • a`, where `n : ℕ` or `n : ℤ`.
Further lemmas can be found in `algebra.group_power.lemmas`.

The analogous results for groups with zero can be found in `algebra.group_with_zero.power`.

## Notation

- `a ^ n` is used as notation for `has_pow.pow a n`; in this file `n : ℕ` or `n : ℤ`.
- `n • a` is used as notation for `has_scalar.smul n a`; in this file `n : ℕ` or `n : ℤ`.

## Implementation details

We adopt the convention that `0^0 = 1`.
-/

universes u v w x y z u₁ u₂

variables {M : Type u} {N : Type v} {G : Type w} {H : Type x} {A : Type y} {B : Type z}
  {R : Type u₁} {S : Type u₂}

/-!
### Commutativity

First we prove some facts about `semiconj_by` and `commute`. They do not require any theory about
`pow` and/or `nsmul` and will be useful later in this file.
-/

section monoid
variables [monoid M] [monoid N] [add_monoid A] [add_monoid B]

@[simp, to_additive one_nsmul]
theorem pow_one (a : M) : a^1 = a :=
by rw [pow_succ, pow_zero, mul_one]

/-- Note that most of the lemmas about powers of two refer to it as `sq`. -/
@[to_additive two_nsmul]
theorem pow_two (a : M) : a^2 = a * a :=
by rw [pow_succ, pow_one]

alias pow_two ← sq

@[to_additive nsmul_add_comm']
theorem pow_mul_comm' (a : M) (n : ℕ) : a^n * a = a * a^n := commute.pow_self a n

@[to_additive add_nsmul]
theorem pow_add (a : M) (m n : ℕ) : a^(m + n) = a^m * a^n :=
by induction n with n ih; [rw [nat.add_zero, pow_zero, mul_one],
  rw [pow_succ', ← mul_assoc, ← ih, ← pow_succ', nat.add_assoc]]

@[simp] lemma pow_ite (P : Prop) [decidable P] (a : M) (b c : ℕ) :
  a ^ (if P then b else c) = if P then a ^ b else a ^ c :=
by split_ifs; refl

@[simp] lemma ite_pow (P : Prop) [decidable P] (a b : M) (c : ℕ) :
  (if P then a else b) ^ c = if P then a ^ c else b ^ c :=
by split_ifs; refl

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
by rw [←pow_add, nat.add_comm, tsub_add_cancel_of_le h]

@[to_additive sub_nsmul_nsmul_add]
theorem pow_sub_mul_pow (a : M) {m n : ℕ} (h : m ≤ n) : a ^ (n - m) * a ^ m = a ^ n :=
by rw [←pow_add, tsub_add_cancel_of_le h]

@[to_additive bit0_nsmul]
theorem pow_bit0 (a : M) (n : ℕ) : a ^ bit0 n = a^n * a^n := pow_add _ _ _

@[to_additive bit1_nsmul]
theorem pow_bit1 (a : M) (n : ℕ) : a ^ bit1 n = a^n * a^n * a :=
by rw [bit1, pow_succ', pow_bit0]

@[to_additive nsmul_add_comm]
theorem pow_mul_comm (a : M) (m n : ℕ) : a^m * a^n = a^n * a^m :=
commute.pow_pow_self a m n

@[to_additive]
lemma commute.mul_pow {a b : M} (h : commute a b) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n :=
nat.rec_on n (by simp only [pow_zero, one_mul]) $ λ n ihn,
by simp only [pow_succ, ihn, ← mul_assoc, (h.pow_left n).right_comm]

theorem neg_pow [ring R] (a : R) (n : ℕ) : (- a) ^ n = (-1) ^ n * a ^ n :=
(neg_one_mul a) ▸ (commute.neg_one_left a).mul_pow n

@[to_additive bit0_nsmul']
theorem pow_bit0' (a : M) (n : ℕ) : a ^ bit0 n = (a * a) ^ n :=
by rw [pow_bit0, (commute.refl a).mul_pow]

@[to_additive bit1_nsmul']
theorem pow_bit1' (a : M) (n : ℕ) : a ^ bit1 n = (a * a) ^ n * a :=
by rw [bit1, pow_succ', pow_bit0']

@[simp] theorem neg_pow_bit0 [ring R] (a : R) (n : ℕ) : (- a) ^ (bit0 n) = a ^ (bit0 n) :=
by rw [pow_bit0', neg_mul_neg, pow_bit0']

@[simp] theorem neg_pow_bit1 [ring R] (a : R) (n : ℕ) : (- a) ^ (bit1 n) = - a ^ (bit1 n) :=
by simp only [bit1, pow_succ, neg_pow_bit0, neg_mul_eq_neg_mul]

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
@[to_additive nsmul_add_monoid_hom "Multiplication by a natural `n` on a commutative additive
monoid, considered as a morphism of additive monoids.", simps]
def pow_monoid_hom (n : ℕ) : M →* M :=
{ to_fun := (^ n),
  map_one' := one_pow _,
  map_mul' := λ a b, mul_pow a b n }

-- the below line causes the linter to complain :-/
-- attribute [simps] pow_monoid_hom nsmul_add_monoid_hom

lemma dvd_pow {x y : M} (hxy : x ∣ y) :
  ∀ {n : ℕ} (hn : n ≠ 0), x ∣ y^n
| 0       hn := (hn rfl).elim
| (n + 1) hn := by { rw pow_succ, exact hxy.mul_right _ }

alias dvd_pow ← has_dvd.dvd.pow

lemma dvd_pow_self (a : M) {n : ℕ} (hn : n ≠ 0) : a ∣ a^n :=
dvd_rfl.pow hn

end comm_monoid

section div_inv_monoid
variable [div_inv_monoid G]

open int

@[simp, to_additive one_zsmul]
theorem zpow_one (a : G) : a ^ (1:ℤ) = a :=
by { convert pow_one a using 1, exact zpow_coe_nat a 1 }

theorem zpow_two (a : G) : a ^ (2 : ℤ) = a * a :=
by { convert pow_two a using 1, exact zpow_coe_nat a 2 }

@[to_additive neg_one_zsmul]
theorem zpow_neg_one (x : G) : x ^ (-1:ℤ) = x⁻¹ :=
(zpow_neg_succ_of_nat x 0).trans $ congr_arg has_inv.inv (pow_one x)

end div_inv_monoid

section group
variables [group G] [group H] [add_group A] [add_group B]

open int

section nat

@[simp, to_additive neg_nsmul] theorem inv_pow (a : G) (n : ℕ) : (a⁻¹)^n = (a^n)⁻¹ :=
begin
  induction n with n ih,
  { rw [pow_zero, pow_zero, one_inv] },
  { rw [pow_succ', pow_succ, ih, mul_inv_rev] }
end

@[to_additive nsmul_sub] -- rename to sub_nsmul?
theorem pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a^(m - n) = a^m * (a^n)⁻¹ :=
have h1 : m - n + n = m, from tsub_add_cancel_of_le h,
have h2 : a^(m - n) * a^n = a^m, by rw [←pow_add, h1],
eq_mul_inv_of_mul_eq h2

@[to_additive nsmul_neg_comm]
theorem pow_inv_comm (a : G) (m n : ℕ) : (a⁻¹)^m * a^n = a^n * (a⁻¹)^m :=
(commute.refl a).inv_left.pow_pow m n

@[to_additive sub_nsmul_neg]
theorem inv_pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a⁻¹^(m - n) = (a^m)⁻¹ * a^n :=
by rw [pow_sub a⁻¹ h, inv_pow, inv_pow, inv_inv]

end nat

@[simp, to_additive zsmul_zero]
theorem one_zpow : ∀ (n : ℤ), (1 : G) ^ n = 1
| (n : ℕ) := by rw [zpow_coe_nat, one_pow]
| -[1+ n] := by rw [zpow_neg_succ_of_nat, one_pow, one_inv]

@[simp, to_additive neg_zsmul]
theorem zpow_neg (a : G) : ∀ (n : ℤ), a ^ -n = (a ^ n)⁻¹
| (n+1:ℕ) := div_inv_monoid.zpow_neg' _ _
| 0       := by { change a ^ (0 : ℤ) = (a ^ (0 : ℤ))⁻¹, simp }
| -[1+ n] := by { rw [zpow_neg_succ_of_nat, inv_inv, ← zpow_coe_nat], refl }

@[to_additive neg_one_zsmul_add] lemma mul_zpow_neg_one (a b : G) :
  (a*b)^(-(1:ℤ)) = b^(-(1:ℤ))*a^(-(1:ℤ)) :=
by simp only [mul_inv_rev, zpow_one, zpow_neg]

@[to_additive zsmul_neg]
theorem inv_zpow (a : G) : ∀n:ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
| (n : ℕ) := by rw [zpow_coe_nat, zpow_coe_nat, inv_pow]
| -[1+ n] := by rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat, inv_pow]

@[to_additive add_commute.zsmul_add]
theorem commute.mul_zpow {a b : G} (h : commute a b) : ∀ n : ℤ, (a * b) ^ n = a ^ n * b ^ n
| (n : ℕ) := by simp [zpow_coe_nat, h.mul_pow n]
| -[1+n]  := by simp [h.mul_pow, (h.pow_pow n.succ n.succ).inv_inv.symm.eq]

end group

section comm_group
variables [comm_group G] [add_comm_group A]

@[to_additive zsmul_add]
theorem mul_zpow (a b : G) (n : ℤ) : (a * b)^n = a^n * b^n := (commute.all a b).mul_zpow n

@[to_additive zsmul_sub]
theorem div_zpow (a b : G) (n : ℤ) : (a / b) ^ n = a ^ n / b ^ n :=
by rw [div_eq_mul_inv, div_eq_mul_inv, mul_zpow, inv_zpow]

/-- The `n`th power map (`n` an integer) on a commutative group, considered as a group
homomorphism. -/
@[to_additive "Multiplication by an integer `n` on a commutative additive group, considered as an
additive group homomorphism.", simps]
def zpow_group_hom (n : ℤ) : G →* G :=
{ to_fun := (^ n),
  map_one' := one_zpow n,
  map_mul' := λ a b, mul_zpow a b n }

end comm_group

lemma zero_pow [monoid_with_zero R] : ∀ {n : ℕ}, 0 < n → (0 : R) ^ n = 0
| (n+1) _ := by rw [pow_succ, zero_mul]

lemma zero_pow_eq [monoid_with_zero R] (n : ℕ) : (0 : R)^n = if n = 0 then 1 else 0 :=
begin
  split_ifs with h,
  { rw [h, pow_zero], },
  { rw [zero_pow (nat.pos_of_ne_zero h)] },
end

lemma pow_eq_zero_of_le [monoid_with_zero M] {x : M} {n m : ℕ}
  (hn : n ≤ m) (hx : x^n = 0) : x^m = 0 :=
by rw [← tsub_add_cancel_of_le hn, pow_add, hx, mul_zero]

namespace ring_hom

variables [semiring R] [semiring S]

protected lemma map_pow (f : R →+* S) (a) :
  ∀ n : ℕ, f (a ^ n) = (f a) ^ n :=
map_pow f a

end ring_hom

section
variables (R)

theorem neg_one_pow_eq_or [ring R] : ∀ n : ℕ, (-1 : R)^n = 1 ∨ (-1 : R)^n = -1
| 0     := or.inl (pow_zero _)
| (n+1) := (neg_one_pow_eq_or n).swap.imp
  (λ h, by rw [pow_succ, h, neg_one_mul, neg_neg])
  (λ h, by rw [pow_succ, h, mul_one])

end

@[simp]
lemma neg_one_pow_mul_eq_zero_iff [ring R] {n : ℕ} {r : R} : (-1)^n * r = 0 ↔ r = 0 :=
by rcases neg_one_pow_eq_or R n; simp [h]

@[simp]
lemma mul_neg_one_pow_eq_zero_iff [ring R] {n : ℕ} {r : R} : r * (-1)^n = 0 ↔ r = 0 :=
by rcases neg_one_pow_eq_or R n; simp [h]

lemma pow_dvd_pow [monoid R] (a : R) {m n : ℕ} (h : m ≤ n) :
  a ^ m ∣ a ^ n := ⟨a ^ (n - m), by rw [← pow_add, nat.add_comm, tsub_add_cancel_of_le h]⟩

theorem pow_dvd_pow_of_dvd [comm_monoid R] {a b : R} (h : a ∣ b) : ∀ n : ℕ, a ^ n ∣ b ^ n
| 0     := by rw [pow_zero, pow_zero]
| (n+1) := by { rw [pow_succ, pow_succ], exact mul_dvd_mul h (pow_dvd_pow_of_dvd n) }

lemma sq_sub_sq {R : Type*} [comm_ring R] (a b : R) :
  a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
by rw [sq, sq, mul_self_sub_mul_self]

alias sq_sub_sq ← pow_two_sub_pow_two

lemma eq_or_eq_neg_of_sq_eq_sq [comm_ring R] [is_domain R] (a b : R) (h : a ^ 2 = b ^ 2) :
  a = b ∨ a = -b :=
by rwa [← add_eq_zero_iff_eq_neg, ← sub_eq_zero, or_comm, ← mul_eq_zero,
        ← sq_sub_sq a b, sub_eq_zero]

theorem pow_eq_zero [monoid_with_zero R] [no_zero_divisors R] {x : R} {n : ℕ} (H : x^n = 0) :
  x = 0 :=
begin
  induction n with n ih,
  { rw pow_zero at H,
    rw [← mul_one x, H, mul_zero] },
  { rw pow_succ at H,
    exact or.cases_on (mul_eq_zero.1 H) id ih }
end

@[simp] lemma pow_eq_zero_iff [monoid_with_zero R] [no_zero_divisors R]
  {a : R} {n : ℕ} (hn : 0 < n) :
  a ^ n = 0 ↔ a = 0 :=
begin
  refine ⟨pow_eq_zero, _⟩,
  rintros rfl,
  exact zero_pow hn,
end

lemma pow_ne_zero_iff [monoid_with_zero R] [no_zero_divisors R] {a : R} {n : ℕ} (hn : 0 < n) :
  a ^ n ≠ 0 ↔ a ≠ 0 :=
by rwa [not_iff_not, pow_eq_zero_iff]

@[field_simps] theorem pow_ne_zero [monoid_with_zero R] [no_zero_divisors R]
  {a : R} (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 :=
mt pow_eq_zero h

section semiring

variables [semiring R]

lemma min_pow_dvd_add {n m : ℕ} {a b c : R} (ha : c ^ n ∣ a) (hb : c ^ m ∣ b) :
  c ^ (min n m) ∣ a + b :=
begin
  replace ha := (pow_dvd_pow c (min_le_left n m)).trans ha,
  replace hb := (pow_dvd_pow c (min_le_right n m)).trans hb,
  exact dvd_add ha hb
end

end semiring

section comm_semiring

variables [comm_semiring R]

lemma add_sq (a b : R) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
by simp only [sq, add_mul_self_eq]

alias add_sq ← add_pow_two

end comm_semiring

@[simp] lemma neg_sq {α} [ring α] (z : α) : (-z)^2 = z^2 :=
by simp [sq]

alias neg_sq ← neg_pow_two

lemma sub_sq {R} [comm_ring R] (a b : R) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 :=
by rw [sub_eq_add_neg, add_sq, neg_sq, mul_neg_eq_neg_mul_symm, ← sub_eq_add_neg]

alias sub_sq ← sub_pow_two

lemma of_add_nsmul [add_monoid A] (x : A) (n : ℕ) :
  multiplicative.of_add (n • x) = (multiplicative.of_add x)^n := rfl

lemma of_add_zsmul [add_group A] (x : A) (n : ℤ) :
  multiplicative.of_add (n • x) = (multiplicative.of_add x)^n := rfl

lemma of_mul_pow {A : Type*} [monoid A] (x : A) (n : ℕ) :
  additive.of_mul (x ^ n) = n • (additive.of_mul x) := rfl

lemma of_mul_zpow [group G] (x : G) (n : ℤ) : additive.of_mul (x ^ n) = n • additive.of_mul x :=
rfl

@[simp] lemma semiconj_by.zpow_right [group G] {a x y : G} (h : semiconj_by a x y) :
  ∀ m : ℤ, semiconj_by a (x^m) (y^m)
| (n : ℕ) := by simp [zpow_coe_nat, h.pow_right n]
| -[1+n] := by simp [(h.pow_right n.succ).inv_right]

namespace commute

variables [group G] {a b : G}

@[simp] lemma zpow_right (h : commute a b) (m : ℤ) : commute a (b^m) :=
h.zpow_right m

@[simp] lemma zpow_left (h : commute a b) (m : ℤ) : commute (a^m) b :=
(h.symm.zpow_right m).symm

lemma zpow_zpow (h : commute a b) (m n : ℤ) : commute (a^m) (b^n) := (h.zpow_left m).zpow_right n

variables (a) (m n : ℤ)

@[simp] theorem self_zpow : commute a (a ^ n) := (commute.refl a).zpow_right n
@[simp] theorem zpow_self : commute (a ^ n) a := (commute.refl a).zpow_left n
@[simp] theorem zpow_zpow_self : commute (a ^ m) (a ^ n) := (commute.refl a).zpow_zpow m n

end commute
