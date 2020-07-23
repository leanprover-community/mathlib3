/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import algebra.opposites
import data.list.basic
import data.int.cast
import data.equiv.basic
import deprecated.ring

/-!
# Power operations on monoids and groups

The power operation on monoids and groups.
We separate this from group, because it depends on `ℕ`,
which in turn depends on other parts of algebra.

## Notation

The class `has_pow α β` provides the notation `a^b` for powers.
We define instances of `has_pow M ℕ`, for monoids `M`, and `has_pow G ℤ` for groups `G`.

We also define infix operators `•ℕ` and `•ℤ` for scalar multiplication by a natural and an integer
numbers, respectively.

## Implementation details

We adopt the convention that `0^0 = 1`.
-/

universes u v w x y z u₁ u₂

variables {M : Type u} {N : Type v} {G : Type w} {H : Type x} {A : Type y} {B : Type z}
  {R : Type u₁} {S : Type u₂}

/-- The power operation in a monoid. `a^n = a*a*...*a` n times. -/
def monoid.pow [has_mul M] [has_one M] (a : M) : ℕ → M
| 0     := 1
| (n+1) := a * monoid.pow n

/-- The scalar multiplication in an additive monoid.
`n •ℕ a = a+a+...+a` n times. -/
def nsmul [has_add A] [has_zero A] (n : ℕ) (a : A) : A :=
@monoid.pow (multiplicative A) _ { one := (0 : A) } a n

infix ` •ℕ `:70 := nsmul

@[priority 5] instance monoid.has_pow [monoid M] : has_pow M ℕ := ⟨monoid.pow⟩

/-!
### Commutativity

First we prove some facts about `semiconj_by` and `commute`. They do not require any theory about
`pow` and/or `nsmul` and will be useful later in this file.
-/

namespace semiconj_by

variables [monoid M]

@[simp] lemma pow_right {a x y : M} (h : semiconj_by a x y) (n : ℕ) : semiconj_by a (x^n) (y^n) :=
nat.rec_on n (one_right a) $ λ n ihn, h.mul_right ihn

end semiconj_by

namespace commute

variables [monoid M] {a b : M}

@[simp] theorem pow_right (h : commute a b) (n : ℕ) : commute a (b ^ n) := h.pow_right n
@[simp] theorem pow_left (h : commute a b) (n : ℕ) : commute (a ^ n) b := (h.symm.pow_right n).symm
@[simp] theorem pow_pow (h : commute a b) (m n : ℕ) : commute (a ^ m) (b ^ n) :=
(h.pow_left m).pow_right n

@[simp] theorem self_pow (a : M) (n : ℕ) : commute a (a ^ n) := (commute.refl a).pow_right n
@[simp] theorem pow_self (a : M) (n : ℕ) : commute (a ^ n) a := (commute.refl a).pow_left n
@[simp] theorem pow_pow_self (a : M) (m n : ℕ) : commute (a ^ m) (a ^ n) :=
(commute.refl a).pow_pow m n

end commute

/-!
### (Additive) monoid
-/
section monoid
variables [monoid M] [monoid N] [add_monoid A] [add_monoid B]

@[simp] theorem pow_zero (a : M) : a^0 = 1 := rfl
@[simp] theorem zero_nsmul (a : A) : 0 •ℕ a = 0 := rfl

theorem pow_succ (a : M) (n : ℕ) : a^(n+1) = a * a^n := rfl
theorem succ_nsmul (a : A) (n : ℕ) : (n+1) •ℕ a = a + n •ℕ a := rfl

@[simp] theorem pow_one (a : M) : a^1 = a := mul_one _
@[simp] theorem one_nsmul (a : A) : 1 •ℕ a = a := add_zero _

@[simp] lemma pow_ite (P : Prop) [decidable P] (a : M) (b c : ℕ) :
  a ^ (if P then b else c) = if P then a ^ b else a ^ c :=
by split_ifs; refl

@[simp] lemma ite_pow (P : Prop) [decidable P] (a b : M) (c : ℕ) :
  (if P then a else b) ^ c = if P then a ^ c else b ^ c :=
by split_ifs; refl

@[simp] lemma pow_boole (P : Prop) [decidable P] (a : M) :
  a ^ (if P then 1 else 0) = if P then a else 1 :=
by simp

theorem pow_mul_comm' (a : M) (n : ℕ) : a^n * a = a * a^n := commute.pow_self a n
theorem nsmul_add_comm' : ∀ (a : A) (n : ℕ), n •ℕ a + a = a + n •ℕ a :=
@pow_mul_comm' (multiplicative A) _

theorem pow_succ' (a : M) (n : ℕ) : a^(n+1) = a^n * a :=
by rw [pow_succ, pow_mul_comm']
theorem succ_nsmul' (a : A) (n : ℕ) : (n+1) •ℕ a = n •ℕ a + a :=
@pow_succ' (multiplicative A) _ _ _

theorem pow_two (a : M) : a^2 = a * a :=
show a*(a*1)=a*a, by rw mul_one
theorem two_nsmul (a : A) : 2 •ℕ a = a + a :=
@pow_two (multiplicative A) _ a

theorem pow_add (a : M) (m n : ℕ) : a^(m + n) = a^m * a^n :=
by induction n with n ih; [rw [add_zero, pow_zero, mul_one],
  rw [pow_succ', ← mul_assoc, ← ih, ← pow_succ', add_assoc]]
theorem add_nsmul : ∀ (a : A) (m n : ℕ), (m + n) •ℕ a = m •ℕ a + n •ℕ a :=
@pow_add (multiplicative A) _

@[simp] theorem one_pow (n : ℕ) : (1 : M)^n = 1 :=
by induction n with n ih; [refl, rw [pow_succ, ih, one_mul]]
@[simp] theorem nsmul_zero (n : ℕ) : n •ℕ (0 : A) = 0 :=
by induction n with n ih; [refl, rw [succ_nsmul, ih, zero_add]]

theorem pow_mul (a : M) (m n : ℕ) : a^(m * n) = (a^m)^n :=
by induction n with n ih; [rw mul_zero, rw [nat.mul_succ, pow_add, pow_succ', ih]]; refl
theorem mul_nsmul' : ∀ (a : A) (m n : ℕ), m * n •ℕ a = n •ℕ (m •ℕ a) :=
@pow_mul (multiplicative A) _

theorem pow_mul' (a : M) (m n : ℕ) : a^(m * n) = (a^n)^m :=
by rw [mul_comm, pow_mul]
theorem mul_nsmul (a : A) (m n : ℕ) : m * n •ℕ a = m •ℕ (n •ℕ a) :=
@pow_mul' (multiplicative A) _ a m n

@[simp] theorem nsmul_one [has_one A] : ∀ n : ℕ, n •ℕ (1 : A) = n :=
add_monoid_hom.eq_nat_cast
  ⟨λ n, n •ℕ (1 : A), zero_nsmul _, λ _ _, add_nsmul _ _ _⟩
  (one_nsmul _)

theorem pow_bit0 (a : M) (n : ℕ) : a ^ bit0 n = a^n * a^n := pow_add _ _ _
theorem bit0_nsmul (a : A) (n : ℕ) : bit0 n •ℕ a = n •ℕ a + n •ℕ a := add_nsmul _ _ _

theorem pow_bit1 (a : M) (n : ℕ) : a ^ bit1 n = a^n * a^n * a :=
by rw [bit1, pow_succ', pow_bit0]
theorem bit1_nsmul : ∀ (a : A) (n : ℕ), bit1 n •ℕ a = n •ℕ a + n •ℕ a + a :=
@pow_bit1 (multiplicative A) _

theorem pow_mul_comm (a : M) (m n : ℕ) : a^m * a^n = a^n * a^m :=
commute.pow_pow_self a m n
theorem nsmul_add_comm : ∀ (a : A) (m n : ℕ), m •ℕ a + n •ℕ a = n •ℕ a + m •ℕ a :=
@pow_mul_comm (multiplicative A) _

@[simp, priority 500]
theorem list.prod_repeat (a : M) (n : ℕ) : (list.repeat a n).prod = a ^ n :=
begin
  induction n with n ih,
  { refl },
  { rw [list.repeat_succ, list.prod_cons, ih], refl, }
end
@[simp, priority 500]
theorem list.sum_repeat : ∀ (a : A) (n : ℕ), (list.repeat a n).sum = n •ℕ a :=
@list.prod_repeat (multiplicative A) _

theorem monoid_hom.map_pow (f : M →* N) (a : M) : ∀(n : ℕ), f (a ^ n) = (f a) ^ n
| 0     := f.map_one
| (n+1) := by rw [pow_succ, pow_succ, f.map_mul, monoid_hom.map_pow]

theorem add_monoid_hom.map_nsmul (f : A →+ B) (a : A) (n : ℕ) : f (n •ℕ a) = n •ℕ f a :=
f.to_multiplicative.map_pow a n

theorem is_monoid_hom.map_pow (f : M → N) [is_monoid_hom f] (a : M) :
  ∀(n : ℕ), f (a ^ n) = (f a) ^ n :=
(monoid_hom.of f).map_pow a

theorem is_add_monoid_hom.map_nsmul (f : A → B) [is_add_monoid_hom f] (a : A) (n : ℕ) :
  f (n •ℕ a) = n •ℕ f a :=
(add_monoid_hom.of f).map_nsmul a n

@[simp, norm_cast] lemma units.coe_pow (u : units M) (n : ℕ) : ((u ^ n : units M) : M) = u ^ n :=
(units.coe_hom M).map_pow u n

lemma commute.mul_pow {a b : M} (h : commute a b) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n :=
nat.rec_on n (by simp) $ λ n ihn,
by simp only [pow_succ, ihn, ← mul_assoc, (h.pow_left n).right_comm]

theorem neg_pow [ring R] (a : R) (n : ℕ) : (- a) ^ n = (-1) ^ n * a ^ n :=
(neg_one_mul a) ▸ (commute.neg_one_left a).mul_pow n

end monoid

@[simp] theorem nat.pow_eq_pow (p q : ℕ) :
  @has_pow.pow _ _ monoid.has_pow p q = p ^ q :=
by induction q with q ih; [refl, rw [nat.pow_succ, pow_succ', ih]]

theorem nat.nsmul_eq_mul (m n : ℕ) : m •ℕ n = m * n :=
by induction m with m ih; [rw [zero_nsmul, zero_mul],
  rw [succ_nsmul', ih, nat.succ_mul]]

/-!
### Commutative (additive) monoid
-/

section comm_monoid
variables [comm_monoid M] [add_comm_monoid A]

theorem mul_pow (a b : M) (n : ℕ) : (a * b)^n = a^n * b^n :=
(commute.all a b).mul_pow n
theorem nsmul_add : ∀ (a b : A) (n : ℕ), n •ℕ (a + b) = n •ℕ a + n •ℕ b :=
@mul_pow (multiplicative A) _

instance pow.is_monoid_hom (n : ℕ) : is_monoid_hom ((^ n) : M → M) :=
{ map_mul := λ _ _, mul_pow _ _ _, map_one := one_pow _ }

instance nsmul.is_add_monoid_hom (n : ℕ) : is_add_monoid_hom (nsmul n : A → A) :=
{ map_add := λ _ _, nsmul_add _ _ _, map_zero := nsmul_zero _ }

end comm_monoid

section group
variables [group G] [group H] [add_group A] [add_group B]

section nat

@[simp] theorem inv_pow (a : G) (n : ℕ) : (a⁻¹)^n = (a^n)⁻¹ :=
by induction n with n ih; [exact one_inv.symm,
  rw [pow_succ', pow_succ, ih, mul_inv_rev]]
@[simp] theorem neg_nsmul : ∀ (a : A) (n : ℕ), n •ℕ (-a) = -(n •ℕ a) :=
@inv_pow (multiplicative A) _

theorem pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a^(m - n) = a^m * (a^n)⁻¹ :=
have h1 : m - n + n = m, from nat.sub_add_cancel h,
have h2 : a^(m - n) * a^n = a^m, by rw [←pow_add, h1],
eq_mul_inv_of_mul_eq h2
theorem nsmul_sub : ∀ (a : A) {m n : ℕ}, n ≤ m → (m - n) •ℕ a = m •ℕ a - n •ℕ a :=
@pow_sub (multiplicative A) _

theorem pow_inv_comm (a : G) (m n : ℕ) : (a⁻¹)^m * a^n = a^n * (a⁻¹)^m :=
(commute.refl a).inv_left.pow_pow m n
theorem nsmul_neg_comm : ∀ (a : A) (m n : ℕ), m •ℕ (-a) + n •ℕ a = n •ℕ a + m •ℕ (-a) :=
@pow_inv_comm (multiplicative A) _
end nat

open int

/--
The power operation in a group. This extends `monoid.pow` to negative integers
with the definition `a^(-n) = (a^n)⁻¹`.
-/
def gpow (a : G) : ℤ → G
| (of_nat n) := a^n
| -[1+n]     := (a^(nat.succ n))⁻¹

/--
The scalar multiplication by integers on an additive group.
This extends `nsmul` to negative integers
with the definition `(-n) •ℤ a = -(n •ℕ a)`.
-/
def gsmul (n : ℤ) (a : A) : A :=
@gpow (multiplicative A) _ a n

@[priority 10] instance group.has_pow : has_pow G ℤ := ⟨gpow⟩

infix ` •ℤ `:70 := gsmul

@[simp] theorem gpow_coe_nat (a : G) (n : ℕ) : a ^ (n:ℤ) = a ^ n := rfl
@[simp] theorem gsmul_coe_nat (a : A) (n : ℕ) : n •ℤ a = n •ℕ a := rfl

theorem gpow_of_nat (a : G) (n : ℕ) : a ^ of_nat n = a ^ n := rfl
theorem gsmul_of_nat (a : A) (n : ℕ) : of_nat n •ℤ a = n •ℕ a := rfl

@[simp] theorem gpow_neg_succ_of_nat (a : G) (n : ℕ) : a ^ -[1+n] = (a ^ n.succ)⁻¹ := rfl
@[simp] theorem gsmul_neg_succ_of_nat (a : A) (n : ℕ) : -[1+n] •ℤ a = - (n.succ •ℕ a) := rfl

local attribute [ematch] le_of_lt
open nat

@[simp] theorem gpow_zero (a : G) : a ^ (0:ℤ) = 1 := rfl
@[simp] theorem zero_gsmul (a : A) : (0:ℤ) •ℤ a = 0 := rfl

@[simp] theorem gpow_one (a : G) : a ^ (1:ℤ) = a := pow_one a
@[simp] theorem one_gsmul (a : A) : (1:ℤ) •ℤ a = a := add_zero _

@[simp] theorem one_gpow : ∀ (n : ℤ), (1 : G) ^ n = 1
| (n : ℕ) := one_pow _
| -[1+ n] := show _⁻¹=(1:G), by rw [_root_.one_pow, one_inv]
@[simp] theorem gsmul_zero : ∀ (n : ℤ), n •ℤ (0 : A) = 0 :=
@one_gpow (multiplicative A) _

@[simp] theorem gpow_neg (a : G) : ∀ (n : ℤ), a ^ -n = (a ^ n)⁻¹
| (n+1:ℕ) := rfl
| 0       := one_inv.symm
| -[1+ n] := (inv_inv _).symm

lemma mul_gpow_neg_one (a b : G) : (a*b)^(-(1:ℤ)) = b^(-(1:ℤ))*a^(-(1:ℤ)) :=
by simp only [mul_inv_rev, gpow_one, gpow_neg]

@[simp] theorem neg_gsmul : ∀ (a : A) (n : ℤ), -n •ℤ a = -(n •ℤ a) :=
@gpow_neg (multiplicative A) _

theorem gpow_neg_one (x : G) : x ^ (-1:ℤ) = x⁻¹ := congr_arg has_inv.inv $ pow_one x
theorem neg_one_gsmul (x : A) : (-1:ℤ) •ℤ x = -x := congr_arg has_neg.neg $ one_nsmul x

theorem gsmul_one [has_one A] (n : ℤ) : n •ℤ (1 : A) = n :=
by cases n; simp

theorem inv_gpow (a : G) : ∀n:ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
| (n : ℕ) := inv_pow a n
| -[1+ n] := congr_arg has_inv.inv $ inv_pow a (n+1)
theorem gsmul_neg (a : A) (n : ℤ) : gsmul n (- a) = - gsmul n a :=
@inv_gpow (multiplicative A) _ a n

lemma gpow_add_one (a : G) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
| (of_nat n) := by simp [← int.coe_nat_succ, pow_succ']
| -[1+0]     := by simp [int.neg_succ_of_nat_eq]
| -[1+(n+1)] := by rw [int.neg_succ_of_nat_eq, gpow_neg, neg_add, neg_add_cancel_right, gpow_neg,
  ← int.coe_nat_succ, gpow_coe_nat, gpow_coe_nat, _root_.pow_succ _ (n + 1), mul_inv_rev,
  inv_mul_cancel_right]

theorem add_one_gsmul : ∀ (a : A) (i : ℤ), (i + 1) •ℤ a = i •ℤ a + a :=
@gpow_add_one (multiplicative A) _

lemma gpow_sub_one (a : G) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
calc a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ : (mul_inv_cancel_right _ _).symm
             ... = a^n * a⁻¹             : by rw [← gpow_add_one, sub_add_cancel]

lemma gpow_add (a : G) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n :=
begin
  induction n using int.induction_on with n ihn n ihn,
  case hz : { simp },
  { simp only [← add_assoc, gpow_add_one, ihn, mul_assoc] },
  { rw [gpow_sub_one, ← mul_assoc, ← ihn, ← gpow_sub_one, add_sub_assoc] }
end

lemma mul_self_gpow (b : G) (m : ℤ) : b*b^m = b^(m+1) :=
by { conv_lhs {congr, rw ← gpow_one b }, rw [← gpow_add, add_comm] }

lemma mul_gpow_self (b : G) (m : ℤ) : b^m*b = b^(m+1) :=
by { conv_lhs {congr, skip, rw ← gpow_one b }, rw [← gpow_add, add_comm] }

theorem add_gsmul : ∀ (a : A) (i j : ℤ), (i + j) •ℤ a = i •ℤ a + j •ℤ a :=
@gpow_add (multiplicative A) _

lemma gpow_sub (a : G) (m n : ℤ) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ :=
by rw [sub_eq_add_neg, gpow_add, gpow_neg]

lemma sub_gsmul (m n : ℤ) (a : A) : (m - n) •ℤ a = m •ℤ a - n •ℤ a :=
@gpow_sub (multiplicative A) _ _ _ _

theorem gpow_one_add (a : G) (i : ℤ) : a ^ (1 + i) = a * a ^ i :=
by rw [gpow_add, gpow_one]
theorem one_add_gsmul : ∀ (a : A) (i : ℤ), (1 + i) •ℤ a = a + i •ℤ a :=
@gpow_one_add (multiplicative A) _

theorem gpow_mul_comm (a : G) (i j : ℤ) : a ^ i * a ^ j = a ^ j * a ^ i :=
by rw [← gpow_add, ← gpow_add, add_comm]
theorem gsmul_add_comm : ∀ (a : A) (i j), i •ℤ a + j •ℤ a = j •ℤ a + i •ℤ a :=
@gpow_mul_comm (multiplicative A) _

theorem gpow_mul (a : G) (m n : ℤ) : a ^ (m * n) = (a ^ m) ^ n :=
int.induction_on n (by simp) (λ n ihn, by simp [mul_add, gpow_add, ihn])
  (λ n ihn, by simp only [mul_sub, gpow_sub, ihn, mul_one, gpow_one])

theorem gsmul_mul' : ∀ (a : A) (m n : ℤ), m * n •ℤ a = n •ℤ (m •ℤ a) :=
@gpow_mul (multiplicative A) _

theorem gpow_mul' (a : G) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m :=
by rw [mul_comm, gpow_mul]
theorem gsmul_mul (a : A) (m n : ℤ) : m * n •ℤ a = m •ℤ (n •ℤ a) :=
by rw [mul_comm, gsmul_mul']

theorem gpow_bit0 (a : G) (n : ℤ) : a ^ bit0 n = a ^ n * a ^ n := gpow_add _ _ _
theorem bit0_gsmul (a : A) (n : ℤ) : bit0 n •ℤ a = n •ℤ a + n •ℤ a := gpow_add _ _ _

theorem gpow_bit1 (a : G) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a :=
by rw [bit1, gpow_add]; simp [gpow_bit0]
theorem bit1_gsmul : ∀ (a : A) (n : ℤ), bit1 n •ℤ a = n •ℤ a + n •ℤ a + a :=
@gpow_bit1 (multiplicative A) _

theorem monoid_hom.map_gpow (f : G →* H) (a : G) (n : ℤ) : f (a ^ n) = f a ^ n :=
by cases n; [exact f.map_pow _ _, exact (f.map_inv _).trans (congr_arg _ $ f.map_pow _ _)]

theorem add_monoid_hom.map_gsmul (f : A →+ B) (a : A) (n : ℤ) : f (n •ℤ a) = n •ℤ f a :=
f.to_multiplicative.map_gpow a n

@[simp, norm_cast] lemma units.coe_gpow (u : units G) (n : ℤ) : ((u ^ n : units G) : G) = u ^ n :=
(units.coe_hom G).map_gpow u n

theorem commute.mul_gpow {a b : G} (h : commute a b) : ∀ n : ℤ, (a * b) ^ n = a ^ n * b ^ n
| (n : ℕ) := h.mul_pow n
| -[1+n] := by simp [h.mul_pow, (h.pow_pow n.succ n.succ).inv_inv.symm.eq]

end group

section comm_group
variables [comm_group G] [add_comm_group A]

theorem mul_gpow (a b : G) (n : ℤ) : (a * b)^n = a^n * b^n := (commute.all a b).mul_gpow n

theorem gsmul_add : ∀ (a b : A) (n : ℤ), n •ℤ (a + b) = n •ℤ a + n •ℤ b :=
@mul_gpow (multiplicative A) _

theorem gsmul_sub (a b : A) (n : ℤ) : gsmul n (a - b) = gsmul n a - gsmul n b :=
by simp only [gsmul_add, gsmul_neg, sub_eq_add_neg]

instance gpow.is_group_hom (n : ℤ) : is_group_hom ((^ n) : G → G) :=
{ map_mul := λ _ _, mul_gpow _ _ n }

instance gsmul.is_add_group_hom (n : ℤ) : is_add_group_hom (gsmul n : A → A) :=
{ map_add := λ _ _, gsmul_add _ _ n }

end comm_group

@[simp] lemma with_bot.coe_nsmul [add_monoid A] (a : A) (n : ℕ) :
  ((nsmul n a : A) : with_bot A) = nsmul n a :=
add_monoid_hom.map_nsmul ⟨(coe : A → with_bot A), with_bot.coe_zero, with_bot.coe_add⟩ a n

theorem nsmul_eq_mul' [semiring R] (a : R) (n : ℕ) : n •ℕ a = a * n :=
by induction n with n ih; [rw [zero_nsmul, nat.cast_zero, mul_zero],
  rw [succ_nsmul', ih, nat.cast_succ, mul_add, mul_one]]

@[simp] theorem nsmul_eq_mul [semiring R] (n : ℕ) (a : R) : n •ℕ a = n * a :=
by rw [nsmul_eq_mul', (n.cast_commute a).eq]

theorem mul_nsmul_left [semiring R] (a b : R) (n : ℕ) : n •ℕ (a * b) = a * (n •ℕ b) :=
by rw [nsmul_eq_mul', nsmul_eq_mul', mul_assoc]

theorem mul_nsmul_assoc [semiring R] (a b : R) (n : ℕ) : n •ℕ (a * b) = n •ℕ a * b :=
by rw [nsmul_eq_mul, nsmul_eq_mul, mul_assoc]

lemma zero_pow [semiring R] : ∀ {n : ℕ}, 0 < n → (0 : R) ^ n = 0
| (n+1) _ := zero_mul _

@[simp, norm_cast] theorem nat.cast_pow [semiring R] (n m : ℕ) : (↑(n ^ m) : R) = ↑n ^ m :=
by induction m with m ih; [exact nat.cast_one, rw [nat.pow_succ, pow_succ', nat.cast_mul, ih]]

@[simp, norm_cast] theorem int.coe_nat_pow (n m : ℕ) : ((n ^ m : ℕ) : ℤ) = n ^ m :=
by induction m with m ih; [exact int.coe_nat_one, rw [nat.pow_succ, pow_succ', int.coe_nat_mul, ih]]

theorem int.nat_abs_pow (n : ℤ) (k : ℕ) : int.nat_abs (n ^ k) = (int.nat_abs n) ^ k :=
by induction k with k ih; [refl, rw [pow_succ', int.nat_abs_mul, nat.pow_succ, ih]]

namespace ring_hom

variables [semiring R] [semiring S]

@[simp] lemma map_pow (f : R →+* S) (a) :
  ∀ n : ℕ, f (a ^ n) = (f a) ^ n :=
f.to_monoid_hom.map_pow a

end ring_hom

lemma is_semiring_hom.map_pow [semiring R] [semiring S] (f : R → S) [is_semiring_hom f] (a) :
  ∀ n : ℕ, f (a ^ n) = (f a) ^ n :=
is_monoid_hom.map_pow f a

theorem neg_one_pow_eq_or [ring R] : ∀ n : ℕ, (-1 : R)^n = 1 ∨ (-1 : R)^n = -1
| 0     := or.inl rfl
| (n+1) := (neg_one_pow_eq_or n).swap.imp
  (λ h, by rw [pow_succ, h, neg_one_mul, neg_neg])
  (λ h, by rw [pow_succ, h, mul_one])

lemma pow_dvd_pow [comm_semiring R] (a : R) {m n : ℕ} (h : m ≤ n) :
  a ^ m ∣ a ^ n := ⟨a ^ (n - m), by rw [← pow_add, nat.add_sub_cancel' h]⟩

theorem pow_dvd_pow_of_dvd [comm_semiring R] {a b : R} (h : a ∣ b) : ∀ n : ℕ, a ^ n ∣ b ^ n
| 0     := dvd_refl _
| (n+1) := mul_dvd_mul h (pow_dvd_pow_of_dvd n)

lemma pow_two_sub_pow_two {R : Type*} [comm_ring R] (a b : R) :
  a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
by simp only [pow_two, mul_sub, add_mul, sub_sub, add_sub, mul_comm, sub_add_cancel]

lemma eq_or_eq_neg_of_pow_two_eq_pow_two [integral_domain R] (a b : R) (h : a ^ 2 = b ^ 2) :
  a = b ∨ a = -b :=
by rwa [← add_eq_zero_iff_eq_neg, ← sub_eq_zero, or_comm, ← mul_eq_zero,
        ← pow_two_sub_pow_two a b, sub_eq_zero]

-- The next four lemmas allow us to replace multiplication by a numeral with a `gsmul` expression.
-- They are used by the `noncomm_ring` tactic, to normalise expressions before passing to `abel`.

lemma bit0_mul [ring R] {n r : R} : bit0 n * r = gsmul 2 (n * r) :=
by { dsimp [bit0], rw [add_mul, add_gsmul, one_gsmul], }

lemma mul_bit0 [ring R] {n r : R} : r * bit0 n = gsmul 2 (r * n) :=
by { dsimp [bit0], rw [mul_add, add_gsmul, one_gsmul], }

lemma bit1_mul [ring R] {n r : R} : bit1 n * r = gsmul 2 (n * r) + r :=
by { dsimp [bit1], rw [add_mul, bit0_mul, one_mul], }

lemma mul_bit1 [ring R] {n r : R} : r * bit1 n = gsmul 2 (r * n) + r :=
by { dsimp [bit1], rw [mul_add, mul_bit0, mul_one], }

@[simp] theorem gsmul_eq_mul [ring R] (a : R) : ∀ n, n •ℤ a = n * a
| (n : ℕ) := nsmul_eq_mul _ _
| -[1+ n] := show -(_ •ℕ _)=-_*_, by rw [neg_mul_eq_neg_mul_symm, nsmul_eq_mul, nat.cast_succ]

theorem gsmul_eq_mul' [ring R] (a : R) (n : ℤ) : n •ℤ a = a * n :=
by rw [gsmul_eq_mul, (n.cast_commute a).eq]

theorem mul_gsmul_left [ring R] (a b : R) (n : ℤ) : n •ℤ (a * b) = a * (n •ℤ b) :=
by rw [gsmul_eq_mul', gsmul_eq_mul', mul_assoc]

theorem mul_gsmul_assoc [ring R] (a b : R) (n : ℤ) : n •ℤ (a * b) = n •ℤ a * b :=
by rw [gsmul_eq_mul, gsmul_eq_mul, mul_assoc]

@[simp]
lemma gsmul_int_int (a b : ℤ) : a •ℤ b = a * b := by simp [gsmul_eq_mul]

lemma gsmul_int_one (n : ℤ) : n •ℤ 1 = n := by simp

@[simp, norm_cast] theorem int.cast_pow [ring R] (n : ℤ) (m : ℕ) : (↑(n ^ m) : R) = ↑n ^ m :=
by induction m with m ih; [exact int.cast_one,
  rw [pow_succ, pow_succ, int.cast_mul, ih]]

lemma neg_one_pow_eq_pow_mod_two [ring R] {n : ℕ} : (-1 : R) ^ n = (-1) ^ (n % 2) :=
by rw [← nat.mod_add_div n 2, pow_add, pow_mul]; simp [pow_two]

theorem sq_sub_sq [comm_ring R] (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
by rw [pow_two, pow_two, mul_self_sub_mul_self]

theorem pow_eq_zero [domain R] {x : R} {n : ℕ} (H : x^n = 0) : x = 0 :=
begin
  induction n with n ih,
  { rw pow_zero at H,
    rw [← mul_one x, H, mul_zero] },
  exact or.cases_on (mul_eq_zero.1 H) id ih
end

@[field_simps] theorem pow_ne_zero [domain R] {a : R} (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 :=
mt pow_eq_zero h

theorem nsmul_nonneg [ordered_add_comm_monoid R] {a : R} (H : 0 ≤ a) : ∀ n : ℕ, 0 ≤ n •ℕ a
| 0     := le_refl _
| (n+1) := add_nonneg H (nsmul_nonneg n)

lemma pow_abs [decidable_linear_ordered_comm_ring R] (a : R) (n : ℕ) : (abs a)^n = abs (a^n) :=
by induction n with n ih; [exact (abs_one).symm,
  rw [pow_succ, pow_succ, ih, abs_mul]]

lemma abs_neg_one_pow [decidable_linear_ordered_comm_ring R] (n : ℕ) : abs ((-1 : R)^n) = 1 :=
by rw [←pow_abs, abs_neg, abs_one, one_pow]

section add_monoid
variable [ordered_add_comm_monoid A]

theorem nsmul_le_nsmul {a : A} {n m : ℕ} (ha : 0 ≤ a) (h : n ≤ m) : n •ℕ a ≤ m •ℕ a :=
let ⟨k, hk⟩ := nat.le.dest h in
calc n •ℕ a = n •ℕ a + 0 : (add_zero _).symm
  ... ≤ n •ℕ a + k •ℕ a : add_le_add_left (nsmul_nonneg ha _) _
  ... = m •ℕ a : by rw [← hk, add_nsmul]

lemma nsmul_le_nsmul_of_le_right {a b : A} (hab : a ≤ b) : ∀ i : ℕ, i •ℕ a ≤ i •ℕ b
| 0 := by simp
| (k+1) := add_le_add hab (nsmul_le_nsmul_of_le_right _)

end add_monoid

namespace canonically_ordered_semiring
variable [canonically_ordered_comm_semiring R]

theorem pow_pos {a : R} (H : 0 < a) : ∀ n : ℕ, 0 < a ^ n
| 0     := canonically_ordered_semiring.zero_lt_one
| (n+1) := canonically_ordered_semiring.mul_pos.2 ⟨H, pow_pos n⟩

lemma pow_le_pow_of_le_left {a b : R} (hab : a ≤ b) : ∀ i : ℕ, a^i ≤ b^i
| 0     := by simp
| (k+1) := canonically_ordered_semiring.mul_le_mul hab (pow_le_pow_of_le_left k)

theorem one_le_pow_of_one_le {a : R} (H : 1 ≤ a) (n : ℕ) : 1 ≤ a ^ n :=
by simpa only [one_pow] using pow_le_pow_of_le_left H n

theorem pow_le_one {a : R} (H : a ≤ 1) (n : ℕ) : a ^ n ≤ 1:=
by simpa only [one_pow] using pow_le_pow_of_le_left H n

end canonically_ordered_semiring

section linear_ordered_semiring
variable [linear_ordered_semiring R]

theorem pow_pos {a : R} (H : 0 < a) : ∀ (n : ℕ), 0 < a ^ n
| 0     := zero_lt_one
| (n+1) := mul_pos H (pow_pos _)

theorem pow_nonneg {a : R} (H : 0 ≤ a) : ∀ (n : ℕ), 0 ≤ a ^ n
| 0     := zero_le_one
| (n+1) := mul_nonneg H (pow_nonneg _)

theorem pow_lt_pow_of_lt_left {x y : R} {n : ℕ} (Hxy : x < y) (Hxpos : 0 ≤ x) (Hnpos : 0 < n) :
  x ^ n < y ^ n :=
begin
  cases lt_or_eq_of_le Hxpos,
  { rw ←nat.sub_add_cancel Hnpos,
    induction (n - 1), { simpa only [pow_one] },
    rw [pow_add, pow_add, nat.succ_eq_add_one, pow_one, pow_one],
    apply mul_lt_mul ih (le_of_lt Hxy) h (le_of_lt (pow_pos (lt_trans h Hxy) _)) },
  { rw [←h, zero_pow Hnpos], apply pow_pos (by rwa ←h at Hxy : 0 < y),}
end

theorem pow_left_inj {x y : R} {n : ℕ} (Hxpos : 0 ≤ x) (Hypos : 0 ≤ y) (Hnpos : 0 < n)
  (Hxyn : x ^ n = y ^ n) : x = y :=
begin
  rcases lt_trichotomy x y with hxy | rfl | hyx,
  { exact absurd Hxyn (ne_of_lt (pow_lt_pow_of_lt_left hxy Hxpos Hnpos)) },
  { refl },
  { exact absurd Hxyn (ne_of_gt (pow_lt_pow_of_lt_left hyx Hypos Hnpos)) },
end

theorem one_le_pow_of_one_le {a : R} (H : 1 ≤ a) : ∀ (n : ℕ), 1 ≤ a ^ n
| 0     := le_refl _
| (n+1) := by simpa only [mul_one] using mul_le_mul H (one_le_pow_of_one_le n)
    zero_le_one (le_trans zero_le_one H)

/-- Bernoulli's inequality. This version works for semirings but requires
an additional hypothesis `0 ≤ a * a`. -/
theorem one_add_mul_le_pow' {a : R} (Hsqr : 0 ≤ a * a) (H : 0 ≤ 1 + a) :
  ∀ (n : ℕ), 1 + n •ℕ a ≤ (1 + a) ^ n
| 0     := le_of_eq $ add_zero _
| (n+1) :=
calc 1 + (n + 1) •ℕ a ≤ (1 + a) * (1 + n •ℕ a) :
  by simpa [succ_nsmul, mul_add, add_mul, mul_nsmul_left, add_comm, add_left_comm]
    using nsmul_nonneg Hsqr n
... ≤ (1 + a)^(n+1) : mul_le_mul_of_nonneg_left (one_add_mul_le_pow' n) H

theorem pow_le_pow {a : R} {n m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m :=
let ⟨k, hk⟩ := nat.le.dest h in
calc a ^ n = a ^ n * 1 : (mul_one _).symm
  ... ≤ a ^ n * a ^ k : mul_le_mul_of_nonneg_left
    (one_le_pow_of_one_le ha _)
    (pow_nonneg (le_trans zero_le_one ha) _)
  ... = a ^ m : by rw [←hk, pow_add]

lemma pow_lt_pow {a : R} {n m : ℕ} (h : 1 < a) (h2 : n < m) : a ^ n < a ^ m :=
begin
  have h' : 1 ≤ a := le_of_lt h,
  have h'' : 0 < a := lt_trans zero_lt_one h,
  cases m, cases h2, rw [pow_succ, ←one_mul (a ^ n)],
  exact mul_lt_mul h (pow_le_pow h' (nat.le_of_lt_succ h2)) (pow_pos h'' _) (le_of_lt h'')
end

lemma pow_le_pow_of_le_left {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) : ∀ i : ℕ, a^i ≤ b^i
| 0     := by simp
| (k+1) := mul_le_mul hab (pow_le_pow_of_le_left _) (pow_nonneg ha _) (le_trans ha hab)

lemma lt_of_pow_lt_pow {a b : R} (n : ℕ) (hb : 0 ≤ b) (h : a ^ n < b ^ n) : a < b :=
lt_of_not_ge $ λ hn, not_lt_of_ge (pow_le_pow_of_le_left hb hn _) h

private lemma pow_lt_pow_of_lt_one_aux {a : R} (h : 0 < a) (ha : a < 1) (i : ℕ) :
  ∀ k : ℕ, a ^ (i + k + 1) < a ^ i
| 0 :=
  begin
    simp only [add_zero],
    rw ←one_mul (a^i), exact mul_lt_mul ha (le_refl _) (pow_pos h _) zero_le_one
  end
| (k+1) :=
  begin
    rw ←one_mul (a^i),
    apply mul_lt_mul ha _ _ zero_le_one,
    { apply le_of_lt, apply pow_lt_pow_of_lt_one_aux },
    { show 0 < a ^ (i + (k + 1) + 0), apply pow_pos h }
  end

private lemma pow_le_pow_of_le_one_aux {a : R}  (h : 0 ≤ a) (ha : a ≤ 1) (i : ℕ) :
  ∀ k : ℕ, a ^ (i + k) ≤ a ^ i
| 0 := by simp
| (k+1) := by rw [←add_assoc, ←one_mul (a^i)];
              exact mul_le_mul ha (pow_le_pow_of_le_one_aux _) (pow_nonneg h _) zero_le_one

lemma pow_lt_pow_of_lt_one  {a : R} (h : 0 < a) (ha : a < 1)
  {i j : ℕ} (hij : i < j) : a ^ j < a ^ i :=
let ⟨k, hk⟩ := nat.exists_eq_add_of_lt hij in
by rw hk; exact pow_lt_pow_of_lt_one_aux h ha _ _

lemma pow_le_pow_of_le_one  {a : R} (h : 0 ≤ a) (ha : a ≤ 1)
  {i j : ℕ} (hij : i ≤ j) : a ^ j ≤ a ^ i :=
let ⟨k, hk⟩ := nat.exists_eq_add_of_le hij in
by rw hk; exact pow_le_pow_of_le_one_aux h ha _ _

lemma pow_le_one {x : R} : ∀ (n : ℕ) (h0 : 0 ≤ x) (h1 : x ≤ 1), x ^ n ≤ 1
| 0     h0 h1 := le_refl (1 : R)
| (n+1) h0 h1 := mul_le_one h1 (pow_nonneg h0 _) (pow_le_one n h0 h1)

end linear_ordered_semiring

theorem pow_two_nonneg [linear_ordered_ring R] (a : R) : 0 ≤ a ^ 2 :=
by { rw pow_two, exact mul_self_nonneg _ }

theorem pow_two_pos_of_ne_zero [linear_ordered_ring R] (a : R) (h : a ≠ 0) : 0 < a ^ 2 :=
lt_of_le_of_ne (pow_two_nonneg a) (pow_ne_zero 2 h).symm

/-- Bernoulli's inequality for `n : ℕ`, `-2 ≤ a`. -/
theorem one_add_mul_le_pow [linear_ordered_ring R] {a : R} (H : -2 ≤ a) :
  ∀ (n : ℕ), 1 + n •ℕ a ≤ (1 + a) ^ n
| 0     := le_of_eq $ add_zero _
| 1     := by simp
| (n+2) :=
have H' : 0 ≤ 2 + a,
  from neg_le_iff_add_nonneg.1 H,
have 0 ≤ n •ℕ (a * a * (2 + a)) + a * a,
  from add_nonneg (nsmul_nonneg (mul_nonneg (mul_self_nonneg a) H') n)
    (mul_self_nonneg a),
calc 1 + (n + 2) •ℕ a ≤ 1 + (n + 2) •ℕ a + (n •ℕ (a * a * (2 + a)) + a * a) :
  (le_add_iff_nonneg_right _).2 this
... = (1 + a) * (1 + a) * (1 + n •ℕ a) :
  by { simp only [add_mul, mul_add, mul_two, mul_one, one_mul, succ_nsmul, nsmul_add,
         mul_nsmul_assoc, (mul_nsmul_left _ _ _).symm],
       ac_refl }
... ≤ (1 + a) * (1 + a) * (1 + a)^n :
  mul_le_mul_of_nonneg_left (one_add_mul_le_pow n) (mul_self_nonneg (1 + a))
... = (1 + a)^(n + 2) : by simp only [pow_succ, mul_assoc]

/-- Bernoulli's inequality reformulated to estimate `a^n`. -/
theorem one_add_sub_mul_le_pow [linear_ordered_ring R]
  {a : R} (H : -1 ≤ a) (n : ℕ) : 1 + n •ℕ (a - 1) ≤ a ^ n :=
have -2 ≤ a - 1, by { rw [bit0, neg_add], exact sub_le_sub_right H 1 },
by simpa only [add_sub_cancel'_right] using one_add_mul_le_pow this n

namespace int

lemma units_pow_two (u : units ℤ) : u ^ 2 = 1 :=
(units_eq_one_or u).elim (λ h, h.symm ▸ rfl) (λ h, h.symm ▸ rfl)

lemma units_pow_eq_pow_mod_two (u : units ℤ) (n : ℕ) : u ^ n = u ^ (n % 2) :=
by conv {to_lhs, rw ← nat.mod_add_div n 2}; rw [pow_add, pow_mul, units_pow_two, one_pow, mul_one]

@[simp] lemma nat_abs_pow_two (x : ℤ) : (x.nat_abs ^ 2 : ℤ) = x ^ 2 :=
by rw [pow_two, int.nat_abs_mul_self', pow_two]

end int

@[simp] lemma neg_square {α} [ring α] (z : α) : (-z)^2 = z^2 :=
by simp [pow, monoid.pow]

lemma of_add_nsmul [add_monoid A] (x : A) (n : ℕ) :
  multiplicative.of_add (n •ℕ x) = (multiplicative.of_add x)^n := rfl

lemma of_add_gsmul [add_group A] (x : A) (n : ℤ) :
  multiplicative.of_add (n •ℤ x) = (multiplicative.of_add x)^n := rfl

variables (M G A)

/-- Monoid homomorphisms from `multiplicative ℕ` are defined by the image
of `multiplicative.of_add 1`. -/
def powers_hom [monoid M] : M ≃ (multiplicative ℕ →* M) :=
{ to_fun := λ x, ⟨λ n, x ^ n.to_add, pow_zero x, λ m n, pow_add x m n⟩,
  inv_fun := λ f, f (multiplicative.of_add 1),
  left_inv := pow_one,
  right_inv := λ f, monoid_hom.ext $ λ n, by { simp [← f.map_pow, ← of_add_nsmul] } }

/-- Monoid homomorphisms from `multiplicative ℤ` are defined by the image
of `multiplicative.of_add 1`. -/
def gpowers_hom [group G] : G ≃ (multiplicative ℤ →* G) :=
{ to_fun := λ x, ⟨λ n, x ^ n.to_add, gpow_zero x, λ m n, gpow_add x m n⟩,
  inv_fun := λ f, f (multiplicative.of_add 1),
  left_inv := gpow_one,
  right_inv := λ f, monoid_hom.ext $ λ n, by { simp [← f.map_gpow, ← of_add_gsmul ] } }

/-- Additive homomorphisms from `ℕ` are defined by the image of `1`. -/
def multiples_hom [add_monoid A] : A ≃ (ℕ →+ A) :=
{ to_fun := λ x, ⟨λ n, n •ℕ x, zero_nsmul x, λ m n, add_nsmul _ _ _⟩,
  inv_fun := λ f, f 1,
  left_inv := one_nsmul,
  right_inv := λ f, add_monoid_hom.ext_nat $ one_nsmul (f 1) }

/-- Additive homomorphisms from `ℤ` are defined by the image of `1`. -/
def gmultiples_hom [add_group A] : A ≃ (ℤ →+ A) :=
{ to_fun := λ x, ⟨λ n, n •ℤ x, zero_gsmul x, λ m n, add_gsmul _ _ _⟩,
  inv_fun := λ f, f 1,
  left_inv := one_gsmul,
  right_inv := λ f, add_monoid_hom.ext_int $ one_gsmul (f 1) }

variables {M G A}

@[simp] lemma powers_hom_apply [monoid M] (x : M) (n : multiplicative ℕ) :
  powers_hom M x n = x ^ n.to_add := rfl

@[simp] lemma powers_hom_symm_apply [monoid M] (f : multiplicative ℕ →* M) :
  (powers_hom M).symm f = f (multiplicative.of_add 1) := rfl

lemma mnat_monoid_hom_eq [monoid M] (f : multiplicative ℕ →* M) (n : multiplicative ℕ) :
  f n = (f (multiplicative.of_add 1)) ^ n.to_add :=
by rw [← powers_hom_symm_apply, ← powers_hom_apply, equiv.apply_symm_apply]

lemma mnat_monoid_hom_ext [monoid M] ⦃f g : multiplicative ℕ →* M⦄
  (h : f (multiplicative.of_add 1) = g (multiplicative.of_add 1)) : f = g :=
monoid_hom.ext $ λ n, by rw [mnat_monoid_hom_eq f, mnat_monoid_hom_eq g, h]

/-!
### Commutativity (again)

Facts about `semiconj_by` and `commute` that require `gpow` or `gsmul`, or the fact that integer
multiplication equals semiring multiplication.
-/

namespace semiconj_by

section

variables [semiring R] {a x y : R}

@[simp] lemma cast_nat_mul_right (h : semiconj_by a x y) (n : ℕ) : semiconj_by a ((n : R) * x) (n * y) :=
semiconj_by.mul_right (nat.commute_cast _ _) h

@[simp] lemma cast_nat_mul_left (h : semiconj_by a x y) (n : ℕ) : semiconj_by ((n : R) * a) x y :=
semiconj_by.mul_left (nat.cast_commute _ _) h

@[simp] lemma cast_nat_mul_cast_nat_mul (h : semiconj_by a x y) (m n : ℕ) :
  semiconj_by ((m : R) * a) (n * x) (n * y) :=
(h.cast_nat_mul_left m).cast_nat_mul_right n

end

variables [monoid M] [group G] [ring R]

@[simp] lemma units_gpow_right {a : M} {x y : units M} (h : semiconj_by a x y) :
  ∀ m : ℤ, semiconj_by a (↑(x^m)) (↑(y^m))
| (n : ℕ) := by simp only [gpow_coe_nat, units.coe_pow, h, pow_right]
| -[1+n] := by simp only [gpow_neg_succ_of_nat, units.coe_pow, units_inv_right, h, pow_right]

@[simp] lemma gpow_right {a x y : G} (h : semiconj_by a x y) : ∀ m : ℤ, semiconj_by a (x^m) (y^m)
| (n : ℕ) := h.pow_right n
| -[1+n] := (h.pow_right n.succ).inv_right

variables {a b x y x' y' : R}

@[simp] lemma cast_int_mul_right (h : semiconj_by a x y) (m : ℤ) :
  semiconj_by a ((m : ℤ) * x) (m * y) :=
semiconj_by.mul_right (int.commute_cast _ _) h

@[simp] lemma cast_int_mul_left (h : semiconj_by a x y) (m : ℤ) : semiconj_by ((m : R) * a) x y :=
semiconj_by.mul_left (int.cast_commute _ _) h

@[simp] lemma cast_int_mul_cast_int_mul (h : semiconj_by a x y) (m n : ℤ) :
  semiconj_by ((m : R) * a) (n * x) (n * y) :=
(h.cast_int_mul_left m).cast_int_mul_right n

end semiconj_by

namespace commute

section

variables [semiring R] {a b : R}

@[simp] theorem cast_nat_mul_right (h : commute a b) (n : ℕ) : commute a ((n : R) * b) :=
h.cast_nat_mul_right n

@[simp] theorem cast_nat_mul_left (h : commute a b) (n : ℕ) : commute ((n : R) * a) b :=
h.cast_nat_mul_left n

@[simp] theorem cast_nat_mul_cast_nat_mul (h : commute a b) (m n : ℕ) :
  commute ((m : R) * a) (n * b) :=
h.cast_nat_mul_cast_nat_mul m n

@[simp] theorem self_cast_nat_mul (n : ℕ) : commute a (n * a) :=
(commute.refl a).cast_nat_mul_right n

@[simp] theorem cast_nat_mul_self (n : ℕ) : commute ((n : R) * a) a :=
(commute.refl a).cast_nat_mul_left n

@[simp] theorem self_cast_nat_mul_cast_nat_mul (m n : ℕ) : commute ((m : R) * a) (n * a) :=
(commute.refl a).cast_nat_mul_cast_nat_mul m n

end

variables [monoid M] [group G] [ring R]

@[simp] lemma units_gpow_right {a : M} {u : units M} (h : commute a u) (m : ℤ) :
  commute a (↑(u^m)) :=
h.units_gpow_right m

@[simp] lemma units_gpow_left {u : units M} {a : M} (h : commute ↑u a) (m : ℤ) :
  commute (↑(u^m)) a :=
(h.symm.units_gpow_right m).symm

section

variables {a b : G}

@[simp] lemma gpow_right (h : commute a b) (m : ℤ) : commute a (b^m) :=
h.gpow_right m

@[simp] lemma gpow_left (h : commute a b) (m : ℤ) : commute (a^m) b :=
(h.symm.gpow_right m).symm

lemma gpow_gpow (h : commute a b) (m n : ℤ) : commute (a^m) (b^n) := (h.gpow_left m).gpow_right n

variables (a) (m n : ℕ)

@[simp] theorem self_gpow : commute a (a ^ n) := (commute.refl a).gpow_right n
@[simp] theorem gpow_self : commute (a ^ n) a := (commute.refl a).gpow_left n
@[simp] theorem gpow_gpow_self : commute (a ^ m) (a ^ n) := (commute.refl a).gpow_gpow m n

end

variables {a b : R}

@[simp] lemma cast_int_mul_right (h : commute a b) (m : ℤ) : commute a (m * b) :=
h.cast_int_mul_right m

@[simp] lemma cast_int_mul_left (h : commute a b) (m : ℤ) : commute ((m : R) * a) b :=
h.cast_int_mul_left m

lemma cast_int_mul_cast_int_mul (h : commute a b) (m n : ℤ) : commute ((m : R) * a) (n * b) :=
h.cast_int_mul_cast_int_mul m n

variables (a) (m n : ℤ)

@[simp] theorem self_cast_int_mul : commute a (n * a) := (commute.refl a).cast_int_mul_right n

@[simp] theorem cast_int_mul_self : commute ((n : R) * a) a := (commute.refl a).cast_int_mul_left n

theorem self_cast_int_mul_cast_int_mul : commute ((m : R) * a) (n * a) :=
(commute.refl a).cast_int_mul_cast_int_mul m n

end commute

namespace units

variables [monoid M]

lemma conj_pow (u : units M) (x : M) (n : ℕ) : (↑u * x * ↑(u⁻¹))^n = u * x^n * ↑(u⁻¹) :=
(divp_eq_iff_mul_eq.2 ((u.mk_semiconj_by x).pow_right n).eq.symm).symm

lemma conj_pow' (u : units M) (x : M) (n : ℕ) : (↑(u⁻¹) * x * u)^n = ↑(u⁻¹) * x^n * u:=
(u⁻¹).conj_pow x n

open opposite

/-- Moving to the opposite monoid commutes with taking powers. -/
@[simp] lemma op_pow (x : M) (n : ℕ) : op (x ^ n) = (op x) ^ n :=
begin
  induction n with n h,
  { simp },
  { rw [pow_succ', op_mul, h, pow_succ] }
end

@[simp] lemma unop_pow (x : Mᵒᵖ) (n : ℕ) : unop (x ^ n) = (unop x) ^ n :=
begin
  induction n with n h,
  { simp },
  { rw [pow_succ', unop_mul, h, pow_succ] }
end

end units
