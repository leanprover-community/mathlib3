/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import algebra.group.type_tags

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
begin
  induction n with n ih,
  { rw [nat.add_zero, pow_zero, mul_one] },
  { rw [pow_succ', ← mul_assoc, ← ih, ← pow_succ', nat.add_assoc] }
end
theorem add_nsmul : ∀ (a : A) (m n : ℕ), (m + n) •ℕ a = m •ℕ a + n •ℕ a :=
@pow_add (multiplicative A) _

@[simp] theorem one_pow (n : ℕ) : (1 : M)^n = 1 :=
by induction n with n ih; [refl, rw [pow_succ, ih, one_mul]]
@[simp] theorem nsmul_zero (n : ℕ) : n •ℕ (0 : A) = 0 :=
by induction n with n ih; [refl, rw [succ_nsmul, ih, zero_add]]

theorem pow_mul (a : M) (m n : ℕ) : a^(m * n) = (a^m)^n :=
by induction n with n ih; [rw nat.mul_zero, rw [nat.mul_succ, pow_add, pow_succ', ih]]; refl
theorem mul_nsmul' : ∀ (a : A) (m n : ℕ), m * n •ℕ a = n •ℕ (m •ℕ a) :=
@pow_mul (multiplicative A) _

theorem pow_mul' (a : M) (m n : ℕ) : a^(m * n) = (a^n)^m :=
by rw [nat.mul_comm, pow_mul]
theorem mul_nsmul (a : A) (m n : ℕ) : m * n •ℕ a = m •ℕ (n •ℕ a) :=
@pow_mul' (multiplicative A) _ a m n

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

end monoid

