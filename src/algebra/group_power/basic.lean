/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import algebra.order_functions
import deprecated.group

/-!
# Power operations on monoids and groups

The power operation on monoids and groups.
We separate this from group, because it depends on `ℕ`,
which in turn depends on other parts of algebra.

This module contains the definitions of `monoid.pow` and `group.pow`
and their additive counterparts `nsmul` and `gsmul`, along with a few lemmas.
Further lemmas can be found in `algebra.group_power.lemmas`.

## Notation

The class `has_pow α β` provides the notation `a^b` for powers.
We define instances of `has_pow M ℕ`, for monoids `M`, and `has_pow G ℤ` for groups `G`.

We also define infix operators `•ℕ` and `•ℤ` for scalar multiplication by a natural and an integer
numbers, respectively.

## Implementation details

We adopt the convention that `0^0 = 1`.

This module provides the instance `has_pow ℕ ℕ` (via `monoid.has_pow`)
and is imported by `data.nat.basic`, so it has to live low in the import hierarchy.
Not all of its imports are needed yet; the intent is to move more lemmas here from `.lemmas`
so that they are available in `data.nat.basic`, and the imports will be required then.
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

section monoid
variables [monoid M] [monoid N] [add_monoid A] [add_monoid B]

@[simp] theorem pow_zero (a : M) : a^0 = 1 := rfl
@[simp] theorem zero_nsmul (a : A) : 0 •ℕ a = 0 := rfl

theorem pow_succ (a : M) (n : ℕ) : a^(n+1) = a * a^n := rfl
theorem succ_nsmul (a : A) (n : ℕ) : (n+1) •ℕ a = a + n •ℕ a := rfl

theorem pow_two (a : M) : a^2 = a * a :=
show a*(a*1)=a*a, by rw mul_one
theorem two_nsmul (a : A) : 2 •ℕ a = a + a :=
@pow_two (multiplicative A) _ a

theorem pow_mul_comm' (a : M) (n : ℕ) : a^n * a = a * a^n := commute.pow_self a n
theorem nsmul_add_comm' : ∀ (a : A) (n : ℕ), n •ℕ a + a = a + n •ℕ a :=
@pow_mul_comm' (multiplicative A) _

theorem pow_succ' (a : M) (n : ℕ) : a^(n+1) = a^n * a :=
by rw [pow_succ, pow_mul_comm']
theorem succ_nsmul' (a : A) (n : ℕ) : (n+1) •ℕ a = n •ℕ a + a :=
@pow_succ' (multiplicative A) _ _ _

theorem pow_add (a : M) (m n : ℕ) : a^(m + n) = a^m * a^n :=
by induction n with n ih; [rw [nat.add_zero, pow_zero, mul_one],
  rw [pow_succ', ← mul_assoc, ← ih, ← pow_succ', nat.add_assoc]]
theorem add_nsmul : ∀ (a : A) (m n : ℕ), (m + n) •ℕ a = m •ℕ a + n •ℕ a :=
@pow_add (multiplicative A) _

end monoid

section group
variables [group G] [group H] [add_group A] [add_group B]

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

end group
