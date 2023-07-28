/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import algebra.group.defs
import algebra.ne_zero

/-!
# Cast of natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the *canonical* homomorphism from the natural numbers into an
`add_monoid` with a one.  In additive monoids with one, there exists a unique
such homomorphism and we store it in the `nat_cast : ℕ → R` field.

Preferentially, the homomorphism is written as a coercion.

## Main declarations

* `add_monoid_with_one`: Type class for `nat.cast`.
* `nat.cast`: Canonical homomorphism `ℕ → R`.
-/

universes u
set_option old_structure_cmd true

/-- The numeral `((0+1)+⋯)+1`. -/
protected def nat.unary_cast {R : Type u} [has_one R] [has_zero R] [has_add R] : ℕ → R
| 0 := 0
| (n + 1) := nat.unary_cast n + 1

/--
Type class for the canonical homomorphism `ℕ → R`.
-/
@[protect_proj]
class has_nat_cast (R : Type u) :=
(nat_cast : ℕ → R)

/--
An `add_monoid_with_one` is an `add_monoid` with a `1`.
It also contains data for the unique homomorphism `ℕ → R`.
-/
@[protect_proj, ancestor has_nat_cast add_monoid has_one]
class add_monoid_with_one (R : Type u) extends has_nat_cast R, add_monoid R, has_one R :=
(nat_cast := nat.unary_cast)
(nat_cast_zero : nat_cast 0 = (0 : R) . control_laws_tac)
(nat_cast_succ : ∀ n, nat_cast (n + 1) = (nat_cast n + 1 : R) . control_laws_tac)

/-- Canonical homomorphism from `ℕ` to a additive monoid `R` with a `1`. -/
protected def nat.cast {R : Type u} [has_nat_cast R] : ℕ → R := has_nat_cast.nat_cast

/-- An `add_comm_monoid_with_one` is an `add_monoid_with_one` satisfying `a + b = b + a`.  -/
@[protect_proj, ancestor add_monoid_with_one add_comm_monoid]
class add_comm_monoid_with_one (R : Type*) extends add_monoid_with_one R, add_comm_monoid R

section
variables {R : Type*} [add_monoid_with_one R]

/--
Coercions such as `nat.cast_coe` that go from a concrete structure such as
`ℕ` to an arbitrary ring `R` should be set up as follows:
```lean
@[priority 900] instance : has_coe_t ℕ R := ⟨...⟩
```

It needs to be `has_coe_t` instead of `has_coe` because otherwise type-class
inference would loop when constructing the transitive coercion `ℕ → ℕ → ℕ → ...`.
The reduced priority is necessary so that it doesn't conflict with instances
such as `has_coe_t R (option R)`.

For this to work, we reduce the priority of the `coe_base` and `coe_trans`
instances because we want the instances for `has_coe_t` to be tried in the
following order:

 1. `has_coe_t` instances declared in mathlib (such as `has_coe_t R (with_top R)`, etc.)
 2. `coe_base`, which contains instances such as `has_coe (fin n) n`
 3. `nat.cast_coe : has_coe_t ℕ R` etc.
 4. `coe_trans`

If `coe_trans` is tried first, then `nat.cast_coe` doesn't get a chance to apply.
-/
library_note "coercion into rings"
attribute [instance, priority 950] coe_base
attribute [instance, priority 500] coe_trans

namespace nat

-- see note [coercion into rings]
@[priority 900] instance cast_coe {R} [has_nat_cast R] : has_coe_t ℕ R := ⟨nat.cast⟩

@[simp, norm_cast] theorem cast_zero : ((0 : ℕ) : R) = 0 := add_monoid_with_one.nat_cast_zero

-- Lemmas about nat.succ need to get a low priority, so that they are tried last.
-- This is because `nat.succ _` matches `1`, `3`, `x+1`, etc.
-- Rewriting would then produce really wrong terms.
@[simp, norm_cast, priority 500]
theorem cast_succ (n : ℕ) : ((succ n : ℕ) : R) = n + 1 := add_monoid_with_one.nat_cast_succ _

theorem cast_add_one (n : ℕ) : ((n + 1 : ℕ) : R) = n + 1 := cast_succ _

@[simp, norm_cast] theorem cast_ite (P : Prop) [decidable P] (m n : ℕ) :
  (((ite P m n) : ℕ) : R) = ite P (m : R) (n : R) :=
by { split_ifs; refl, }

end nat

end

namespace nat
variables {R : Type*}

@[simp, norm_cast] theorem cast_one [add_monoid_with_one R] : ((1 : ℕ) : R) = 1 :=
by rw [cast_succ, cast_zero, zero_add]

@[simp, norm_cast] theorem cast_add [add_monoid_with_one R] (m n : ℕ) : ((m + n : ℕ) : R) = m + n :=
by induction n; simp [add_succ, add_assoc, nat.add_zero, *]

/-- Computationally friendlier cast than `nat.unary_cast`, using binary representation. -/
protected def bin_cast [has_zero R] [has_one R] [has_add R] (n : ℕ) : R :=
@nat.binary_rec (λ _, R) 0 (λ odd k a, cond odd (a + a + 1) (a + a)) n

@[simp] lemma bin_cast_eq [add_monoid_with_one R] (n : ℕ) : (nat.bin_cast n : R) = ((n : ℕ) : R) :=
begin
  rw nat.bin_cast,
  apply binary_rec _ _ n,
  { rw [binary_rec_zero, cast_zero] },
  { intros b k h,
    rw [binary_rec_eq, h],
    { cases b; simp [bit, bit0, bit1] },
    { simp } },
end

@[simp, norm_cast] theorem cast_bit0 [add_monoid_with_one R] (n : ℕ) :
  ((bit0 n : ℕ) : R) = bit0 n := cast_add _ _

@[simp, norm_cast] theorem cast_bit1 [add_monoid_with_one R] (n : ℕ) :
  ((bit1 n : ℕ) : R) = bit1 n :=
by rw [bit1, cast_add_one, cast_bit0]; refl

lemma cast_two [add_monoid_with_one R] : ((2 : ℕ) : R) = 2 :=
by rw [cast_add_one, cast_one, bit0]

attribute [simp, norm_cast] int.nat_abs_of_nat

end nat

/-- `add_monoid_with_one` implementation using unary recursion. -/
@[reducible] protected def add_monoid_with_one.unary {R : Type*} [add_monoid R] [has_one R] :
  add_monoid_with_one R :=
{ .. ‹has_one R›, .. ‹add_monoid R› }

/-- `add_monoid_with_one` implementation using binary recursion. -/
@[reducible] protected def add_monoid_with_one.binary {R : Type*} [add_monoid R] [has_one R] :
  add_monoid_with_one R :=
{ nat_cast := nat.bin_cast,
  nat_cast_zero := by simp [nat.bin_cast, nat.cast],
  nat_cast_succ := λ n, begin
    simp only [nat.cast],
    letI : add_monoid_with_one R := add_monoid_with_one.unary,
    erw [nat.bin_cast_eq, nat.bin_cast_eq, nat.cast_succ],
    refl,
  end,
  .. ‹has_one R›, .. ‹add_monoid R› }

namespace ne_zero

lemma nat_cast_ne (n : ℕ) (R) [add_monoid_with_one R] [h : ne_zero (n : R)] :
  (n : R) ≠ 0 := h.out

lemma of_ne_zero_coe (R) [add_monoid_with_one R] {n : ℕ} [h : ne_zero (n : R)] : ne_zero n :=
⟨by {casesI h, rintro rfl, by simpa using h}⟩

lemma pos_of_ne_zero_coe (R) [add_monoid_with_one R] {n : ℕ} [ne_zero (n : R)] : 0 < n :=
nat.pos_of_ne_zero (of_ne_zero_coe R).out

end ne_zero
