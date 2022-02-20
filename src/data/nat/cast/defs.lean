/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import algebra.group.defs
import algebra.group.basic

/-!
# Cast of natural numbers

This file defines the *canonical* homomorphism from the natural numbers into an
`add_monoid` with a one.

## Main declarations

* `add_monoid_with_one`: Type class for `nat.cast`.
* `nat.cast`: Canonical homomorphism `ℕ → α`.
-/

universes u
set_option old_structure_cmd true

/-- The numeral `((0+1)+⋯)+1`. -/
protected def nat.unary_cast {α : Type u} [has_one α] [has_zero α] [has_add α] : ℕ → α
| 0 := 0
| (n + 1) := nat.unary_cast n + 1

class add_monoid_with_one (α : Type u) extends add_monoid α, has_one α :=
(nat_cast : ℕ → α := nat.unary_cast)
(nat_cast_zero : nat_cast 0 = (0 : α) . control_laws_tac)
(nat_cast_succ : ∀ n, nat_cast (n + 1) = (nat_cast n + 1 : α) . control_laws_tac)

/-- Canonical homomorphism from `ℕ` to a additive monoid `α` with a `1`. -/
protected def nat.cast {α : Type*} [add_monoid_with_one α] : ℕ → α := add_monoid_with_one.nat_cast

class add_comm_monoid_with_one (α : Type*) extends add_monoid_with_one α, add_comm_monoid α

section
variables {α : Type*} [add_monoid_with_one α]

/--
Coercions such as `nat.cast_coe` that go from a concrete structure such as
`ℕ` to an arbitrary ring `α` should be set up as follows:
```lean
@[priority 900] instance : has_coe_t ℕ α := ⟨...⟩
```

It needs to be `has_coe_t` instead of `has_coe` because otherwise type-class
inference would loop when constructing the transitive coercion `ℕ → ℕ → ℕ → ...`.
The reduced priority is necessary so that it doesn't conflict with instances
such as `has_coe_t α (option α)`.

For this to work, we reduce the priority of the `coe_base` and `coe_trans`
instances because we want the instances for `has_coe_t` to be tried in the
following order:

 1. `has_coe_t` instances declared in mathlib (such as `has_coe_t α (with_top α)`, etc.)
 2. `coe_base`, which contains instances such as `has_coe (fin n) n`
 3. `nat.cast_coe : has_coe_t ℕ α` etc.
 4. `coe_trans`

If `coe_trans` is tried first, then `nat.cast_coe` doesn't get a chance to apply.
-/
library_note "coercion into rings"
attribute [instance, priority 950] coe_base
attribute [instance, priority 500] coe_trans

namespace nat

-- see note [coercion into rings]
@[priority 900] instance cast_coe : has_coe_t ℕ α := ⟨nat.cast⟩

@[simp, norm_cast] theorem cast_zero : ((0 : ℕ) : α) = 0 := add_monoid_with_one.nat_cast_zero

-- Lemmas about nat.succ need to get a low priority, so that they are tried last.
-- This is because `nat.succ _` matches `1`, `3`, `x+1`, etc.
-- Rewriting would then produce really wrong terms.
@[simp, norm_cast, priority 500]
theorem cast_succ (n : ℕ) : ((succ n : ℕ) : α) = n + 1 := add_monoid_with_one.nat_cast_succ _

theorem cast_add_one (n : ℕ) : ((n + 1 : ℕ) : α) = n + 1 := cast_succ _

@[simp, norm_cast] theorem cast_ite (P : Prop) [decidable P] (m n : ℕ) :
  (((ite P m n) : ℕ) : α) = ite P (m : α) (n : α) :=
by { split_ifs; refl, }

end nat

end

namespace nat
variables {α : Type*}

@[simp, norm_cast] theorem cast_one [add_monoid_with_one α] : ((1 : ℕ) : α) = 1 :=
by rw [cast_succ, cast_zero, zero_add]

@[simp, norm_cast] theorem cast_add [add_monoid_with_one α] (m n : ℕ) : ((m + n : ℕ) : α) = m + n :=
by induction n; simp [add_succ, add_assoc, nat.add_zero, *]

/-- Computationally friendlier cast than `nat.unary_cast`, using binary representation. -/
protected def bin_cast [has_zero α] [has_one α] [has_add α] (n : ℕ) : α :=
@nat.binary_rec (λ _, α) 0 (λ odd k a, cond odd (a + a + 1) (a + a)) n

@[simp] lemma bin_cast_eq [add_monoid_with_one α] (n : ℕ) : (nat.bin_cast n : α) = ((n : ℕ) : α) :=
begin
  rw nat.bin_cast,
  apply binary_rec _ _ n,
  { rw [binary_rec_zero, cast_zero] },
  { intros b k h,
    rw [binary_rec_eq, h],
    { cases b; simp [bit, bit0, bit1] },
    { simp } },
end

@[simp, norm_cast] theorem cast_bit0 [add_monoid_with_one α] (n : ℕ) :
  ((bit0 n : ℕ) : α) = bit0 n := cast_add _ _

@[simp, norm_cast] theorem cast_bit1 [add_monoid_with_one α] (n : ℕ) :
  ((bit1 n : ℕ) : α) = bit1 n :=
by rw [bit1, cast_add_one, cast_bit0]; refl

lemma cast_two [add_monoid_with_one α] : ((2 : ℕ) : α) = 2 :=
by rw [cast_add_one, cast_one, bit0]

attribute [simp, norm_cast] int.nat_abs_of_nat

end nat

@[reducible] protected def add_monoid_with_one.unary {α : Type*} [add_monoid α] [has_one α] :
  add_monoid_with_one α :=
{ .. ‹has_one α›, .. ‹add_monoid α› }

@[reducible] protected def add_monoid_with_one.binary {α : Type*} [add_monoid α] [has_one α] :
  add_monoid_with_one α :=
{ nat_cast := nat.bin_cast,
  nat_cast_zero := by simp [nat.bin_cast, nat.cast],
  nat_cast_succ := λ n, begin
    simp only [nat.cast],
    letI : add_monoid_with_one α := add_monoid_with_one.unary,
    erw [nat.bin_cast_eq, nat.bin_cast_eq, nat.cast_succ],
    refl,
  end,
  .. ‹has_one α›, .. ‹add_monoid α› }
