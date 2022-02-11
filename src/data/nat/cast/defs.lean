/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import algebra.group.defs
import algebra.group.basic

/-!
# Cast of naturals

This file defines the *canonical* homomorphism from the natural numbers into a type `α` with `0`,
`1` and `+` (typically an `add_monoid` with one).

## Main declarations

* `cast`: Canonical homomorphism `ℕ → α` where `α` has a `0`, `1` and `+`.
* `bin_cast`: Binary representation version of `cast`.
* `cast_add_monoid_hom`: `cast` bundled as an `add_monoid_hom`.
* `cast_ring_hom`: `cast` bundled as a `ring_hom`.

## Implementation note

Setting up the coercions priorities is tricky. See Note [coercion into rings].
-/

set_option old_structure_cmd true

class has_nat_cast_aux (α : Type*) :=
(nat_cast : ℕ → α)

/-- Canonical homomorphism from `ℕ` to a type `α` with `0`, `1` and `+`. -/
protected def nat.cast {α : Type*} [has_nat_cast_aux α] : ℕ → α := has_nat_cast_aux.nat_cast

class has_nat_cast (α : Type*) extends add_monoid α, has_one α, has_nat_cast_aux α :=
(nat_cast_zero : nat.cast 0 = (0 : α))
(nat_cast_succ : ∀ n, nat.cast (n + 1) = (nat.cast n + 1 : α))

class add_group_with_one (α : Type*) extends add_group α, has_one α, has_nat_cast α

section
variables {α : Type*} [has_nat_cast α]

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

@[simp, norm_cast] theorem cast_zero : ((0 : ℕ) : α) = 0 := has_nat_cast.nat_cast_zero

@[simp, norm_cast, priority 500]
theorem cast_succ (n : ℕ) : ((succ n : ℕ) : α) = n + 1 := has_nat_cast.nat_cast_succ _

theorem cast_add_one (n : ℕ) : ((n + 1 : ℕ) : α) = n + 1 := cast_succ _

@[simp, norm_cast] theorem cast_ite (P : Prop) [decidable P] (m n : ℕ) :
  (((ite P m n) : ℕ) : α) = ite P (m : α) (n : α) :=
by { split_ifs; refl, }

end nat

end

namespace nat
variables {α : Type*}

@[simp, norm_cast] theorem cast_one [has_nat_cast α] : ((1 : ℕ) : α) = 1 :=
by rw [cast_succ, cast_zero, zero_add]

@[simp, norm_cast] theorem cast_add [has_nat_cast α] (m n : ℕ) : ((m + n : ℕ) : α) = m + n :=
by induction n; simp [add_succ, add_assoc, nat.add_zero, *]

/-- Computationally friendlier cast than `nat.cast`, using binary representation. -/
protected def bin_cast [has_zero α] [has_one α] [has_add α] (n : ℕ) : α :=
@nat.binary_rec (λ _, α) 0 (λ odd k a, cond odd (a + a + 1) (a + a)) n

@[simp] lemma bin_cast_eq [has_nat_cast α] (n : ℕ) : (nat.bin_cast n : α) = ((n : ℕ) : α) :=
begin
  rw nat.bin_cast,
  apply binary_rec _ _ n,
  { rw [binary_rec_zero, cast_zero] },
  { intros b k h,
    rw [binary_rec_eq, h],
    { cases b; simp [bit, bit0, bit1] },
    { simp } },
end

@[simp, norm_cast] theorem cast_bit0 [has_nat_cast α] (n : ℕ) :
  ((bit0 n : ℕ) : α) = bit0 n := cast_add _ _

@[simp, norm_cast] theorem cast_bit1 [has_nat_cast α] (n : ℕ) :
  ((bit1 n : ℕ) : α) = bit1 n :=
by rw [bit1, cast_add_one, cast_bit0]; refl

lemma cast_two [has_nat_cast α] : ((2 : ℕ) : α) = 2 :=
by rw [cast_add_one, cast_one, bit0]

@[simp, norm_cast] theorem cast_sub [add_group_with_one α] {m n} (h : m ≤ n) :
  ((n - m : ℕ) : α) = n - m :=
eq_sub_of_add_eq $ by rw [← cast_add, nat.sub_add_cancel h]

@[simp, norm_cast] theorem cast_pred [add_group_with_one α] :
  ∀ {n}, 0 < n → ((n - 1 : ℕ) : α) = n - 1
| 0 h := by cases h
| (n+1) h := by rw [cast_succ, add_sub_cancel]; refl

end nat
