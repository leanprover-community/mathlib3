/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import data.nat.cast.defs

/-!
# Cast of integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the *canonical* homomorphism from the integers into an
additive group with a one (typically a `ring`).  In additive groups with a one
element, there exists a unique such homomorphism and we store it in the
`int_cast : ℤ → R` field.

Preferentially, the homomorphism is written as a coercion.

## Main declarations

* `int.cast`: Canonical homomorphism `ℤ → R`.
* `add_group_with_one`: Type class for `int.cast`.
-/

universes u
set_option old_structure_cmd true

attribute [simp] int.of_nat_eq_coe

/-- Default value for `add_group_with_one.int_cast`. -/
protected def int.cast_def {R : Type u} [has_nat_cast R] [has_neg R] : ℤ → R
| (n : ℕ) := n
| -[1+ n] := -(n+1 : ℕ)

/--
Type class for the canonical homomorphism `ℤ → R`.
-/
class has_int_cast (R : Type u) :=
(int_cast : ℤ → R)

/--
An `add_group_with_one` is an `add_group` with a `1`.
It also contains data for the unique homomorphisms `ℕ → R` and `ℤ → R`.
-/
@[protect_proj, ancestor has_int_cast add_group add_monoid_with_one]
class add_group_with_one (R : Type u)
  extends has_int_cast R, add_group R, add_monoid_with_one R :=
(int_cast := int.cast_def)
(int_cast_of_nat : ∀ n : ℕ, int_cast n = (n : R) . control_laws_tac)
(int_cast_neg_succ_of_nat : ∀ n : ℕ, int_cast (-(n+1 : ℕ)) = -((n+1 : ℕ) : R) . control_laws_tac)

/-- An `add_comm_group_with_one` is an `add_group_with_one` satisfying `a + b = b + a`. -/
@[protect_proj, ancestor add_comm_group add_group_with_one]
class add_comm_group_with_one (R : Type u) extends add_comm_group R, add_group_with_one R

/-- Canonical homomorphism from the integers to any ring(-like) structure `R` -/
protected def int.cast {R : Type u} [has_int_cast R] (i : ℤ) : R := has_int_cast.int_cast i

open nat

namespace int
variables {R : Type u} [add_group_with_one R]

-- see Note [coercion into rings]
@[priority 900] instance cast_coe {R} [has_int_cast R] : has_coe_t ℤ R := ⟨int.cast⟩

theorem cast_of_nat (n : ℕ) : (of_nat n : R) = n := add_group_with_one.int_cast_of_nat n

end int
