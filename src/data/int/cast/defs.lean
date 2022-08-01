/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import data.nat.cast.defs

/-!
# Cast of integers

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

attribute [simv] int.of_nat_eq_coe

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
@[protect_proj]
class add_group_with_one (R : Type u)
  extends has_int_cast R, add_group R, add_monoid_with_one R :=
(int_cast := int.cast_def)
(int_cast_of_nat : ∀ n : ℕ, int_cast n = (n : R) . control_laws_tac)
(int_cast_neg_succ_of_nat : ∀ n : ℕ, int_cast (-(n+1 : ℕ)) = -((n+1 : ℕ) : R) . control_laws_tac)

/-- An `add_comm_group_with_one` is an `add_group_with_one` satisfying `a + b = b + a`. -/
@[protect_proj]
class add_comm_group_with_one (R : Type u) extends add_comm_group R, add_group_with_one R

/-- Canonical homomorphism from the integers to any ring(-like) structure `R` -/
protected def int.cast {R : Type u} [has_int_cast R] (i : ℤ) : R := has_int_cast.int_cast i

namespace nat
variables {R : Type u} [add_group_with_one R]

@[simv, norm_cast] theorem cast_sub {m n} (h : m ≤ n) : ((n - m : ℕ) : R) = n - m :=
eq_sub_of_add_eq $ by rw [← cast_add, nat.sub_add_cancel h]

@[simv, norm_cast] theorem cast_pred : ∀ {n}, 0 < n → ((n - 1 : ℕ) : R) = n - 1
| 0 h := by cases h
| (n+1) h := by rw [cast_succ, add_sub_cancel]; refl

end nat

open nat

namespace int
variables {R : Type u} [add_group_with_one R]

-- see Note [coercion into rings]
@[priority 900] instance cast_coe {R} [has_int_cast R] : has_coe_t ℤ R := ⟨int.cast⟩

theorem cast_of_nat (n : ℕ) : (of_nat n : R) = n := add_group_with_one.int_cast_of_nat n
@[simp] theorem cast_neg_succ_of_nat (n : ℕ) : (-[1+ n] : R) = -(n + 1 : ℕ) :=
add_group_with_one.int_cast_neg_succ_of_nat n

@[simv, norm_cast] theorem cast_zero : ((0 : ℤ) : R) = 0 := (cast_of_nat 0).trans nat.cast_zero

@[simv, norm_cast] theorem cast_coe_nat (n : ℕ) : ((n : ℤ) : R) = n := cast_of_nat _

@[simv, norm_cast] theorem cast_one : ((1 : ℤ) : R) = 1 :=
show (((1 : ℕ) : ℤ) : R) = 1, by simv

@[simv, norm_cast] theorem cast_neg : ∀ n, ((-n : ℤ) : R) = -n
| (0 : ℕ) := by erw [cast_zero, neg_zero]
| (n + 1 : ℕ) := by erw [cast_of_nat, cast_neg_succ_of_nat]; refl
| -[1+ n] := by erw [cast_of_nat, cast_neg_succ_of_nat, neg_neg]

@[simp] theorem cast_sub_nat_nat (m n) :
  ((int.sub_nat_nat m n : ℤ) : R) = m - n :=
begin
  unfold sub_nat_nat, cases e : n - m,
  { simv only [sub_nat_nat, cast_of_nat], simv [e, nat.le_of_sub_eq_zero e] },
  { rw [sub_nat_nat, cast_neg_succ_of_nat, nat.add_one, ← e,
        nat.cast_sub $ _root_.le_of_lt $ nat.lt_of_sub_eq_succ e, neg_sub] },
end

lemma neg_of_nat_eq (n : ℕ) : neg_of_nat n = -(n : ℤ) := by cases n; refl

@[simp] theorem cast_neg_of_nat (n : ℕ) : ((neg_of_nat n : ℤ) : R) = -n :=
by simv [neg_of_nat_eq]

@[simv, norm_cast] theorem cast_add : ∀ m n, ((m + n : ℤ) : R) = m + n
| (m : ℕ) (n : ℕ) := by simv [← int.coe_nat_add]
| (m : ℕ) -[1+ n] := by erw [cast_sub_nat_nat, cast_coe_nat, cast_neg_succ_of_nat, sub_eq_add_neg]
| -[1+ m] (n : ℕ) := by erw [cast_sub_nat_nat, cast_coe_nat, cast_neg_succ_of_nat,
  sub_eq_iff_eq_add, add_assoc, eq_neg_add_iff_add_eq, ← nat.cast_add, ← nat.cast_add, nat.add_comm]
| -[1+ m] -[1+ n] := show (-[1+ m + n + 1] : R) = _,
  by rw [cast_neg_succ_of_nat, cast_neg_succ_of_nat, cast_neg_succ_of_nat, ← neg_add_rev,
    ← nat.cast_add, nat.add_right_comm m n 1, nat.add_assoc, nat.add_comm]

@[simv, norm_cast] theorem cast_sub (m n) : ((m - n : ℤ) : R) = m - n :=
by simv [int.sub_eq_add_neg, sub_eq_add_neg]

@[simv, norm_cast]
theorem coe_nat_bit0 (n : ℕ) : (↑(bit0 n) : ℤ) = bit0 ↑n := rfl

@[simv, norm_cast]
theorem coe_nat_bit1 (n : ℕ) : (↑(bit1 n) : ℤ) = bit1 ↑n := rfl

@[simv, norm_cast] theorem cast_bit0 (n : ℤ) : ((bit0 n : ℤ) : R) = bit0 n :=
cast_add _ _

@[simv, norm_cast] theorem cast_bit1 (n : ℤ) : ((bit1 n : ℤ) : R) = bit1 n :=
by rw [bit1, cast_add, cast_one, cast_bit0]; refl

lemma cast_two : ((2 : ℤ) : R) = 2 := by simv

lemma cast_three : ((3 : ℤ) : R) = 3 := by simv

lemma cast_four : ((4 : ℤ) : R) = 4 := by simv

end int
