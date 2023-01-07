/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import data.int.cast.defs
import algebra.group.basic

/-!
# Cast of integers (additional theorems)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`int.cast`).

There is also `data.int.cast.lemmas`,
which includes lemmas stated in terms of algebraic homomorphisms,
and results involving the order structure of `ℤ`.

By contrast, this file's only import beyond `data.int.cast.defs` is `algebra.group.basic`.
-/

universes u

namespace nat
variables {R : Type u} [add_group_with_one R]

@[simp, norm_cast] theorem cast_sub {m n} (h : m ≤ n) : ((n - m : ℕ) : R) = n - m :=
eq_sub_of_add_eq $ by rw [← cast_add, nat.sub_add_cancel h]

@[simp, norm_cast] theorem cast_pred : ∀ {n}, 0 < n → ((n - 1 : ℕ) : R) = n - 1
| 0 h := by cases h
| (n+1) h := by rw [cast_succ, add_sub_cancel]; refl

end nat

open nat

namespace int
variables {R : Type u} [add_group_with_one R]

@[simp] theorem cast_neg_succ_of_nat (n : ℕ) : (-[1+ n] : R) = -(n + 1 : ℕ) :=
add_group_with_one.int_cast_neg_succ_of_nat n

@[simp, norm_cast] theorem cast_zero : ((0 : ℤ) : R) = 0 := (cast_of_nat 0).trans nat.cast_zero

@[simp, norm_cast] theorem cast_coe_nat (n : ℕ) : ((n : ℤ) : R) = n := cast_of_nat _

@[simp, norm_cast] theorem cast_one : ((1 : ℤ) : R) = 1 :=
show (((1 : ℕ) : ℤ) : R) = 1, by simp

@[simp, norm_cast] theorem cast_neg : ∀ n, ((-n : ℤ) : R) = -n
| (0 : ℕ) := by erw [cast_zero, neg_zero]
| (n + 1 : ℕ) := by erw [cast_of_nat, cast_neg_succ_of_nat]; refl
| -[1+ n] := by erw [cast_of_nat, cast_neg_succ_of_nat, neg_neg]

@[simp] theorem cast_sub_nat_nat (m n) :
  ((int.sub_nat_nat m n : ℤ) : R) = m - n :=
begin
  unfold sub_nat_nat, cases e : n - m,
  { simp only [sub_nat_nat, cast_of_nat], simp [e, nat.le_of_sub_eq_zero e] },
  { rw [sub_nat_nat, cast_neg_succ_of_nat, nat.add_one, ← e,
        nat.cast_sub $ _root_.le_of_lt $ nat.lt_of_sub_eq_succ e, neg_sub] },
end

lemma neg_of_nat_eq (n : ℕ) : neg_of_nat n = -(n : ℤ) := by cases n; refl

@[simp] theorem cast_neg_of_nat (n : ℕ) : ((neg_of_nat n : ℤ) : R) = -n :=
by simp [neg_of_nat_eq]

@[simp, norm_cast] theorem cast_add : ∀ m n, ((m + n : ℤ) : R) = m + n
| (m : ℕ) (n : ℕ) := by simp [← int.coe_nat_add]
| (m : ℕ) -[1+ n] := by erw [cast_sub_nat_nat, cast_coe_nat, cast_neg_succ_of_nat, sub_eq_add_neg]
| -[1+ m] (n : ℕ) := by erw [cast_sub_nat_nat, cast_coe_nat, cast_neg_succ_of_nat,
  sub_eq_iff_eq_add, add_assoc, eq_neg_add_iff_add_eq, ← nat.cast_add, ← nat.cast_add, nat.add_comm]
| -[1+ m] -[1+ n] := show (-[1+ m + n + 1] : R) = _,
  by rw [cast_neg_succ_of_nat, cast_neg_succ_of_nat, cast_neg_succ_of_nat, ← neg_add_rev,
    ← nat.cast_add, nat.add_right_comm m n 1, nat.add_assoc, nat.add_comm]

@[simp, norm_cast] theorem cast_sub (m n) : ((m - n : ℤ) : R) = m - n :=
by simp [int.sub_eq_add_neg, sub_eq_add_neg]

@[simp, norm_cast]
theorem coe_nat_bit0 (n : ℕ) : (↑(bit0 n) : ℤ) = bit0 ↑n := rfl

@[simp, norm_cast]
theorem coe_nat_bit1 (n : ℕ) : (↑(bit1 n) : ℤ) = bit1 ↑n := rfl

@[simp, norm_cast] theorem cast_bit0 (n : ℤ) : ((bit0 n : ℤ) : R) = bit0 n :=
cast_add _ _

@[simp, norm_cast] theorem cast_bit1 (n : ℤ) : ((bit1 n : ℤ) : R) = bit1 n :=
by rw [bit1, cast_add, cast_one, cast_bit0]; refl

lemma cast_two : ((2 : ℤ) : R) = 2 := by simp

lemma cast_three : ((3 : ℤ) : R) = 3 := by simp

lemma cast_four : ((4 : ℤ) : R) = 4 := by simp

end int
