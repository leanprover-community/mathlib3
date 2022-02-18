/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.nat.cast.defs

/-!
# Cast of integers

This file defines the *canonical* homomorphism from the integers into a type `α` with `0`,
`1`, `+` and `-` (typically a `ring`).

## Main declarations

* `cast`: Canonical homomorphism `ℤ → α` where `α` has a `0`, `1`, `+` and `-`.
* `cast_add_hom`: `cast` bundled as an `add_monoid_hom`.
* `cast_ring_hom`: `cast` bundled as a `ring_hom`.

## Implementation note

Setting up the coercions priorities is tricky. See Note [coercion into rings].
-/

universes u
set_option old_structure_cmd true

/-- Canonical homomorphism from the integers to any ring(-like) structure `α` -/
protected def int.cast_def {α : Type u} [add_monoid_with_one α] [has_neg α] : ℤ → α
| (n : ℕ) := n
| -[1+ n] := -(n+1 : ℕ)

@[protect_proj]
class add_group_with_one (α : Type u) extends add_group α, add_monoid_with_one α :=
(int_cast : ℤ → α := int.cast_def)
(int_cast_of_nat : ∀ n : ℕ, int_cast n = (n : α) . control_laws_tac)
(int_cast_neg_succ_of_nat : ∀ n : ℕ, int_cast (-(n+1 : ℕ)) = -((n+1 : ℕ) : α) . control_laws_tac)

@[protect_proj]
class add_comm_group_with_one (α : Type u) extends add_comm_group α, add_group_with_one α

namespace nat
variables {α : Type u} [add_group_with_one α]

@[simp, norm_cast] theorem cast_sub {m n} (h : m ≤ n) : ((n - m : ℕ) : α) = n - m :=
eq_sub_of_add_eq $ by rw [← cast_add, nat.sub_add_cancel h]

@[simp, norm_cast] theorem cast_pred : ∀ {n}, 0 < n → ((n - 1 : ℕ) : α) = n - 1
| 0 h := by cases h
| (n+1) h := by rw [cast_succ, add_sub_cancel]; refl

end nat

open nat

namespace int
variables {α : Type u} [add_group_with_one α]

/-- Canonical homomorphism from the integers to any ring(-like) structure `α` -/
protected def cast (i : ℤ) : α := add_group_with_one.int_cast i

-- see Note [coercion into rings]
@[priority 900] instance cast_coe : has_coe_t ℤ α := ⟨int.cast⟩

@[simp] theorem cast_of_nat (n : ℕ) : (of_nat n : α) = n := add_group_with_one.int_cast_of_nat n
@[simp] theorem cast_neg_succ_of_nat (n : ℕ) : (-[1+ n] : α) = -(n + 1 : ℕ) :=
add_group_with_one.int_cast_neg_succ_of_nat n

@[simp, norm_cast] theorem cast_zero : ((0 : ℤ) : α) = 0 := (cast_of_nat 0).trans nat.cast_zero

@[simp, norm_cast] theorem cast_coe_nat (n : ℕ) : ((n : ℤ) : α) = n := cast_of_nat _

@[simp, norm_cast] theorem cast_one : ((1 : ℤ) : α) = 1 :=
show (((1 : ℕ) : ℤ) : α) = 1, by simp

@[simp, norm_cast] theorem cast_neg : ∀ n, ((-n : ℤ) : α) = -n
| (0 : ℕ) := by erw [cast_zero, neg_zero]
| (n + 1 : ℕ) := by erw [cast_of_nat, cast_neg_succ_of_nat]; refl
| -[1+ n] := by erw [cast_of_nat, cast_neg_succ_of_nat, neg_neg]

@[simp] theorem cast_sub_nat_nat (m n) :
  ((int.sub_nat_nat m n : ℤ) : α) = m - n :=
begin
  unfold sub_nat_nat, cases e : n - m,
  { simp only [sub_nat_nat, cast_of_nat], simp [e, nat.le_of_sub_eq_zero e] },
  { rw [sub_nat_nat, cast_neg_succ_of_nat, nat.add_one, ← e,
        nat.cast_sub $ _root_.le_of_lt $ nat.lt_of_sub_eq_succ e, neg_sub] },
end

lemma neg_of_nat_eq (n : ℕ) : neg_of_nat n = -(n : ℤ) := by cases n; refl

@[simp] theorem cast_neg_of_nat (n : ℕ) : ((neg_of_nat n : ℤ) : α) = -n :=
by simp [neg_of_nat_eq]

@[simp, norm_cast] theorem cast_add : ∀ m n, ((m + n : ℤ) : α) = m + n
| (m : ℕ) (n : ℕ) := by simp [← int.coe_nat_add]
| (m : ℕ) -[1+ n] := by erw [cast_sub_nat_nat, cast_coe_nat, cast_neg_succ_of_nat, sub_eq_add_neg]
| -[1+ m] (n : ℕ) := by erw [cast_sub_nat_nat, cast_coe_nat, cast_neg_succ_of_nat,
  sub_eq_iff_eq_add, add_assoc, eq_neg_add_iff_add_eq, ← nat.cast_add, ← nat.cast_add, nat.add_comm]
| -[1+ m] -[1+ n] := show (-[1+ m + n + 1] : α) = _,
  by rw [cast_neg_succ_of_nat, cast_neg_succ_of_nat, cast_neg_succ_of_nat, ← neg_add_rev,
    ← nat.cast_add, nat.add_right_comm m n 1, nat.add_assoc, nat.add_comm]

@[simp, norm_cast] theorem cast_sub (m n) : ((m - n : ℤ) : α) = m - n :=
by simp [int.sub_eq_add_neg, sub_eq_add_neg]

@[simp, norm_cast]
theorem coe_nat_bit0 (n : ℕ) : (↑(bit0 n) : ℤ) = bit0 ↑n := rfl

@[simp, norm_cast]
theorem coe_nat_bit1 (n : ℕ) : (↑(bit1 n) : ℤ) = bit1 ↑n := rfl

@[simp, norm_cast] theorem cast_bit0 (n : ℤ) : ((bit0 n : ℤ) : α) = bit0 n :=
cast_add _ _

@[simp, norm_cast] theorem cast_bit1 (n : ℤ) : ((bit1 n : ℤ) : α) = bit1 n :=
by rw [bit1, cast_add, cast_one, cast_bit0]; refl

lemma cast_two : ((2 : ℤ) : α) = 2 := by norm_cast

end int
