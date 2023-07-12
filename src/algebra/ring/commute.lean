/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import algebra.ring.semiconj
import algebra.ring.units
import algebra.group.commute

/-!
# Semirings and rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file gives lemmas about semirings, rings and domains.
This is analogous to `algebra.group.basic`,
the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

For the definitions of semirings and rings see `algebra.ring.defs`.

-/
universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open function

namespace commute

@[simp] theorem add_right [distrib R] {a b c : R} :
  commute a b → commute a c → commute a (b + c) :=
semiconj_by.add_right

@[simp] theorem add_left [distrib R] {a b c : R} :
  commute a c → commute b c → commute (a + b) c :=
semiconj_by.add_left

lemma bit0_right [distrib R] {x y : R} (h : commute x y) : commute x (bit0 y) :=
h.add_right h

lemma bit0_left [distrib R] {x y : R} (h : commute x y) : commute (bit0 x) y :=
h.add_left h

lemma bit1_right [non_assoc_semiring R] {x y : R} (h : commute x y) : commute x (bit1 y) :=
h.bit0_right.add_right (commute.one_right x)

lemma bit1_left [non_assoc_semiring R] {x y : R} (h : commute x y) : commute (bit1 x) y :=
h.bit0_left.add_left (commute.one_left y)

/-- Representation of a difference of two squares of commuting elements as a product. -/
lemma mul_self_sub_mul_self_eq [non_unital_non_assoc_ring R] {a b : R} (h : commute a b) :
  a * a - b * b = (a + b) * (a - b) :=
by rw [add_mul, mul_sub, mul_sub, h.eq, sub_add_sub_cancel]

lemma mul_self_sub_mul_self_eq' [non_unital_non_assoc_ring R] {a b : R} (h : commute a b) :
  a * a - b * b = (a - b) * (a + b) :=
by rw [mul_add, sub_mul, sub_mul, h.eq, sub_add_sub_cancel]

lemma mul_self_eq_mul_self_iff [non_unital_non_assoc_ring R] [no_zero_divisors R] {a b : R}
  (h : commute a b) : a * a = b * b ↔ a = b ∨ a = -b :=
by rw [← sub_eq_zero, h.mul_self_sub_mul_self_eq, mul_eq_zero, or_comm, sub_eq_zero,
  add_eq_zero_iff_eq_neg]

section
variables [has_mul R] [has_distrib_neg R] {a b : R}

theorem neg_right : commute a b → commute a (- b) := semiconj_by.neg_right
@[simp] theorem neg_right_iff : commute a (-b) ↔ commute a b := semiconj_by.neg_right_iff

theorem neg_left : commute a b → commute (- a) b := semiconj_by.neg_left
@[simp] theorem neg_left_iff : commute (-a) b ↔ commute a b := semiconj_by.neg_left_iff

end

section
variables [mul_one_class R] [has_distrib_neg R] {a : R}

@[simp] theorem neg_one_right (a : R) : commute a (-1) := semiconj_by.neg_one_right a
@[simp] theorem neg_one_left (a : R): commute (-1) a := semiconj_by.neg_one_left a

end

section
variables [non_unital_non_assoc_ring R] {a b c : R}

@[simp] theorem sub_right : commute a b → commute a c → commute a (b - c) := semiconj_by.sub_right
@[simp] theorem sub_left : commute a c → commute b c → commute (a - b) c := semiconj_by.sub_left

end

end commute

/-- Representation of a difference of two squares in a commutative ring as a product. -/
theorem mul_self_sub_mul_self [comm_ring R] (a b : R) : a * a - b * b = (a + b) * (a - b) :=
(commute.all a b).mul_self_sub_mul_self_eq

lemma mul_self_sub_one [non_assoc_ring R] (a : R) : a * a - 1 = (a + 1) * (a - 1) :=
by rw [←(commute.one_right a).mul_self_sub_mul_self_eq, mul_one]

lemma mul_self_eq_mul_self_iff [comm_ring R] [no_zero_divisors R] {a b : R} :
  a * a = b * b ↔ a = b ∨ a = -b :=
(commute.all a b).mul_self_eq_mul_self_iff

lemma mul_self_eq_one_iff [non_assoc_ring R] [no_zero_divisors R] {a : R} :
  a * a = 1 ↔ a = 1 ∨ a = -1 :=
by rw [←(commute.one_right a).mul_self_eq_mul_self_iff, mul_one]

namespace units

/-- In the unit group of an integral domain, a unit is its own inverse iff the unit is one or
  one's additive inverse. -/
lemma inv_eq_self_iff [ring R] [no_zero_divisors R] (u : Rˣ) : u⁻¹ = u ↔ u = 1 ∨ u = -1 :=
begin
  rw inv_eq_iff_mul_eq_one,
  simp only [ext_iff],
  push_cast,
  exact mul_self_eq_one_iff
end

end units
