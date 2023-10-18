/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import algebra.field.defs
import algebra.group_with_zero.power
import algebra.parity

/-!
# Results about powers in fields or division rings.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file exists to ensure we can define `field` with minimal imports,
so contains some lemmas about powers of elements which need imports
beyond those needed for the basic definition.
-/

variables {α : Type*}

section division_ring
variables [division_ring α] {n : ℤ}

@[simp] lemma zpow_bit1_neg (a : α) (n : ℤ) : (-a) ^ bit1 n = - a ^ bit1 n :=
by rw [zpow_bit1', zpow_bit1', neg_mul_neg, neg_mul_eq_mul_neg]

lemma odd.neg_zpow (h : odd n) (a : α) : (-a) ^ n = - a ^ n :=
by { obtain ⟨k, rfl⟩ := h.exists_bit1, exact zpow_bit1_neg _ _ }

lemma odd.neg_one_zpow (h : odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_zpow, one_zpow]

end division_ring
