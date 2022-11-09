/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import algebra.field.defs
import algebra.group_with_zero.power

/-!
# Results about powers in fields or division rings.

This file exists to ensure we can define `field` with minimal imports,
so contains some lemmas about powers of elements which need imports
beyond those needed for the basic definition.
-/

variables {α : Type*}

section division_ring
variables [division_ring α]

@[simp] lemma zpow_bit1_neg (x : α) (n : ℤ) : (-x) ^ bit1 n = - x ^ bit1 n :=
by rw [zpow_bit1', zpow_bit1', neg_mul_neg, neg_mul_eq_mul_neg]

end division_ring
