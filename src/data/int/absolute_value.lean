/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import algebra.order.absolute_value
import algebra.algebra.basic
import data.int.cast
import group_theory.group_action.units

/-!
# Absolute values and the integers

This file contains some results on absolute values applied to integers.

## Main results

 * `absolute_value.map_units_int`: an absolute value sends all units of `ℤ` to `1`
-/

variables {R S : Type*} [ring R] [linear_ordered_comm_ring S]

@[simp]
lemma absolute_value.map_units_int (abv : absolute_value ℤ S) (x : units ℤ) :
  abv x = 1 :=
by rcases int.units_eq_one_or x with (rfl | rfl); simp

@[simp]
lemma absolute_value.map_units_int_cast [nontrivial R] (abv : absolute_value R S) (x : units ℤ) :
  abv ((x : ℤ) : R) = 1 :=
by rcases int.units_eq_one_or x with (rfl | rfl); simp

@[simp]
lemma absolute_value.map_units_int_smul (abv : absolute_value R S) (x : units ℤ) (y : R) :
  abv (x • y) = abv y :=
by rcases int.units_eq_one_or x with (rfl | rfl); simp
