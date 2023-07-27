/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fintype.pi
import logic.equiv.array

/-!
# `array n α` is a fintype when `α` is.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*}

instance d_array.fintype {n : ℕ} {α : fin n → Type*}
  [∀ n, fintype (α n)] : fintype (d_array n α) :=
fintype.of_equiv _ (equiv.d_array_equiv_fin _).symm

instance array.fintype {n : ℕ} {α : Type*} [fintype α] : fintype (array n α) :=
d_array.fintype
