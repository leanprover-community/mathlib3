/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fintype.pi
import data.sym.basic

/-!
# `vector α n` and `sym α n` are fintypes when `α` is.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*}

instance vector.fintype [fintype α] {n : ℕ} : fintype (vector α n) :=
fintype.of_equiv _ (equiv.vector_equiv_fin _ _).symm

instance [decidable_eq α] [fintype α] {n : ℕ} : fintype (sym.sym' α n) :=
quotient.fintype _

instance [decidable_eq α] [fintype α] {n : ℕ} : fintype (sym α n) :=
fintype.of_equiv _ sym.sym_equiv_sym'.symm
