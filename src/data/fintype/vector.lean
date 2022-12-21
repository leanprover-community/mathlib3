/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fintype.pi
import data.array.lemmas
import data.sym.basic

/-!
# `vector α n` is a fintype when `α` is.
-/

variables {α : Type*}

instance d_array.fintype {n : ℕ} {α : fin n → Type*}
  [∀ n, fintype (α n)] : fintype (d_array n α) :=
fintype.of_equiv _ (equiv.d_array_equiv_fin _).symm

instance array.fintype {n : ℕ} {α : Type*} [fintype α] : fintype (array n α) :=
d_array.fintype

instance vector.fintype [fintype α] {n : ℕ} : fintype (vector α n) :=
fintype.of_equiv _ (equiv.vector_equiv_fin _ _).symm

instance [decidable_eq α] [fintype α] {n : ℕ} : fintype (sym.sym' α n) :=
quotient.fintype _

instance [decidable_eq α] [fintype α] {n : ℕ} : fintype (sym α n) :=
fintype.of_equiv _ sym.sym_equiv_sym'.symm
