/-
Copyright (c) 2020 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers
-/
import .profunctor_optic

open control.optic
open control.profunctor

variables {A B S T : Type}

variable {n: ℕ}
open vector

def vector.grate : grate A B (vector A n) (vector B n) :=
grate.mk $ λ f, vector.of_fn $ λ i, f $ λ va, vector.nth va i
instance [has_repr A] : has_repr (vector A n) := ⟨λ x, repr $ x.to_list⟩

def vector.iota (n : ℕ) : vector ℕ n := @vector.of_fn nat n $ λ i, i.val

-- #eval zip_with_of_2 vector.grate (+) (vector.iota 100) (vector.iota _)
