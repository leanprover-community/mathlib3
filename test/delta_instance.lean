/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import data.set
import algebra.category.Mon.basic

def X : Type := set ℕ

instance : has_coe_to_sort X Type := set.has_coe_to_sort

@[derive ring] def T := ℤ

class binclass (T1 T2 : Type)

instance : binclass ℤ ℤ := ⟨⟩

@[derive [ring, binclass ℤ]] def U := ℤ

@[derive λ α, binclass α ℤ] def V := ℤ

-- test instance naming
example := U.ring
example := U.binclass
example := V.binclass

@[derive ring] def id_ring (α) [ring α] : Type := α

@[derive decidable_eq] def S := ℕ

@[derive decidable_eq] inductive P | a | b | c

open category_theory

-- Test that `delta_instance` works in the presence of universe metavariables.
attribute [derive large_category] Mon

-- test deriving instances on function types
@[derive monad]
meta def my_tactic : Type → Type :=
tactic
