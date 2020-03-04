/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/

import control.uliftable
import system.random
import system.random.basic

/-!
# Gen Monad

This monad is used to formulate randomized computations with a parameter
to specify the desired size of the result.

This is a port of the Haskell QuickCheck library.

## Main definitions
  * `gen` monad

## Local notation

 * `i .. j` : `Icc i j`, the set of values between `i` and `j` inclusively;

## Tags

random testing

## References

  * https://hackage.haskell.org/package/QuickCheck

-/

universes u v

/-- Monad to generate random examples to test properties with.
It has a `nat` parameter so that the caller can decide on the
size of the examples -/
@[reducible]
def gen (α : Type u) := reader_t (ulift ℕ) rand α

instance : monad gen :=
infer_instance_as $ monad $ reader_t (ulift ℕ) rand

instance : is_lawful_monad gen :=
infer_instance_as $ is_lawful_monad $ reader_t (ulift ℕ) rand

variable (α : Type u)

local infix ` .. `:41 := set.Icc

-- open rand (assumption_or_dec_trivial)

/-- execute a `gen` inside the `io` monad using `i` as the example
size and creating a fresh random number generator -/
def io.run_gen {α} (x : gen α) (i : ℕ) : io α :=
io.run_rand (x.run ⟨i⟩)

namespace gen

section rand

variables [preorder α]

/-- lift `random.random` to the `gen` monad -/
def choose_any [random α] : gen α :=
⟨ λ _, rand.random α ⟩

variables {α}

/-- lift `random.random_r` to the `gen` monad -/
def choose [bounded_random α] (x y : α) (p : x ≤ y) : gen (x .. y) :=
⟨ λ _, rand.random_r x y p ⟩

end rand

open nat (hiding choose)

/-- generate a `nat` example between `x` and `y` -/
def choose_nat (x y : ℕ) (p : x ≤ y) : gen (x .. y) :=
choose x y p

open nat

instance : uliftable gen.{u} gen.{v} :=
reader_t.uliftable' (equiv.ulift.trans equiv.ulift.symm)

instance : has_orelse gen.{u} :=
⟨ λ α x y, do
  b ← uliftable.up $ choose_any bool,
  if b.down then x else y ⟩

variable {α}

/-- Get access to the size parameter of the `gen` monad. For
reasons of universe polymorphism, it is specified in
continuation passing style. -/
def sized (cmd : ℕ → gen α) : gen α :=
⟨ λ ⟨sz⟩, reader_t.run (cmd sz) ⟨sz⟩ ⟩

/-- create `n` examples using `cmd` -/
def vector_of : ∀ (n : ℕ) (cmd : gen α), gen (vector α n)
| 0 _ := return vector.nil
| (succ n) cmd := vector.cons <$> cmd <*> vector_of n cmd

/-- create a list of examples using `cmd`. The size is controlled
by the size parameter of `gen` -/
def list_of (cmd : gen α) : gen (list α) :=
sized $ λ sz, do
do ⟨ n ⟩ ← uliftable.up $ choose_nat 0 (sz + 1) dec_trivial,
   v ← vector_of n.val cmd,
   return v.to_list

open ulift

/-- given a list of example generators, choose one to create an example -/
def one_of (xs : list (gen α)) (pos : fact $ 0 < xs.length) : gen α := do
n ← uliftable.up $ choose_any (fin xs.length),
list.nth_le xs (down n).val (down n).is_lt

end gen
