/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/

import algebra.group_power
import control.uliftable
import control.monad.basic

import data.bitvec.basic
import data.list.basic
import data.set.intervals.basic
import data.stream.basic
import data.fin

import tactic.cache
import tactic.interactive
import tactic.norm_num

import system.io
import system.random

/-!
# Rand Monad and Random Class

This module provides tools for formulating computations guided by randomness and for
defining objects that can be created randomly.

## Main definitions
  * `rand` monad for computations guided by randomness;
  * `random` class for objects that can be generated randomly;
    * `random` to generate one object;
    * `random_r` to generate one object inside a range;
    * `random_series` to generate an infinite series of objects;
    * `random_series_r` to generate an infinite series of objects inside a range;
  * `io.mk_generator` to create a new random number generator;
  * `io.run_rand` to run a randomized computation inside the `io` monad;
  * `tactic.run_rand` to run a randomized computation inside the `tactic` monad

## Local notation

 * `i .. j` : `Icc i j`, the set of values between `i` and `j` inclusively;

## Tags

random monad io

## References

  * Similar library in Haskell: https://hackage.haskell.org/package/MonadRandom

-/

open list io applicative

universes u v w

/-- A monad to generate random objects using the generator type `g` -/
@[reducible]
def rand_g (g : Type) (α : Type u) : Type u := state (ulift.{u} g) α
/-- A monad to generate random objects using the generator type `std_gen` -/
@[reducible]
def rand := rand_g std_gen

instance (g : Type) : uliftable (rand_g.{u} g) (rand_g.{v} g) :=
@state_t.uliftable' _ _ _ _ _ (equiv.ulift.trans.{u u u u u} equiv.ulift.symm)

open ulift (hiding inhabited)

/-- Generate one more `ℕ` -/
def rand_g.next {g : Type} [random_gen g] : rand_g g ℕ :=
⟨ prod.map id up ∘ random_gen.next ∘ down ⟩

local infix ` .. `:41 := set.Icc

open stream

/-- `bounded_random α` gives us machinery to generate values of type `α` between certain bounds -/
class bounded_random (α : Type u) [preorder α] :=
(random_r : Π g [random_gen g] (x y : α),
              (x ≤ y) → rand_g g (x .. y))

/-- `random α` gives us machinery to generate values of type `α` -/
class random (α : Type u) [preorder α] extends bounded_random α :=
(random [] : Π (g : Type) [random_gen g], rand_g g α)

attribute [instance, priority 100] random.to_bounded_random

/-- shift_31_left = 2^31; multiplying by it shifts the binary
representation of a number left by 31 bits, dividing by it shifts it
right by 31 bits -/
def shift_31_left : ℕ :=
by apply_normed 2^31

namespace stream

/-- Use a state monad to generate a stream through corecursion -/
def corec_state {σ α} (cmd : state σ α) (s : σ) : stream α :=
stream.corec prod.fst (cmd.run ∘ prod.snd) (cmd.run s)

end stream

namespace rand

open stream

variables (α : Type u)
variables (g : Type) [random_gen g]

/-- create a new random number generator distinct from the one stored in the state -/
def split : rand_g g g := ⟨ prod.map id up ∘ random_gen.split ∘ down ⟩

variables {g}

section random
variables [preorder α] [random α]

export random (random)

/-- re-export `random.random` -/
def random : rand_g g α :=
random.random α g

/-- generate an infinite series of random values of type `α` -/
def random_series : rand_g g (stream α) :=
do gen ← uliftable.up (split g),
   pure $ stream.corec_state (random.random α g) gen

end random

variables {α}

/-- re-export `bounded_random.random_r` -/
def random_r [preorder α] [bounded_random α] (x y : α) (h : x ≤ y) : rand_g g (x .. y) :=
bounded_random.random_r g x y h

/-- generate an infinite series of random values of type `α` between `x` and `y` -/
def random_series_r [preorder α] [bounded_random α] (x y : α) (h : x ≤ y) : rand_g g (stream (x .. y)) :=
do gen ← uliftable.up (split g),
   pure $ corec_state (bounded_random.random_r g x y h) gen

end rand

namespace io

private def accum_char (w : ℕ) (c : char) : ℕ :=
c.to_nat + 256 * w

/-- create and a seed a random number generator -/
def mk_generator : io std_gen := do
seed ← io.rand 0 shift_31_left,
return $ mk_std_gen seed

variables {α : Type}

/-- run `cmd` using a randomly seeded random number generator -/
def run_rand (cmd : _root_.rand α) : io α :=
do g ← io.mk_generator,
   return $ (cmd.run ⟨g⟩).1

section random
variables [preorder α] [random α]

/-- randomly generate a value of type α -/
def random : io α :=
io.run_rand (rand.random α)

/-- randomly generate an infinite series of value of type α -/
def random_series : io (stream α) :=
io.run_rand (rand.random_series α)

end random

section bounded_random
variables [preorder α] [bounded_random α]

/-- randomly generate a value of type α between `x` and `y` -/
def random_r (x y : α) (p : x ≤ y) : io (x .. y) :=
io.run_rand (bounded_random.random_r _ x y p)

/-- randomly generate an infinite series of value of type α between `x` and `y` -/
def random_series_r (x y : α) (h : x ≤ y) : io (stream $ x .. y) :=
io.run_rand (rand.random_series_r x y h)

end bounded_random

end io

namespace tactic

/-- create a seeded random number generator in the `tactic` monad -/
meta def mk_generator : tactic std_gen := do
tactic.unsafe_run_io @io.mk_generator

/-- run `cmd` using the a randomly seeded random number generator
in the tactic monad -/
meta def run_rand {α : Type u} (cmd : rand α) : tactic α := do
⟨g⟩ ← tactic.up mk_generator,
return (cmd.run ⟨g⟩).1

variables {α : Type u}

section bounded_random
variables [preorder α] [bounded_random α]

/-- use `random_r` in the `tactic` monad -/
meta def random_r (x y : α) (h : x ≤ y) : tactic (x .. y) :=
run_rand (rand.random_r x y h)

/-- use `random_series_r` in the `tactic` monad -/
meta def random_series_r (x y : α) (h : x ≤ y) : tactic (stream $ x .. y) :=
run_rand (rand.random_series_r x y h)

end bounded_random

section random

variables [preorder α] [random α]

/-- use `random` in the `tactic` monad -/
meta def random : tactic α :=
run_rand (rand.random α)

/-- use `random_series` in the `tactic` monad -/
meta def random_series : tactic (stream α) :=
run_rand (rand.random_series α)

end random

end tactic

namespace bool

/-- Make `i` into an element of the interval `x .. y` if feasible
and return an arbitrary element of `x .. y` otherwise -/
def fit_in_Icc (x y : bool) (p : x ≤ y) (i : bool) : x .. y := do
  if hx : x ≤ i ∧ i ≤ y
  then ⟨ i, hx ⟩
  else ⟨ x , le_refl x , p ⟩

open ulift (hiding inhabited)
variables {g : Type} [random_gen g]

/-- generate a randomly generated boolean value -/
protected def get_random : rand_g g bool :=
⟨ prod.map id up ∘ @rand_bool g _ ∘ down ⟩

end bool

instance : random bool :=
{ random   := λ g, @bool.get_random _,
  random_r := λ g _inst x y p, bool.fit_in_Icc _ _ p <$> (@bool.get_random g _inst) }

open nat (succ one_add mod_eq_of_lt zero_lt_succ add_one succ_le_succ)

namespace stream

variable {α : Type u}

open list (length) stream (approx)

lemma length_approx :
  ∀ (s : stream α) (n : ℕ), length (approx n s) = n
| s 0 := rfl
| s (succ n) := by simp [approx,length,one_add,length_approx]

end stream

variables {g : Type} [random_gen g]

/-- generate a random bit vector of length `n` -/
def bitvec.random (n : ℕ) : rand_g g (bitvec n) := do
bs ← rand.random_series bool,
pure ⟨bs.take n, bs.length_take _⟩

section fit_in_Icc

parameters {i' n : ℕ}
parameters {x y : bitvec n}

parameters P' : x.to_nat ≤ y.to_nat
include P'

local infix ^ := nat.pow

lemma bitvec.interval_fits_in_word_size :
  x.to_nat + i' % (1 + (y.to_nat - x.to_nat)) < 2^n :=
begin
  let x' := x.to_nat,
  let y' := y.to_nat,
  apply @lt_of_lt_of_le _ _ _ (x' + (y' - x' + 1)),
  { apply add_lt_add_left, simp only [add_comm _ 1],
    apply nat.mod_lt,
    simp [add_comm 1,zero_lt_succ], },
  { rw [← add_assoc,← nat.add_sub_assoc P',nat.add_sub_cancel_left,add_one],
    clear P' i',
    cases y with y Hy,
    unfold bitvec.to_nat vector.to_list subtype.val bitvec.bits_to_nat,
    rw [← reverse_reverse y, foldl_reverse,← Hy,← length_reverse],
    generalize : reverse y = z,
    clear x' x y' Hy y n,
    induction z with x xs,
    { rw [list.length,list.foldr,nat.pow] },
    { simp [foldr,length,one_add,pow_succ,flip,bitvec.add_lsb,add_comm _ 1],
      transitivity succ
       (foldr (λ (b : bool) (a : ℕ), a + a + cond b 1 0) 0 xs +
          foldr (λ (b : bool) (a : ℕ), a + a + cond b 1 0) 0 xs + 1),
      { apply succ_le_succ, apply add_le_add_left,
        cases x, apply nat.zero_le, refl, },
      { simp! only,
        rw [← nat.succ_eq_add_one,← nat.succ_add,← nat.add_succ],
        rw [mul_comm _ 2,← two_mul],
        apply nat.mul_le_mul_left,
        simpa [flip,bitvec.add_lsb] using z_ih, } }, },
end
end fit_in_Icc

open nat

/-- Use `i` to generate an element of the interval `x .. y` -/
protected def bitvec.fit_in_Icc {n : ℕ} (x y : bitvec n) (P : x ≤ y)
  (i : bitvec n) :
  (x .. y) :=
let x' := x.to_nat,
    y' := y.to_nat,
    i' := i.to_nat,
    r := i' % (y' - x' + 1) + x' in
have Hx : x ≤ bitvec.of_nat n r,
  begin
    dsimp [r],
    simp only [bitvec.le_def,bitvec.to_nat_of_nat,add_comm _ x',add_comm _ 1],
    rw [mod_eq_of_lt],
    { apply nat.le_add_right },
    dsimp [x', y', i'],
    apply bitvec.interval_fits_in_word_size,
    apply P
  end,
have Hy : bitvec.of_nat n r ≤ y,
  begin
    dsimp [r],
    rw [bitvec.le_def,bitvec.to_nat_of_nat,mod_eq_of_lt],
    transitivity (y' - x') + x',
    { apply add_le_add_right,
      apply le_of_lt_succ,
      rw ← add_one,
      apply mod_lt,
      rw add_one, apply zero_lt_succ },
    { transitivity x' + (y' - x'),
      apply le_of_eq, ac_refl,
      rw [← nat.add_sub_assoc P,nat.add_sub_cancel_left], },
    simp only [add_comm _ x',add_comm _ 1],
    apply bitvec.interval_fits_in_word_size P,
  end,
⟨ bitvec.of_nat _ r , Hx , Hy ⟩

instance random_bitvec (n : ℕ) : random (bitvec n) :=
{ random := λ _ inst, @bitvec.random _ inst n,
  random_r := λ _ inst x y p, bitvec.fit_in_Icc _ _ p <$> @bitvec.random _ inst n }

open nat

/-- `word_size n` gives us the number of bits required to represent `n` -/
def word_size (x : ℕ) : ℕ :=
log 2 x + 1

local infix ^ := nat.pow

namespace fin
section fin
parameters {n : ℕ} [fact (0 < n)]

/-- `random_aux m k` `m` words worth of random numbers and combine them
with `k` -/
protected def random_aux : ℕ → ℕ → rand_g g (fin n)
| 0 k := return $ fin.of_nat' k
| (succ n) k :=
do x ← rand_g.next,
   random_aux n $ x + (k * shift_31_left)

/-- generate a `fin` randomly -/
protected def random : rand_g g (fin n) :=
let m := word_size n / 31 + 1 in
random_aux m 0

section fit_in_Icc

parameters {i' r k : ℕ}
parameters {y : fin k}

parameters {x' : ℕ}

parameters P' : x' ≤ y.val
include P'

lemma interval_fits_in_word_size : x' + i' % (1 + (y.val - x')) < k :=
begin
  apply @lt_of_lt_of_le _ _ _ (x' + (y.val - x' + 1)),
  { apply add_lt_add_left, simp only [add_comm 1],
    apply nat.mod_lt, apply zero_lt_succ },
  { rw [← add_assoc,← nat.add_sub_assoc P',nat.add_sub_cancel_left,add_one],
    apply y.is_lt }
end

end fit_in_Icc

/-- Use `i` to generate an element of the interval `x .. y` -/
protected def fit_in_Icc {n : ℕ} (x y : fin n) (P : x ≤ y)
  (i : fin n) : (x .. y) :=
let x' := x.val,
    i' := i.val,
    r := i' % (y.val - x' + 1) + x' in
have P' : x.val ≤ y.val,
  by { rw ← le_def, apply P },
by haveI : fact (0 < n) :=  lt_of_le_of_lt (nat.zero_le x.val) x.is_lt; exact
have Hx : x ≤ fin.of_nat' r,
  begin
    dsimp [r],
    simp only [fin.le_def,fin.val_of_nat_eq_mod',add_comm _ x',add_comm _ 1],
    rw [mod_eq_of_lt],
    { apply nat.le_add_right },
    apply fin.interval_fits_in_word_size,
    dsimp [x'],
    rw ← fin.le_def, apply P
  end,
have Hy : fin.of_nat' r ≤ y,
  begin
    dsimp [r],
    rw [fin.le_def,fin.val_of_nat_eq_mod',mod_eq_of_lt],
    transitivity (y.val - x') + x',
    { apply add_le_add_right,
      apply le_of_lt_succ,
      rw add_one,
      apply mod_lt,
      apply zero_lt_succ },
    { transitivity x' + (y.val - x'),
      apply le_of_eq, ac_refl,
      rw [← nat.add_sub_assoc P',nat.add_sub_cancel_left], },
    simp only [add_comm _ x',add_comm _ 1],
    apply fin.interval_fits_in_word_size P',
  end,
⟨ fin.of_nat' r , Hx , Hy ⟩

/-- generate an element of the interval `x .. y` -/
protected def random_r (x y : fin n) (p : x ≤ y) : rand_g g (x .. y) :=
fin.fit_in_Icc _ _ p <$> fin.random

end fin
end fin

instance fin_random (n : ℕ) [fact (0 < n)] : random (fin n) :=
{ random := λ g, @fin.random _ _ g,
  random_r := λ x y p, @fin.random_r n _ x y p }

open nat

/-- A shortcut for creating a `random (fin n)` instance from
a proof that `0 < n` rather than on matching on `fin (succ n)`  -/
def random_fin_of_pos : ∀ {n : ℕ} (h : 0 < n), random (fin n)
| (succ n) _ := fin_random _
| 0 h := false.elim (not_lt_zero _ h)

instance nat_bounded_random : bounded_random ℕ :=
{ random_r := λ g inst x y hxy,
  do z ← @random.random (fin $ succ $ y - x) _ _ g inst,
     pure ⟨z.val + x, nat.le_add_left _ _,
       by rw ← nat.le_sub_right_iff_add_le hxy; apply le_of_succ_le_succ z.is_lt⟩ }
