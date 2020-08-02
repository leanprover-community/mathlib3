/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/

import algebra.group_power
import control.liftable

import data.bitvec
import data.list.basic
import data.stream
import tactic.cache
import data.fin

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

## Tags

random monad io

## References

  * Similar library in Haskell: https://hackage.haskell.org/package/MonadRandom

-/

open list io applicative

universes u v w

/-- A monad to generate random objects using the generator type `g` -/
@[reducible]
def rand_g (g : Type) := state (ulift g)
/-- A monad to generate random objects using the generator type `std_gen` -/
@[reducible]
def rand := rand_g std_gen

instance (g : Type) : liftable (rand_g.{u} g) (rand_g.{v} g) :=
@state_t.liftable' _ _ _ _ _ (equiv.ulift.trans.{u u u u u} equiv.ulift.symm)

open ulift (hiding inhabited)

/-- Generate one more `ℕ` -/
def random.next {gen : Type} [random_gen gen] : rand_g gen ℕ :=
⟨ prod.map id up ∘ random_gen.next ∘ down ⟩

/-- `range i j` is a number between `i` and `j` inclusively -/
@[nolint has_inhabited_instance]
def range {α : Type u} [has_le α] (i j : α) :=
{ x : α // i ≤ x ∧ x ≤ j }

infix ` .. `:41 := range

open stream

/-- `random α` gives us machinery to generate values of type `α` -/
class random (α : Type u) extends has_le α :=
(random [] : Π (g : Type) [random_gen g], rand_g g α)
(random_r : Π g [random_gen g] (x y : α),
              x ≤ y →
              rand_g g (x .. y))
(random_series [] : Π (g : Type) [random_gen g], g → stream α :=
by { intros, resetI,
     exact corec prod.fst ((random g).run ∘ prod.snd) ( (random g).run ⟨ a ⟩ ) } )
(random_series_r : Π (g : Type) [random_gen g] (x y : α)
                        (h : x ≤ y),
                        g →
                        stream (x .. y) :=
by { introsI,
     exact corec prod.fst ((random_r g x y h).run ∘ prod.snd) ((random_r g x y h).run ⟨ a ⟩) } )

/-- is 2^31; multiplying by it shifts a number left by 31 bits,
dividing by it shifts it right by 31 bits -/
def shift_31l : ℕ :=
by apply_normed 2^31

namespace tactic.interactive

/-- Some functions require a non-empty range as a parameter. This
tactic checks that the range is non-empty -/
meta def check_range : tactic unit :=
assumption <|> do
`[apply of_as_true, trivial]

end tactic.interactive

export tactic.interactive (check_range)

namespace io

private def accum_char (w : ℕ) (c : char) : ℕ :=
c.to_nat + 256 * w

/-- create and a seed a random number generator -/
def mk_generator : io std_gen := do
seed ← io.rand 0 shift_31l,
return $ mk_std_gen seed

variables {α : Type}

/-- run `cmd` using a randomly seeded random number generator -/
def run_rand (cmd : _root_.rand α) : io α :=
do g ← io.mk_generator,
   return $ (cmd.run ⟨g⟩).1

variable [random α]

/-- randomly generate a value of type α -/
def random : io α :=
io.run_rand (random.random α _)

/-- randomly generate a value of type α between `x` and `y` -/
def random_r (x y : α) (p : x ≤ y . check_range) : io (x .. y) :=
io.run_rand (random.random_r _ x y p)

/-- randomly generate an infinite series of value of type α -/
def random_series : io (stream α) := do
g ← io.mk_generator,
return $ random.random_series _ _ g

/-- randomly generate an infinite series of value of type α between `x` and `y` -/
def random_series_r (x y : α) (h : x ≤ y . check_range) : io (stream $ x .. y) := do
g ← io.mk_generator,
return $ random.random_series_r _ x y h g

end io

namespace tactic.interactive

/-- create a seeded random number generator in the `tactic` monad -/
meta def mk_generator : tactic std_gen := do
tactic.unsafe_run_io @io.mk_generator

/-- run `cmd` using the a randomly seeded random number generator
in the tactic monad -/
meta def run_rand {α : Type u} (cmd : rand α) : tactic α := do
⟨g⟩ ← tactic.up mk_generator,
return (cmd.run ⟨g⟩).1

section random

variables {α : Type u}
variable [random α]

/-- use `random` in the `tactic` monad -/
meta def random : tactic α :=
run_rand (_root_.random.random _ _)

/-- use `random_r` in the `tactic` monad -/
meta def random_r (x y : α) (p : x ≤ y . check_range) : tactic (x .. y) :=
run_rand (random.random_r _ x y p)

/-- use `random_series` in the `tactic` monad -/
meta def random_series : tactic (stream α) := do
⟨g⟩ ← tactic.up mk_generator,
return $ random.random_series _ std_gen g

/-- use `random_series_r` in the `tactic` monad -/
meta def random_series_r (x y : α) (h : x ≤ y . check_range) : tactic (stream $ x .. y) := do
⟨g⟩ ← tactic.up mk_generator,
return $ random.random_series_r std_gen x y h g

end random

end tactic.interactive

instance : preorder bool :=
{ le := λ p q, p → q,
  le_refl := by { introv h, apply h },
  le_trans := by { introv ha hb h, apply hb, apply ha h } }

namespace bool

/-- Make `i` into an element of the interval `x .. y` if feasible
and return an arbitrary element of `x .. y` otherwise -/
def coerce (x y : bool) (p : x ≤ y) (i : bool) : x .. y := do
  if hx : x ≤ i ∧ i ≤ y
  then ⟨ i, hx ⟩
  else ⟨ x , le_refl x , p ⟩

open ulift (hiding inhabited)
variables {gen : Type} [random_gen gen]

/-- generate a randomly generated boolean value -/
protected def get_random : rand_g gen bool :=
⟨ prod.map id up ∘ @rand_bool gen _ ∘ down ⟩

/-- generator for a series of bits -/
@[derive inhabited]
structure bool_generator (g : Type) :=
(next : bool)
(queue : ℕ × ℕ)
(gen : g)

/-- create a `bool_generator` from `g` -/
protected def first (g : gen) : bool_generator gen  :=
let (r,g') := random_gen.next g in
{ next := r % 2 = 1,
  queue := (r / 2,30),
  gen := g' }

/-- get the next bit from a `bool_generator` -/
protected def next : bool_generator gen → bool_generator gen
| ⟨_,(_,0),g⟩ := bool.first g
| ⟨_,(n,k),g⟩ := ⟨(n%2 = 1),(n/2,k-1),g⟩

/-- generate an infinite series of states of a random boolean generator -/
protected def random_series_aux (g : gen) : stream (bool_generator gen) :=
stream.iterate bool.next (bool.first g)

/-- generate an infinite series of bits -/
def random_series (g : gen) : stream bool :=
stream.map bool.bool_generator.next $ bool.random_series_aux g

end bool

instance : random bool :=
{ to_has_le := by apply_instance,
  random   := λ g, @bool.get_random _,
  random_r := λ g _inst x y p, bool.coerce _ _ p <$> (@bool.get_random g _inst),
  random_series   := @bool.random_series,
  random_series_r := λ gen _inst x y p g, stream.map (bool.coerce _ _ p) $ @bool.random_series _ _inst g }

instance (n : ℕ) : preorder (bitvec n) :=
{ le := λ x y, x.to_nat ≤ y.to_nat,
  le_refl  := by { introv, apply nat.le_refl },
  le_trans := by { introv ha hb, apply nat.le_trans ha hb } }

lemma bitvec.le_def {n : ℕ} (x y : bitvec n) :
  x ≤ y ↔ x.to_nat ≤ y.to_nat :=
by refl

open nat (succ one_add mod_eq_of_lt zero_lt_succ add_one succ_le_succ)

namespace stream

variable {α : Type u}

open list (length) stream (approx)

lemma length_approx :
  ∀ (s : stream α) (n : ℕ), length (approx n s) = n
| s 0 := rfl
| s (succ n) := by simp [approx,length,one_add,length_approx]

end stream

variables {gen : Type} [random_gen gen]

/-- generate a random bit vector of length `n` -/
def bitvec.random (n : ℕ) : rand_g gen (bitvec n) :=
⟨ λ ⟨ g ⟩,
let r := bool.random_series_aux g,
    v := map bool.bool_generator.next $ stream.approx n r in
have Hv : length v = n,
     by { simp [stream.length_approx _ _], },
⟨ ⟨ v, Hv ⟩ , ⟨ (r.nth $ succ n).gen ⟩ ⟩ ⟩

section coerce

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
  { apply add_lt_add_left, simp [add_comm 1],
    apply nat.mod_lt,
    apply zero_lt_succ },
  { rw [← add_assoc,← nat.add_sub_assoc P',nat.add_sub_cancel_left,add_one],
    clear P' i',
    cases y with y Hy,
    unfold bitvec.to_nat vector.to_list subtype.val bitvec.bits_to_nat,
    rw [← reverse_reverse y, foldl_reverse,← Hy,← length_reverse],
    generalize : reverse y = z,
    clear x' x y' Hy y n,
    induction z with x xs,
    { rw [list.length,list.foldr,nat.pow] },
    { simp [foldr,length,one_add,pow_succ,flip,bitvec.add_lsb],
      transitivity succ (
       (foldr (λ (b : bool) (a : ℕ), a + a + cond b 1 0) 0 xs +
          foldr (λ (b : bool) (a : ℕ), a + a + cond b 1 0) 0 xs) + 1),
      { apply succ_le_succ, apply add_le_add_left,
        cases x, apply nat.zero_le, refl, },
      { simp!,
        transitivity (foldr (λ (b : bool) (a : ℕ), a + a + cond b 1 0) 0 xs + 1) * 2,
        { simp [mul_comm _ 2,two_mul], ring },
        apply nat.mul_le_mul_right,
        simpa [flip,bitvec.add_lsb] using z_ih } }, },
end
end coerce

open nat

/-- Use `i` to generate an element of the interval `x .. y` -/
protected def bitvec.coerce {n : ℕ} (x y : bitvec n) (P : x ≤ y)
  (i : bitvec n) :
  (x .. y) :=
let x' := x.to_nat,
    y' := y.to_nat,
    i' := i.to_nat,
    r := i' % (y' - x' + 1) + x' in
have Hx : x ≤ bitvec.of_nat n r,
  begin
    unfold_locals r,
    simp [bitvec.le_def,bitvec.to_nat_of_nat],
    rw [mod_eq_of_lt],
    { apply nat.le_add_left },
    unfold_locals x' y' i',
    apply bitvec.interval_fits_in_word_size,
    apply P
  end,
have Hy : bitvec.of_nat n r ≤ y,
  begin
    unfold_locals r,
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
    simp, apply bitvec.interval_fits_in_word_size P,
  end,
⟨ bitvec.of_nat _ r , Hx , Hy ⟩

/-- generate an infinite series of bitvectors -/
protected def bitvec.random_series (n : ℕ) (g : gen) : stream (bitvec n) :=
stream.corec
(λ s, ⟨ stream.approx n s, stream.length_approx _ _ ⟩)
(stream.drop n)
(@random.random_series bool _ gen _ g)

instance random_bitvec (n : ℕ) : random (bitvec n) :=
{ to_has_le := by apply_instance,
  random := λ _ inst, @bitvec.random _ inst n,
  random_r := λ _ inst x y p, bitvec.coerce _ _ p <$> @bitvec.random _ inst n,
  random_series := λ _ inst, @bitvec.random_series _ inst n,
  random_series_r := λ _ inst x y p g, bitvec.coerce _ _ p ∘ @bitvec.random_series _ inst n g }

open nat

lemma div_two_round_up
  (x : ℕ)
  (h₀ : 1 < x)
: (x + 1) / 2 < x :=
begin
  rw [div_lt_iff_lt_mul,norm_num.mul_bit0,mul_one,bit0],
  apply add_lt_add_left, apply h₀,
  apply of_as_true, trivial
end

/-- `word_size n` gives us the number of bits required to represent `n` -/
def word_size : ℕ → ℕ
| x :=
if h : 1 < x then
  have (x + 1) / 2 < x,
    from div_two_round_up _ h,
  succ $ word_size ((x + 1) / 2)
else 0

local infix ^ := nat.pow

lemma word_size_le_two_pow (n : ℕ)
: n ≤ 2^word_size n :=
begin
  apply nat.strong_induction_on n,
  clear n, intros n IH,
  by_cases h : 1 < n,
  { rw [word_size,if_pos h,nat.pow],
    cases n with n, { cases not_lt_zero _ h },
    change n < _,
    rw ← @div_lt_iff_lt_mul _ _ 2 dec_trivial,
    have h' := div_two_round_up (succ n) h,
    specialize IH ((succ n + 1) / 2) h', clear h h',
    rw [succ_add,← add_succ] at *,
    simp only [-succ_pos', add_zero] at *,
    have h : (n + 2 * 1) / 2 = n / 2 + 1 :=
       add_mul_div_left _ _ dec_trivial,
    rw [mul_one] at h,
    rw h at IH ⊢,
    apply IH },
  { rw [word_size,if_neg h,nat.pow],
    apply le_of_not_gt h }
end

namespace fin
section fin
parameter {n : ℕ}

/-- `random_aux m k` `m` words worth of random numbers and combine them
with `k` -/
protected def random_aux : ℕ → ℕ → rand_g gen (fin (succ n))
| 0 k := return $ fin.of_nat k
| (succ n) k :=
do x ← random.next,
   random_aux n $ x + (k * shift_31l)

/-- generate a `fin` randomly -/
protected def random : rand_g gen (fin (succ n)) :=
let m := word_size n / 31 + 1 in
random_aux m 0

section coerce

parameters {i' r k : ℕ}
parameters {y : fin k}

parameters {x' : ℕ}

parameters P' : x' ≤ y.val
include P'

lemma interval_fits_in_word_size : x' + i' % (1 + (y.val - x')) < k :=
begin
  apply @lt_of_lt_of_le _ _ _ (x' + (y.val - x' + 1)),
  { apply add_lt_add_left, simp,
    apply nat.mod_lt,
    rw one_add, apply zero_lt_succ },
  { rw [← add_assoc,← nat.add_sub_assoc P',nat.add_sub_cancel_left,add_one],
    apply y.is_lt }
end
end coerce


/-- Use `i` to generate an element of the interval `x .. y` -/
protected def coerce {n : ℕ} (x y : fin (succ n)) (P : x ≤ y)
  (i : fin (succ n)) : (x .. y) :=
let x' := x.val,
    i' := i.val,
    r := i' % (y.val - x' + 1) + x' in
have P' : x.val ≤ y.val,
  by { rw ← le_def, apply P },
have Hx : x ≤ fin.of_nat r,
  begin
    unfold_locals r,
    simp [fin.le_def,fin.val_of_nat_eq_mod],
    rw [mod_eq_of_lt],
    { apply nat.le_add_right },
    apply fin.interval_fits_in_word_size,
    unfold_locals x',
    rw ← fin.le_def, apply P
  end,
have Hy : fin.of_nat r ≤ y,
  begin
    unfold_locals r,
    rw [fin.le_def,fin.val_of_nat_eq_mod,mod_eq_of_lt],
    transitivity (y.val - x') + x',
    { apply add_le_add_right,
      apply le_of_lt_succ,
      rw add_one,
      apply mod_lt,
      apply zero_lt_succ },
    { transitivity x' + (y.val - x'),
      apply le_of_eq, ac_refl,
      rw [← nat.add_sub_assoc P',nat.add_sub_cancel_left], },
    simp, apply fin.interval_fits_in_word_size P',
  end,
⟨ fin.of_nat r , Hx , Hy ⟩

/-- generate an element of the interval `x .. y` -/
protected def random_r (x y : fin (succ n)) (p : x ≤ y) : rand_g gen (x .. y) :=
fin.coerce _ _ p <$> fin.random

end fin
end fin

instance fin_random (n : ℕ) : random (fin (succ n)) :=
{ to_has_le := by apply_instance,
  random := λ g, @fin.random _ g,
  random_r := λ x y p, @fin.random_r n x y p }

open nat

/-- A value of type `fin n` rather than `fin (succ n)` relying
instead on a proof that `n` is positive. -/
def random_fin_of_pos : ∀ (n : ℕ) (h : 0 < n), random (fin n)
| (succ n) _ := fin_random _
| 0 h := false.elim (not_lt_zero _ h)
