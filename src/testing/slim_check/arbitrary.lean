/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import data.lazy_list
import data.lazy_list2
import data.tree
import testing.slim_check.gen

/-!
# Arbitrary Class

This class permits the creation of arbitrary values of a given type
controlling the size of those values using the `gen` monad`. It also
helps minimize examples by creating smaller versions of given values.

When testing a proposition like `∀ n : ℕ, prime n → n ≤ 100`,
`slim_check` requires that `ℕ` have an instance of `arbitrary` and for
`prime n` to be decidable.  `slim_check` will then use the instance of
`arbitrary` to generate small examples of ℕ and progressively increase
in size. For each example `n`, `prime n` is tested. If it is false,
the example will be rejected (not a test success nor a failure) and
`slim_check` will move on to other examples. If `prime n` is true, `n
≤ 100` will be tested. If it is false, `n` is a counter-example of `∀
n : ℕ, prime n → n ≤ 100` and the test fails. If `n ≤ 100` is true,
the test passes and `slim_check` moves on to trying more examples.



This is a port of the Haskell QuickCheck library.

## Main definitions
  * `arbitrary` class

## Tags

random testing

## References

  * https://hackage.haskell.org/package/QuickCheck

-/
universes u

def lazy_list.init {α} : lazy_list α → lazy_list α
| lazy_list.nil := lazy_list.nil
| (lazy_list.cons x xs) :=
  let xs' := xs () in
  match xs' with
  | lazy_list.nil := lazy_list.nil
  | (lazy_list.cons _ _) := lazy_list.cons x (lazy_list.init xs')
  end

namespace slim_check

variables (α : Type u)

/-- `arbitrary α` provides ways of creating examples of type `α`,
and given such an example `x : α`, gives us a way to shrink it
and find simpler examples.  -/
class arbitrary :=
(arby : gen α)
(shrink : α → lazy_list α)

export arbitrary (arby shrink)

open nat

/-- implementation of `arbitrary nat` -/
def nat.shrink' : ℕ → list ℕ → list ℕ
| n ls :=
if h : n ≤ 0
  then ls
  else
    have 1 * n / 2 < n,
      from nat.div_lt_of_lt_mul (nat.mul_lt_mul_of_pos_right (by norm_num) (lt_of_not_ge h)),
    have n / 2 < n, by simpa,
    let m := n / 2 in
    nat.shrink' m (m :: ls)

/-- implementation of `arbitrary nat` -/
def nat.shrink (n : ℕ) : list ℕ :=
nat.shrink' n []

instance arbitrary_nat : arbitrary ℕ :=
{ arby := sized $ λ sz, fin.val <$> choose_any (fin $ succ (sz^3)),
  shrink := lazy_list.of_list ∘ nat.shrink }

/-- implementation of `arbitrary int` -/
def int.shrink' : ℕ → list ℤ → list ℤ
| n ls :=
if h : 0 < n
  then
    have n / 2 < n, from div_lt_self h (by norm_num),
    let m := n / 2 in
    int.shrink' m (m :: -↑m :: ls)
  else ls

/-- implementation of `arbitrary int` -/
def int.shrink (i : ℤ) : list ℤ :=
int.shrink' (int.nat_abs i) []

instance arbitrary_int : arbitrary ℤ :=
{ arby := sized $ λ sz,
       let k := sz^5 in
       (λ n : fin _, n.val - int.of_nat (k / 2) ) <$> choose_any (fin $ succ k),
  shrink := lazy_list.of_list ∘ int.shrink   }

variables {α}

def interleave {α} : lazy_list α → lazy_list α → lazy_list α
| lazy_list.nil xs := xs
| a@(lazy_list.cons x xs) lazy_list.nil := a
| (lazy_list.cons x xs) (lazy_list.cons y ys) :=
  lazy_list.cons x (lazy_list.cons y (interleave (xs ()) (ys ())))

def interleave_all {α} : list (lazy_list α) → lazy_list α
| [] := lazy_list.nil
| (x :: xs) := interleave x (interleave_all xs)

def interleave_all' {α} : list (lazy_list α) → lazy_list α :=
lazy_list.init ∘ interleave_all

def lseq {α β γ} (f : α → β → γ) : lazy_list α → lazy_list β → lazy_list γ
| lazy_list.nil xs := lazy_list.nil
| a@(lazy_list.cons x xs) lazy_list.nil := lazy_list.nil
| (lazy_list.cons x xs) ys := interleave (ys.map $ f x) (lseq (xs ()) ys)

/-- implementation of `arbitrary (list α)` -/
def list.shrink' (shrink_a : α → lazy_list α) : list α → lazy_list (list α)
| [] := lazy_list.nil
| (x :: xs) :=
  let ys := list.shrink' xs in
  interleave ys $ lseq (::) ((shrink_a x).append (lazy_list.singleton x)) (lazy_list.cons [] ys)

/-- implementation of `arbitrary (list α)` -/
def list.shrink_with (shrink_a : α → lazy_list α) (xs : list α) : lazy_list (list α) :=
(list.shrink' shrink_a xs).init

instance arbitrary_list [arbitrary α] : arbitrary (list α) :=
{ arby := list_of (arby α),
  shrink := list.shrink_with shrink  }

instance arbitrary_prop : arbitrary Prop :=
{ arby := do { x ← choose_any bool,
               return ↑x },
  shrink := λ _, lazy_list.nil }

/-- implementation of `arbitrary (tree α)` -/
def tree.arby (arby : gen α) : ℕ → gen (tree α) | n :=
if h : n > 0
then have n / 2 < n, from div_lt_self h (by norm_num),
     tree.node <$> arby <*> tree.arby (n / 2) <*> tree.arby (n / 2)
else pure tree.nil

/-- Interleave all the elements of a list but omit the last element of the
resulting list. -/
def interleave_all' {α} : list (lazy_list α) → lazy_list α :=
lazy_list.init ∘ interleave_all

/-- implementation of `arbitrary (tree α)` -/
def tree.shrink_with (shrink_a : α → lazy_list α) : tree α → lazy_list (tree α)
| tree.nil := lazy_list.nil
| (tree.node x t₀ t₁) := interleave_all' [(tree.shrink_with t₀).append (lazy_list.singleton t₀),
                                          (tree.shrink_with t₁).append (lazy_list.singleton t₁),
                                          lseq id (lseq tree.node (shrink_a x) (tree.shrink_with t₀)) (tree.shrink_with t₁) ]


instance arbitrary_tree [arbitrary α] : arbitrary (tree α) :=
{ arby := sized $ tree.arby (arby α),
  shrink := tree.shrink_with shrink }

end slim_check
