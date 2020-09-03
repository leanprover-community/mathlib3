/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import data.lazy_list
import data.lazy_list2
import data.tree
import tactic.linarith
import testing.slim_check.gen

/-!
# `sampleable` Class

This class permits the creation samples of a given type
controlling the size of those values using the `gen` monad`. It also
helps minimize examples by creating smaller versions of given values.

When testing a proposition like `∀ n : ℕ, prime n → n ≤ 100`,
`slim_check` requires that `ℕ` have an instance of `sampleable` and for
`prime n` to be decidable.  `slim_check` will then use the instance of
`sampleable` to generate small examples of ℕ and progressively increase
in size. For each example `n`, `prime n` is tested. If it is false,
the example will be rejected (not a test success nor a failure) and
`slim_check` will move on to other examples. If `prime n` is true, `n
≤ 100` will be tested. If it is false, `n` is a counter-example of `∀
n : ℕ, prime n → n ≤ 100` and the test fails. If `n ≤ 100` is true,
the test passes and `slim_check` moves on to trying more examples.


This is a port of the Haskell QuickCheck library.

## Main definitions
  * `sampleable` class

## Tags

random testing

## References

  * https://hackage.haskell.org/package/QuickCheck

-/
universes u

namespace slim_check

variables (α : Type u)

/-- `sampleable α` provides ways of creating examples of type `α`,
and given such an example `x : α`, gives us a way to shrink it
and find simpler examples.  -/
class sampleable :=
(sample [] : gen α)
(shrink : α → lazy_list α)

export sampleable (sample shrink)

open nat lazy_list

/-- Apply `f` to combine every element of the first list with every element
of the second list and interleave the resulting lists.

For instance `lseq prod.mk [1,2,3] [4,5,6]` results in

```
[(1, 4), (2, 4), (1, 5), (3, 4), (1, 6), (2, 5), (3, 5), (2, 6), (3, 6)]
```

The purpose is to take two lists of shrunken values in ascending order of size
and produce a list of combined values in roughly ascending order of size too.

If we add the samples instead with `lseq (+) [1,2,3] [1,2,3]`, we
obtain:

```
[2, 3, 3, 4, 4, 4, 5, 5, 6]
```
 -/
def lazy_list.lseq {α β γ} (f : α → β → γ) : lazy_list α → lazy_list β → lazy_list γ
| lazy_list.nil xs := lazy_list.nil
| (lazy_list.cons x xs) lazy_list.nil := lazy_list.nil
| (lazy_list.cons x xs) ys := interleave (ys.map $ f x) (lazy_list.lseq (xs ()) ys)

/-- `nat.shrink' k n` creates a list of smaller natural numbers by
successively dividing `n` by 2 and subtracting the difference from
`k`. For example, `nat.shrink 100 = [50, 75, 88, 94, 97, 99]`. -/
def nat.shrink' (k : ℕ) : ℕ → list ℕ → list ℕ
| n ls :=
if h : n ≤ 1
  then ls.reverse
  else
    have 1 * n / 2 < n,
      from nat.div_lt_of_lt_mul (nat.mul_lt_mul_of_pos_right (by norm_num) (by linarith)),
    have n / 2 < n, by simpa,
    let m := n / 2 in
    nat.shrink' m ((k - m) :: ls)

/-- `nat.shrink n` creates a list of smaller natural numbers by
successively dividing by 2 and subtracting the difference from
`n`. For example, `nat.shrink 100 = [50, 75, 88, 94, 97, 99]`. -/
def nat.shrink (n : ℕ) : list ℕ :=
nat.shrink' n n []

open gen

/--
Transport a `sampleable` instance from a type `α` to a type `β` using
functions between the two, going in both directions.
-/
def sampleable.lift (α : Type u) {β : Type u} [sampleable α] (f : α → β) (g : β → α) : sampleable β :=
{ sample := f <$> sample α,
  shrink := λ x, f <$> shrink (g x) }

instance sampleable_nat : sampleable ℕ :=
{ sample := sized $ λ sz, coe <$> choose_any (fin $ succ (sz^3)) <|>
                          coe <$> choose_any (fin $ succ sz),
  shrink := lazy_list.of_list ∘ nat.shrink }

instance sampleable_fin {n} [fact $ 0 < n] : sampleable (fin n) :=
sampleable.lift ℕ (fin.of_nat') subtype.val

@[priority 100]
instance sampleable_fin' {n} : sampleable (fin (succ n)) :=
sampleable.lift ℕ fin.of_nat subtype.val

instance sampleable_pnat : sampleable ℕ+ :=
sampleable.lift ℕ nat.succ_pnat (λ i, i - 1)

/-- `int.shrink' k n` creates a list of integers by successively
dividing `n` by 2, subtracting the result from `k` and alternating the signs.
For example, `int.shrink 40 = [20, -20, 30, -30, 35, -35, 38, -38, 39, -39]`. -/
def int.shrink' (k : ℕ) : ℕ → list ℤ → list ℤ
| n ls :=
if h : 1 < n
  then
    have n / 2 < n, from div_lt_self (by linarith) (by norm_num),
    let m := n / 2 in
    let m' := k - m in
    int.shrink' m (-↑m' :: m' :: ls)
  else ls.reverse

/-- `int.shrink n` creates a list of integers by successively
dividing by 2, subtracting the result from `n` and alternating the signs.
For example, `int.shrink 40 = [20, -20, 30, -30, 35, -35, 38, -38, 39, -39]`. -/
def int.shrink (i : ℤ) : list ℤ :=
int.shrink' (int.nat_abs i) (int.nat_abs i) []

instance sampleable_int : sampleable ℤ :=
{ sample := sized $ λ sz,
       let k := sz^5 in
       (λ n : fin _, n.val - int.of_nat (k / 2) ) <$> choose_any (fin $ succ k),
  shrink := lazy_list.of_list ∘ int.shrink   }

instance sampleable_bool : sampleable bool :=
{ sample := do { x ← choose_any bool,
                 return x },
  shrink := λ _, lazy_list.nil }

instance sampleable_prod {β} [sampleable α] [sampleable β] : sampleable (α × β) :=
{ sample := do { ⟨x⟩ ← uliftable.up $ sample α,
                 ⟨y⟩ ← uliftable.up $ sample β,
                 pure (x,y) },
  shrink := λ x, lazy_list.lseq prod.mk (shrink x.1) (shrink x.2) }

/-- shrinking function for sum types -/
def sum.shrink {β} [sampleable α] [sampleable β] : α ⊕ β → lazy_list (α ⊕ β)
| (sum.inr x) := (shrink x).map sum.inr
| (sum.inl x) := (shrink x).map sum.inl

instance sampleable_sum {β} [sampleable α] [sampleable β] : sampleable (α ⊕ β) :=
{ sample := uliftable.up_map sum.inl (sample α) <|>
            uliftable.up_map sum.inr (sample β),
  shrink := sum.shrink _ }

instance sampleable_rat : sampleable ℚ :=
sampleable.lift (ℤ × ℕ+) (λ x, prod.cases_on x rat.mk_pnat) (λ r, (r.num, ⟨r.denom, r.pos⟩))

/-- `sampleable_char` can be specialized into customized `sampleable char` instances.

The resulting instance has `1 / length` chances of making an unrestricted choice of characters
and it otherwise chooses a character from `characters` with uniform probabilities.  -/
def sampleable_char (length : nat) (characters : string) : sampleable char :=
{ sample := do { x ← choose_nat 0 length dec_trivial,
                 if x.val = 0 then do
                   n ← sample ℕ,
                   pure $ char.of_nat n
                 else do
                   i ← choose_nat 0 (characters.length - 1) dec_trivial,
                   pure (characters.mk_iterator.nextn i).curr },
  shrink := λ _, lazy_list.nil }

instance : sampleable char :=
sampleable_char 3 " 0123abcABC:,;`\\/"

variables {α}

/-- implementation of `sampleable (list α)` -/
def list.shrink' (shrink_a : α → lazy_list α) : list α → lazy_list (list α)
| [] := lazy_list.nil
| (x :: xs) :=
  let ys := list.shrink' xs in
  interleave ys $ lazy_list.lseq (::) ((shrink_a x).append (lazy_list.singleton x)) (lazy_list.cons [] ys)

/-- `list.shrink_with shrink_f xs` shrinks `xs` by deleting various items of the list
and shrinking others (using `shrink_f`). `lseq` is being used to interleave the
resulting shrunken lists to put smaller lists earlier in the results. -/
def list.shrink_with (shrink_a : α → lazy_list α) (xs : list α) : lazy_list (list α) :=
(list.shrink' shrink_a xs).init

instance sampleable_list [sampleable α] : sampleable (list α) :=
{ sample := list_of (sample α),
  shrink := list.shrink_with shrink  }

instance sampleable_prop : sampleable Prop :=
{ sample := do { x ← choose_any bool,
               return ↑x },
  shrink := λ _, lazy_list.nil }

instance sampleable_string : sampleable string :=
{ sample := do { x ← list_of (sample char), pure x.as_string },
  shrink := λ s, (shrink s.to_list).map list.as_string }

/-- implementation of `sampleable (tree α)` -/
def tree.sample (sample : gen α) : ℕ → gen (tree α) | n :=
if h : n > 0
then have n / 2 < n, from div_lt_self h (by norm_num),
     tree.node <$> sample <*> tree.sample (n / 2) <*> tree.sample (n / 2)
else pure tree.nil

/-- `tree.shrink_with shrink_f t` shrinks `xs` by using subtrees, shrinking them,
shrinking the contents and recombining the results into bigger trees. -/
def tree.shrink_with (shrink_a : α → lazy_list α) : tree α → lazy_list (tree α)
| tree.nil := lazy_list.nil
| (tree.node x t₀ t₁) :=
-- here, we drop the last tree of the interleaved lists because it is assumed
-- to be the full tree, i.e., not a shrunken tree.
lazy_list.init $ interleave_all [(tree.shrink_with t₀).append (lazy_list.singleton t₀),
                                 (tree.shrink_with t₁).append (lazy_list.singleton t₁),
                                 lazy_list.lseq id (lazy_list.lseq tree.node (shrink_a x) (tree.shrink_with t₀)) (tree.shrink_with t₁) ]

instance sampleable_tree [sampleable α] : sampleable (tree α) :=
{ sample := sized $ tree.sample (sample α),
  shrink := tree.shrink_with shrink }

setup_tactic_parser

/--
Print (at most) 10 samples of a given type to stdout for debugging.
-/
def print_samples (t : Type u) [sampleable t] [has_repr t] : io unit := do
xs ← io.run_rand $ uliftable.down $
  do { xs ← (list.range 10).mmap $ (sample t).run ∘ ulift.up,
       pure ⟨xs.map repr⟩ },
xs.mmap' io.put_str_ln

/--
`#sample my_type`, where `my_type` has an instance of `sampleable`, prints ten random
values of type `my_type` of using an increasing size parameter.

```lean
#sample nat
-- prints
-- 0
-- 0
-- 2
-- 24
-- 64
-- 76
-- 5
-- 132
-- 8
-- 449
-- or some other sequence of numbers

#sample list int
-- prints
-- []
-- [1, 1]
-- [-7, 9, -6]
-- [36]
-- [-500, 105, 260]
-- [-290]
-- [17, 156]
-- [-2364, -7599, 661, -2411, -3576, 5517, -3823, -968]
-- [-643]
-- [11892, 16329, -15095, -15461]
-- or whatever
```
-/
@[user_command]
meta def sample_cmd (_ : parse $ tk "#sample") : lean.parser unit :=
do e ← texpr,
   of_tactic $ do
     e ← tactic.i_to_expr e,
     sampleable_inst ← tactic.mk_app ``sampleable [e] >>= tactic.mk_instance,
     has_repr_inst ← tactic.mk_app ``has_repr [e] >>= tactic.mk_instance,
     print_samples ← tactic.mk_mapp ``print_samples [e, sampleable_inst, has_repr_inst],
     sample ← tactic.eval_expr (io unit) print_samples,
     tactic.unsafe_run_io sample

end slim_check
