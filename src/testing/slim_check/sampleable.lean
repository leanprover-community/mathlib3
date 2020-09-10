/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import data.lazy_list
import data.lazy_list2
import data.tree
import control.bifunctor
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
universes u v w

namespace slim_check

variables (α : Type u)

/-- `sampleable α` provides ways of creating examples of type `α`,
and given such an example `x : α`, gives us a way to shrink it
and find simpler examples.  -/
class sampleable :=
(sample [] : gen α)
(shrink : α → lazy_list α)

class sampleable_functor (F : Type u → Type v) [functor F] :=
(sample [] : ∀ {α}, gen α → gen (F α))
(shrink : ∀ {α}, (α → lazy_list α) → F α → lazy_list (F α))
[p_repr : ∀ α, has_repr α → has_repr (F α)]
-- [dec_eq : ∀ α, decidable_eq α → decidable_eq (F α)]

class sampleable_bifunctor (F : Type u → Type v → Type w) [bifunctor F] :=
(sample [] : ∀ {α β}, gen α → gen β → gen (F α β))
(shrink : ∀ {α β}, (α → lazy_list α) → (β → lazy_list β) → F α β → lazy_list (F α β))
[p_repr : ∀ α β, has_repr α → has_repr β → has_repr (F α β)]
-- [dec_eq : ∀ α β, decidable_eq α → decidable_eq β → decidable_eq (F α β)]

export sampleable (sample shrink)

meta def sampleable.mk_trivial_interp : tactic unit :=
tactic.refine ``(id)

class sampleable_ext (α : Sort u) :=
(proxy_repr : Type v)
(interp [] : proxy_repr → α . sampleable.mk_trivial_interp)
[p_repr : has_repr proxy_repr]
-- [dec_eq : decidable_eq proxy_repr]
(sample [] : gen proxy_repr)
(shrink : proxy_repr → lazy_list proxy_repr)

attribute [instance, priority 100] sampleable_ext.p_repr
attribute [instance, priority 100] sampleable_functor.p_repr
attribute [instance, priority 100] sampleable_bifunctor.p_repr
-- attribute [instance, priority 100]
--   sampleable_ext.dec_eq
--   sampleable_functor.dec_eq
--   sampleable_bifunctor.dec_eq

open nat lazy_list

section prio

open sampleable_ext

set_option default_priority 50

instance {α} [sampleable α] [decidable_eq α] [has_repr α] : sampleable_ext α :=
{ proxy_repr := α,
  sample := sampleable.sample α,
  shrink := shrink }

instance sampleable.functor {α} {F} [functor F] [sampleable_functor F] [sampleable α] : sampleable (F α) :=
{ sample := sampleable_functor.sample F (sampleable.sample α),
  shrink := sampleable_functor.shrink sampleable.shrink }

instance sampleable.bifunctor {α β} {F} [bifunctor F] [sampleable_bifunctor F] [sampleable α] [sampleable β] : sampleable (F α β) :=
{ sample := sampleable_bifunctor.sample F (sampleable.sample α) (sampleable.sample β),
  shrink := sampleable_bifunctor.shrink sampleable.shrink sampleable.shrink }

set_option default_priority 100

instance sampleable_ext.functor {α} {F} [functor F] [sampleable_functor F] [sampleable_ext α] : sampleable_ext (F α) :=
{ proxy_repr := F (proxy_repr α),
  interp := functor.map (interp _),
  sample := sampleable_functor.sample F (sampleable_ext.sample α),
  shrink := sampleable_functor.shrink sampleable_ext.shrink,
  -- dec_eq := sampleable_functor.dec_eq _ sampleable_ext.dec_eq,
  p_repr := sampleable_functor.p_repr _ sampleable_ext.p_repr
  }

instance sampleable_ext.bifunctor {α β} {F} [bifunctor F] [sampleable_bifunctor F] [sampleable_ext α] [sampleable_ext β] : sampleable_ext (F α β) :=
{ proxy_repr := F (proxy_repr α) (proxy_repr β),
  interp := bifunctor.bimap (interp _) (interp _),
  sample := sampleable_bifunctor.sample F (sampleable_ext.sample α) (sampleable_ext.sample β),
  shrink := sampleable_bifunctor.shrink sampleable_ext.shrink sampleable_ext.shrink,
  -- dec_eq := sampleable_bifunctor.dec_eq _ _ sampleable_ext.dec_eq sampleable_ext.dec_eq,
  p_repr := sampleable_bifunctor.p_repr _ _ sampleable_ext.p_repr sampleable_ext.p_repr
  }

end prio

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

instance nat.sampleable : sampleable ℕ :=
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

instance int.sampleable : sampleable ℤ :=
{ sample := sized $ λ sz,
       let k := sz^5 in
       (λ n : fin _, n.val - int.of_nat (k / 2) ) <$> choose_any (fin $ succ k),
  shrink := lazy_list.of_list ∘ int.shrink   }

instance bool.sampleable : sampleable bool :=
{ sample := do { x ← choose_any bool,
                 return x },
  shrink := λ _, lazy_list.nil }

instance prod.sampleable : sampleable_bifunctor.{u v} prod :=
{ sample := λ α β sama samb, do
              { ⟨x⟩ ← (uliftable.up $ sama : gen (ulift.{max u v} α)),
                ⟨y⟩ ← (uliftable.up $ samb : gen (ulift.{max u v} β)),
                pure (x,y) },
  shrink := λ α β sh_α sh_β x, lazy_list.lseq prod.mk (sh_α x.1) (sh_β x.2),
  -- dec_eq := @prod.decidable_eq,
  p_repr := @prod.has_repr }

/-- shrinking function for sum types -/
def sum.shrink {α β} (sam_α : α → lazy_list α) (sam_β : β → lazy_list β) : α ⊕ β → lazy_list (α ⊕ β)
| (sum.inl x) := (sam_α x).map sum.inl
| (sum.inr x) := (sam_β x).map sum.inr

instance sum.sampleable : sampleable_bifunctor.{u v} sum :=
{ sample := λ (α : Type u) (β : Type v) sam_α sam_β,
            (@uliftable.up_map gen.{u} gen.{max u v} _ _ _ _ (@sum.inl α β) sam_α <|>
             @uliftable.up_map gen.{v} gen.{max v u} _ _ _ _ (@sum.inr α β) sam_β),
  shrink := λ α β shr_α shr_β, sum.shrink shr_α shr_β,
  -- dec_eq := λ α β Iα Iβ, @sum.decidable_eq α Iα β Iβ,
  p_repr := @sum.has_repr }

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

instance char.sampleable : sampleable char :=
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

instance sampleable_list : sampleable_functor list.{u} :=
{ sample := λ α sam_α, list_of sam_α,
  shrink := λ α shr_α, list.shrink_with shr_α,
  -- dec_eq := @list.decidable_eq,
  p_repr := @list.has_repr }

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

instance : functor tree :=
{ map := @tree.map }

instance sampleable_tree : sampleable_functor tree :=
{ sample := λ α sam_α, sized $ tree.sample sam_α,
  shrink := λ α shr_α, tree.shrink_with shr_α,
  -- dec_eq := @tree.decidable_eq,
  p_repr := @tree.has_repr }

setup_tactic_parser

/-!
## Subtype instances

The following instances are meant to improve the testing of properties of the form
`∀ i j, i ≤ j, ...`

The naive way to test them is to choose two numbers `i` and `j` and check that
the proper ordering is satisfied. Instead, the following instances make it
so that `j` will be chosen with considerations to the required ordering
constraints. The benefit is that we will not have to discard any choice
of `j`.
 -/

instance slim_check.sampleable_nat_le {y} : slim_check.sampleable { x : ℕ // x ≤ y } :=
{ sample :=
         do { ⟨x,h⟩ ← slim_check.gen.choose_nat 0 y dec_trivial,
              pure ⟨x, h.2⟩},
  shrink := λ _, lazy_list.nil }

instance slim_check.sampleable_nat_ge {x} : slim_check.sampleable { y : ℕ // x ≤ y } :=
{ sample :=
         do { (y : ℕ) ← slim_check.sampleable.sample ℕ,
              pure ⟨x+y, by norm_num⟩ },
  shrink := λ _, lazy_list.nil }

instance slim_check.sampleable_nat_gt {x} : slim_check.sampleable { y : ℕ // x < y } :=
{ sample :=
         do { (y : ℕ) ← slim_check.sampleable.sample ℕ,
              pure ⟨x+y+1, by linarith⟩ },
  shrink := λ _, lazy_list.nil }

instance slim_check.sampleable_int_lt {y} : slim_check.sampleable { x : ℤ // x < y } :=
{ sample :=
         do { x ← slim_check.sampleable.sample ℕ,
              pure ⟨y - (x+1), sub_lt_self _ (by linarith)⟩},
  shrink := λ _, lazy_list.nil }

instance slim_check.sampleable_int_gt {x} : slim_check.sampleable { y : ℤ // x < y } :=
{ sample :=
         do { (y : ℕ) ← slim_check.sampleable.sample ℕ,
              pure ⟨x+y+1, by linarith⟩ },
  shrink := λ _, lazy_list.nil }

instance slim_check.sampleable_le {y : α} [decidable_linear_ordered_add_comm_group α] [sampleable α] : slim_check.sampleable { x : α // x ≤ y } :=
{ sample :=
         do { x ← sample α,
              pure ⟨y - abs x, sub_le_self _ (abs_nonneg _) ⟩ },
  shrink := λ _, lazy_list.nil }

instance slim_check.sampleable_ge {x : α} [decidable_linear_ordered_add_comm_group α] [sampleable α] : slim_check.sampleable { y : α // x ≤ y } :=
{ sample :=
         do { y ← sample α,
              pure ⟨x + abs y, by norm_num [abs_nonneg]⟩ },
  shrink := λ _, lazy_list.nil }

instance slim_check.perm {xs : list α} : slim_check.sampleable { ys : list α // list.perm xs ys } :=
{ sample := permutation_of xs,
  shrink := λ _, lazy_list.nil }

instance slim_check.perm' {xs : list α} : slim_check.sampleable { ys : list α // list.perm ys xs } :=
{ sample := subtype.map id (@list.perm.symm α _) <$> permutation_of xs,
  shrink := λ _, lazy_list.nil }

setup_tactic_parser

/--
Print (at most) 10 samples of a given type to stdout for debugging.
-/
def print_samples (t : Type u) [sampleable_ext t] : io unit := do
xs ← io.run_rand $ uliftable.down $
  do { xs ← (list.range 10).mmap $ (sampleable_ext.sample t).run ∘ ulift.up,
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
     print_samples ← tactic.mk_mapp ``print_samples [e,none],
     sample ← tactic.eval_expr (io unit) print_samples,
     tactic.unsafe_run_io sample

end slim_check
