# Mathlib tactics

In addition to the [tactics found in the core library](https://leanprover.github.io/reference/tactics.html),
mathlib provides a number of specific interactive tactics.
Here we document the mostly commonly used ones, as well as some underdocumented tactics from core.


## elide/unelide

The `elide n (at ...)` tactic hides all subterms of the target goal or hypotheses
beyond depth `n` by replacing them with `hidden`, which is a variant
on the identity function. (Tactics should still mostly be able to see
through the abbreviation, but if you want to unhide the term you can use
`unelide`.)

The `unelide (at ...)` tactic removes all `hidden` subterms in the target
types (usually added by `elide`).

## finish/clarify/safe

These tactics do straightforward things: they call the simplifier, split conjunctive assumptions,
eliminate existential quantifiers on the left, and look for contradictions. They rely on ematching
and congruence closure to try to finish off a goal at the end.

The procedures *do* split on disjunctions and recreate the smt state for each terminal call, so
they are only meant to be used on small, straightforward problems.

* finish:  solves the goal or fails
* clarify: makes as much progress as possible while not leaving more than one goal
* safe:    splits freely, finishes off whatever subgoals it can, and leaves the rest

All accept an optional list of simplifier rules, typically definitions that should be expanded.
(The equations and identities should not refer to the local context.) All also accept an optional list of `ematch` lemmas, which must be preceded by `using`.

## abel

Evaluate expressions in the language of *additive*, commutative monoids and groups.
It attempts to prove the goal outright if there is no `at`
specifier and the target is an equality, but if this
fails, it falls back to rewriting all monoid expressions into a normal form.
If there is an `at` specifier, it rewrites the given target into a normal form.
```lean
example {α : Type*} {a b : α} [add_comm_monoid α] : a + (b + a) = a + a + b := by abel
example {α : Type*} {a b : α} [add_comm_group α] : (a + b) - ((b + a) + a) = -a := by abel
example {α : Type*} {a b : α} [add_comm_group α] (hyp : a + a - a = b - b) : a = 0 :=
by { abel at hyp, exact hyp }
```

## norm_num

Normalises numerical expressions. It supports the operations `+` `-` `*` `/` `^` and `%` over numerical types such as `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`, and can prove goals of the form `A = B`, `A ≠ B`, `A < B` and `A ≤ B`, where `A` and `B` are
numerical expressions. It also has a relatively simple primality prover.
```lean
import data.real.basic

example : (2 : ℝ) + 2 = 4 := by norm_num
example : (12345.2 : ℝ) ≠ 12345.3 := by norm_num
example : (73 : ℝ) < 789/2 := by norm_num
example : 123456789 + 987654321 = 1111111110 := by norm_num
example (R : Type*) [ring R] : (2 : R) + 2 = 4 := by norm_num
example (F : Type*) [linear_ordered_field F] : (2 : F) + 2 < 5 := by norm_num
example : nat.prime (2^13 - 1) := by norm_num
example : ¬ nat.prime (2^11 - 1) := by norm_num
example (x : ℝ) (h : x = 123 + 456) : x = 579 := by norm_num at h; assumption
```

## ring

Evaluate expressions in the language of *commutative* (semi)rings.
Based on [Proving Equalities in a Commutative Ring Done Right in Coq](http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf) by Benjamin Grégoire and Assia Mahboubi.

The variant `ring!` uses a more aggessive reducibility setting to determine equality of atoms.

## ring_exp

Evaluate expressions in *commutative* (semi)rings, allowing for variables in the exponent.

This tactic extends `ring`: it should solve every goal that `ring` can solve.
Additionally, it knows how to evaluate expressions with complicated exponents
(where `ring` only understands constant exponents).
The variants `ring_exp!` and `ring_exp_eq!` use a more aggessive reducibility setting to determine equality of atoms.

For example:
```lean
example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring_exp
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring_exp
example (x y : ℕ) : x + id y = y + id x := by ring_exp!
```



## Instance cache tactics

For performance reasons, Lean does not automatically update its database
of class instances during a proof. The group of tactics described below
helps forcing such updates. For a simple (but very artificial) example,
consider the function `default` from the core library. It has type
`Π (α : Sort u) [inhabited α], α`, so one can use `default α` only if Lean
can find a registered instance of `inhabited α`. Because the database of
such instance is not automatically updated during a proof, the following
attempt won't work (Lean will not pick up the instance from the local
context):
```lean
def my_id (α : Type) : α → α :=
begin
  intro x,
  have : inhabited α := ⟨x⟩,
  exact default α, -- Won't work!
end
```
However, it will work, producing the identity function, if one replaces have by its variant `haveI` described below.

* `resetI`: Reset the instance cache. This allows any instances
  currently in the context to be used in typeclass inference.

* `unfreezeI`: Unfreeze local instances, which allows us to revert
  instances in the context

* `introI`/`introsI`: `intro`/`intros` followed by `resetI`. Like
  `intro`/`intros`, but uses the introduced variable in typeclass inference.

* `haveI`/`letI`: `have`/`let` followed by `resetI`. Used to add typeclasses
  to the context so that they can be used in typeclass inference. The syntax
  `haveI := <proof>` and `haveI : t := <proof>` is supported, but
  `haveI : t, from _` and `haveI : t, { <proof> }` are not; in these cases
  use `have : t, { <proof> }, resetI` directly).

* `exactI`: `resetI` followed by `exact`. Like `exact`, but uses all
  variables in the context for typeclass inference.

## hint

`hint` lists possible tactics which will make progress (that is, not fail) against the current goal.

```lean
example {P Q : Prop} (p : P) (h : P → Q) : Q :=
begin
  hint,
  /- the following tactics make progress:
     ----
     solve_by_elim
     finish
     tauto
  -/
  solve_by_elim,
end
```

You can add a tactic to the list that `hint` tries by either using
1. `attribute [hint_tactic] my_tactic`, if `my_tactic` is already of type `tactic string`
(`tactic unit` is allowed too, in which case the printed string will be the name of the
tactic), or
2. `add_hint_tactic "my_tactic"`, specifying a string which works as an interactive tactic.

## suggest

`suggest` lists possible usages of the `refine` tactic and leaves the tactic state unchanged.
It is intended as a complement of the search function in your editor, the `#find` tactic, and `library_search`.

`suggest` takes an optional natural number `num` as input and returns the first `num` (or less, if all possibilities are exhausted) possibilities ordered by length of lemma names. The default for `num` is `50`.

For performance reasons `suggest` uses monadic lazy lists (`mllist`). This means that `suggest` might miss some results if `num` is not large enough. However, because `suggest` uses monadic lazy lists, smaller values of `num` run faster than larger values.

An example of `suggest` in action,

```lean
example (n : nat) : n < n + 1 :=
begin suggest, sorry end
```

prints the list,

```lean
Try this: exact nat.lt.base n
Try this: exact nat.lt_succ_self n
Try this: refine not_le.mp _
Try this: refine gt_iff_lt.mp _
Try this: refine nat.lt.step _
Try this: refine lt_of_not_ge _
...
```

## library_search

`library_search` is a tactic to identify existing lemmas in the library. It tries to close the
current goal by applying a lemma from the library, then discharging any new goals using
`solve_by_elim`.

Typical usage is:
```
example (n m k : ℕ) : n * (m - k) = n * m - n * k :=
by library_search -- Try this: exact nat.mul_sub_left_distrib n m k
```

`library_search` prints a trace message showing the proof it found, shown above as a comment.
Typically you will then copy and paste this proof, replacing the call to `library_search`.


## solve_by_elim

The tactic `solve_by_elim` repeatedly applies assumptions to the current goal, and succeeds if this eventually discharges the main goal.
```lean
solve_by_elim { discharger := `[cc] }
```
also attempts to discharge the goal using congruence closure before each round of applying assumptions.

`solve_by_elim*` tries to solve all goals together, using backtracking if a solution for one goal
makes other goals impossible.

By default `solve_by_elim` also applies `congr_fun` and `congr_arg` against the goal.

The assumptions can be modified with similar syntax as for `simp`:
* `solve_by_elim [h₁, h₂, ..., hᵣ]` also applies the named lemmas (or all lemmas tagged with the named
attributes).
* `solve_by_elim only [h₁, h₂, ..., hᵣ]` does not include the local context, `congr_fun`, or `congr_arg`
unless they are explicitly included.
* `solve_by_elim [-id_1, ... -id_n]` uses the default assumptions, removing the specified ones.

## ext1 / ext

 * `ext1 id` selects and apply one extensionality lemma (with
    attribute `ext`), using `id`, if provided, to name a
    local constant introduced by the lemma. If `id` is omitted, the
    local constant is named automatically, as per `intro`.

 * `ext` applies as many extensionality lemmas as possible;
 * `ext ids`, with `ids` a list of identifiers, finds extentionality
    and applies them until it runs out of identifiers in `ids` to name
    the local constants.

When trying to prove:

  ```lean
  α β : Type,
  f g : α → set β
  ⊢ f = g
  ```

applying `ext x y` yields:

  ```lean
  α β : Type,
  f g : α → set β,
  x : α,
  y : β
  ⊢ y ∈ f x ↔ y ∈ g x
  ```

by applying functional extensionality and set extensionality.

A maximum depth can be provided with `ext x y z : 3`.

## The `ext` attribute

 Tag lemmas of the form:

 ```lean
 @[ext]
 lemma my_collection.ext (a b : my_collection)
   (h : ∀ x, a.lookup x = b.lookup y) :
   a = b := ...
 ```

 The attribute indexes extensionality lemma using the type of the
 objects (i.e. `my_collection`) which it gets from the statement of
 the lemma.  In some cases, the same lemma can be used to state the
 extensionality of multiple types that are definitionally equivalent.

 ```lean
 attribute [ext [(→),thunk,stream]] funext
 ```

 Those parameters are cumulative. The following are equivalent:

 ```lean
 attribute [ext [(→),thunk]] funext
 attribute [ext [stream]] funext
 ```

 and

 ```lean
 attribute [ext [(→),thunk,stream]] funext
 ```

 One removes type names from the list for one lemma with:

 ```lean
 attribute [ext [-stream,-thunk]] funext
 ```

 Also, the following:

 ```lean
 @[ext]
 lemma my_collection.ext (a b : my_collection)
   (h : ∀ x, a.lookup x = b.lookup y) :
   a = b := ...
 ```

 is equivalent to

 ```lean
 @[ext *]
 lemma my_collection.ext (a b : my_collection)
   (h : ∀ x, a.lookup x = b.lookup y) :
   a = b := ...
 ```

 The `*` parameter indicates to simply infer the
 type from the lemma's statement.

 This allows us specify type synonyms along with the type
 that referred to in the lemma statement.

 ```lean
 @[ext [*,my_type_synonym]]
 lemma my_collection.ext (a b : my_collection)
   (h : ∀ x, a.lookup x = b.lookup y) :
   a = b := ...
 ```

 Attribute `ext` can be applied to a structure to generate its extensionality lemma:

 ```
 @[ext]
 structure foo (α : Type*) :=
 (x y : ℕ)
 (z : {z // z < x})
 (k : α)
 (h : x < y)
 ```

 will generate:

 ```
 @[ext] lemma foo.ext : ∀ {α : Type u_1} (x y : foo α), x.x = y.x → x.y = y.y → x.z == y.z → x.k = y.k → x = y
 lemma foo.ext_iff : ∀ {α : Type u_1} (x y : foo α), x = y ↔ x.x = y.x ∧ x.y = y.y ∧ x.z == y.z ∧ x.k = y.k
 ```


## pi_instance

`pi_instance` constructs an instance of `my_class (Π i : I, f i)`
where we know `Π i, my_class (f i)`. If an order relation is required,
it defaults to `pi.partial_order`. Any field of the instance that
`pi_instance` cannot construct is left untouched and generated as a
new goal.

## assoc_rewrite

`assoc_rewrite [h₀, ← h₁] at ⊢ h₂` behaves like
`rewrite [h₀, ← h₁] at ⊢ h₂` with the exception that associativity is
used implicitly to make rewriting possible.

## restate_axiom

`restate_axiom` makes a new copy of a structure field, first definitionally simplifying the type.
This is useful to remove `auto_param` or `opt_param` from the statement.

As an example, we have:
```lean
structure A :=
(x : ℕ)
(a' : x = 1 . skip)

example (z : A) : z.x = 1 := by rw A.a' -- rewrite tactic failed, lemma is not an equality nor a iff

restate_axiom A.a'
example (z : A) : z.x = 1 := by rw A.a
```

By default, `restate_axiom` names the new lemma by removing a trailing `'`, or otherwise appending
`_lemma` if there is no trailing `'`. You can also give `restate_axiom` a second argument to
specify the new name, as in
```lean
restate_axiom A.a f
example (z : A) : z.x = 1 := by rw A.f
```

## def_replacer

`def_replacer foo` sets up a stub definition `foo : tactic unit`, which can
effectively be defined and re-defined later, by tagging definitions with `@[foo]`.

- `@[foo] meta def foo_1 : tactic unit := ...` replaces the current definition of `foo`.
- `@[foo] meta def foo_2 (old : tactic unit) : tactic unit := ...` replaces the current
  definition of `foo`, and provides access to the previous definition via `old`.
  (The argument can also be an `option (tactic unit)`, which is provided as `none` if
  this is the first definition tagged with `@[foo]` since `def_replacer` was invoked.)

`def_replacer foo : α → β → tactic γ` allows the specification of a replacer with
custom input and output types. In this case all subsequent redefinitions must have the
same type, or the type `α → β → tactic γ → tactic γ` or
`α → β → option (tactic γ) → tactic γ` analogously to the previous cases.

## tidy

`tidy` attempts to use a variety of conservative tactics to solve the goals.
In particular, `tidy` uses the `chain` tactic to repeatedly apply a list of tactics to
the goal and recursively on new goals, until no tactic makes further progress.

`tidy` can report the tactic script it found using `tidy?`. As an example
```lean
example : ∀ x : unit, x = unit.star :=
begin
  tidy? -- Prints the trace message: "intros x, exact dec_trivial"
end
```

The default list of tactics can be found by looking up the definition of
[`default_tidy_tactics`](https://github.com/leanprover/mathlib/blob/master/tactic/tidy.lean).

This list can be overriden using `tidy { tactics :=  ... }`. (The list must be a list of
`tactic string`, so that `tidy?` can report a usable tactic script.)

## linarith

`linarith` attempts to find a contradiction between hypotheses that are linear (in)equalities.
Equivalently, it can prove a linear inequality by assuming its negation and proving `false`.

In theory, `linarith` should prove any goal that is true in the theory of linear arithmetic over the rationals. While there is some special handling for non-dense orders like `nat` and `int`, this tactic is not complete for these theories and will not prove every true goal.

An example:
```lean
example (x y z : ℚ) (h1 : 2*x  < 3*y) (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0)  : false :=
by linarith
```

`linarith` will use all appropriate hypotheses and the negation of the goal, if applicable.

`linarith [t1, t2, t3]` will additionally use proof terms `t1, t2, t3`.

`linarith only [h1, h2, h3, t1, t2, t3]` will use only the goal (if relevant), local hypotheses
h1, h2, h3, and proofs t1, t2, t3. It will ignore the rest of the local context.

`linarith!` will use a stronger reducibility setting to try to identify atoms. For example,
```lean
example (x : ℚ) : id x ≥ x :=
by linarith
```
will fail, because `linarith` will not identify `x` and `id x`. `linarith!` will.
This can sometimes be expensive.

`linarith {discharger := tac, restrict_type := tp, exfalso := ff}` takes a config object with three optional
arguments.
* `discharger` specifies a tactic to be used for reducing an algebraic equation in the
proof stage. The default is `ring`. Other options currently include `ring SOP` or `simp` for basic
problems.
* `restrict_type` will only use hypotheses that are inequalities over `tp`. This is useful
if you have e.g. both integer and rational valued inequalities in the local context, which can
sometimes confuse the tactic.
* If `exfalso` is false, `linarith` will fail when the goal is neither an inequality nor `false`. (True by default.)



## squeeze_simp / squeeze_simpa

`squeeze_simp` and `squeeze_simpa` perform the same task with
the difference that `squeeze_simp` relates to `simp` while
`squeeze_simpa` relates to `simpa`. The following applies to both
`squeeze_simp` and `squeeze_simpa`.

`squeeze_simp` behaves like `simp` (including all its arguments)
and prints a `simp only` invokation to skip the search through the
`simp` lemma list.

For instance, the following is easily solved with `simp`:

```lean
example : 0 + 1 = 1 + 0 := by simp
```

To guide the proof search and speed it up, we may replace `simp`
with `squeeze_simp`:

```lean
example : 0 + 1 = 1 + 0 := by squeeze_simp
-- prints:
-- Try this: simp only [add_zero, eq_self_iff_true, zero_add]
```

`squeeze_simp` suggests a replacement which we can use instead of
`squeeze_simp`.

```lean
example : 0 + 1 = 1 + 0 := by simp only [add_zero, eq_self_iff_true, zero_add]
```

`squeeze_simp only` prints nothing as it already skips the `simp` list.

This tactic is useful for speeding up the compilation of a complete file.
Steps:

   1. search and replace ` simp` with ` squeeze_simp` (the space helps avoid the
      replacement of `simp` in `@[simp]`) throughout the file.
   2. Starting at the beginning of the file, go to each printout in turn, copy
      the suggestion in place of `squeeze_simp`.
   3. after all the suggestions were applied, search and replace `squeeze_simp` with
      `simp` to remove the occurrences of `squeeze_simp` that did not produce a suggestion.

Known limitation(s):
  * in cases where `squeeze_simp` is used after a `;` (e.g. `cases x; squeeze_simp`),
    `squeeze_simp` will produce as many suggestions as the number of goals it is applied to.
    It is likely that none of the suggestion is a good replacement but they can all be
    combined by concatenating their list of lemmas.

## fin_cases
`fin_cases h` performs case analysis on a hypothesis of the form
1) `h : A`, where `[fintype A]` is available, or
2) `h ∈ A`, where `A : finset X`, `A : multiset X` or `A : list X`.

`fin_cases *` performs case analysis on all suitable hypotheses.

As an example, in
```
example (f : ℕ → Prop) (p : fin 3) (h0 : f 0) (h1 : f 1) (h2 : f 2) : f p.val :=
begin
  fin_cases p; simp,
  all_goals { assumption }
end
```
after `fin_cases p; simp`, there are three goals, `f 0`, `f 1`, and `f 2`.

## mono

- `mono` applies a monotonicity rule.
- `mono*` applies monotonicity rules repetitively.
- `mono with x ≤ y` or `mono with [0 ≤ x,0 ≤ y]` creates an assertion for the listed
  propositions. Those help to select the right monotonicity rule.
- `mono left` or `mono right` is useful when proving strict orderings:
   for `x + y < w + z` could be broken down into either
    - left:  `x ≤ w` and `y < z` or
    - right: `x < w` and `y ≤ z`

To use it, first import `tactic.monotonicity`.

Here is an example of mono:

```lean
example (x y z k : ℤ)
  (h : 3 ≤ (4 : ℤ))
  (h' : z ≤ y) :
  (k + 3 + x) - y ≤ (k + 4 + x) - z :=
begin
  mono, -- unfold `(-)`, apply add_le_add
  { -- ⊢ k + 3 + x ≤ k + 4 + x
    mono, -- apply add_le_add, refl
    -- ⊢ k + 3 ≤ k + 4
    mono },
  { -- ⊢ -y ≤ -z
    mono /- apply neg_le_neg -/ }
end
```

More succinctly, we can prove the same goal as:

```lean
example (x y z k : ℤ)
  (h : 3 ≤ (4 : ℤ))
  (h' : z ≤ y) :
  (k + 3 + x) - y ≤ (k + 4 + x) - z :=
by mono*
```

## ac_mono

`ac_mono` reduces the `f x ⊑ f y`, for some relation `⊑` and a
monotonic function `f` to `x ≺ y`.

`ac_mono*` unwraps monotonic functions until it can't.

`ac_mono^k`, for some literal number `k` applies monotonicity `k`
times.

`ac_mono h`, with `h` a hypothesis, unwraps monotonic functions and
uses `h` to solve the remaining goal. Can be combined with `*` or `^k`:
`ac_mono* h`

`ac_mono : p` asserts `p` and uses it to discharge the goal result
unwrapping a series of monotonic functions. Can be combined with * or
^k: `ac_mono* : p`

In the case where `f` is an associative or commutative operator,
`ac_mono` will consider any possible permutation of its arguments and
use the one the minimizes the difference between the left-hand side
and the right-hand side.

To use it, first import `tactic.monotonicity`.

`ac_mono` can be used as follows:

```lean
example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : x ≤ y) :
  (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
  ac_mono,
  -- ⊢ (m + x + n) * z ≤ z * (y + n + m)
  ac_mono,
  -- ⊢ m + x + n ≤ y + n + m
  ac_mono,
end
```

As with `mono*`, `ac_mono*` solves the goal in one go and so does
`ac_mono* h₁`. The latter syntax becomes especially interesting in the
following example:

```lean
example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : m + x + n ≤ y + n + m) :
  (m + x + n) * z + k ≤ z * (y + n + m) + k :=
by ac_mono* h₁.
```

By giving `ac_mono` the assumption `h₁`, we are asking `ac_refl` to
stop earlier than it would normally would.


## push_neg

This tactic pushes negations inside expressions. For instance, given an assumption
```lean
h : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε)
```
writing `push_neg at h` will turn `h` into
```lean
h : ∃ ε, ε > 0 ∧ ∀ δ, δ > 0 → (∃ x, |x - x₀| ≤ δ ∧ ε < |f x - y₀|),
```
(the pretty printer does *not* use the abreviations `∀ δ > 0` and `∃ ε > 0` but this issue
has nothing to do with `push_neg`).
Note that names are conserved by this tactic, contrary to what would happen with `simp`
using the relevant lemmas. One can also use this tactic at the goal using `push_neg`,
at every assumption and the goal using `push_neg at *` or at selected assumptions and the goal
using say `push_neg at h h' ⊢` as usual.

## contrapose

Transforms the goal into its contrapositive.

`contrapose`     turns a goal `P → Q` into `¬ Q → ¬ P`

`contrapose!`    turns a goal `P → Q` into `¬ Q → ¬ P` and pushes negations inside `P` and `Q`
                 using `push_neg`

`contrapose h`   first reverts the local assumption `h`, and then uses `contrapose` and `intro h`

`contrapose! h`  first reverts the local assumption `h`, and then uses `contrapose!` and `intro h`

`contrapose h with new_h` uses the name `new_h` for the introduced hypothesis

## tautology

This tactic (with shorthand `tauto`) breaks down assumptions of the form `_ ∧ _`, `_ ∨ _`, `_ ↔ _` and `∃ _, _`
and splits a goal of the form `_ ∧ _`, `_ ↔ _` or `∃ _, _` until it can be discharged
using `reflexivity` or `solve_by_elim`. This is a finishing tactic: it
either closes the goal or raises an error.

The variants `tautology!` or `tauto!` use the law of excluded middle.

For instance, one can write:
```lean
example (p q r : Prop) [decidable p] [decidable r] : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (r ∨ p ∨ r) := by tauto
```
and the decidability assumptions can be dropped if `tauto!` is used
instead of `tauto`.


## apply_fun

Apply a function to some local assumptions which are either equalities
or inequalities. For instance, if the context contains `h : a = b` and
some function `f` then `apply_fun f at h` turns `h` into
`h : f a = f b`. When the assumption is an inequality `h : a ≤ b`, a side
goal `monotone f` is created, unless this condition is provided using
`apply_fun f at h using P` where `P : monotone f`, or the `mono` tactic
can prove it.

Typical usage is:
```lean
open function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : injective $ g ∘ f) :
  injective f :=
begin
  intros x x' h,
  apply_fun g at h,
  exact H h
end
```


## The `reassoc` attribute

The `reassoc` attribute can be applied to a lemma

```lean
@[reassoc]
lemma some_lemma : foo ≫ bar = baz := ...
```

and produce

```lean
lemma some_lemma_assoc {Y : C} (f : X ⟶ Y) : foo ≫ bar ≫ f = baz ≫ f := ...
```

The name of the produced lemma can be specified with `@[reassoc other_lemma_name]`. If
`simp` is added first, the generated lemma will also have the `simp` attribute.


## The reassoc_of function

`reassoc_of h` takes local assumption `h` and add a ` ≫ f` term on the right of both sides of the equality.
Instead of creating a new assumption from the result, `reassoc_of h` stands for the proof of that reassociated
statement. This prevents poluting the local context with complicated assumptions used only once or twice.

In the following, assumption `h` is needed in a reassociated form. Instead of proving it as a new goal and adding it as
an assumption, we use `reassoc_of h` as a rewrite rule which works just as well.

```lean
example (X Y Z W : C) (x : X ⟶ Y) (y : Y ⟶ Z) (z z' : Z ⟶ W) (w : X ⟶ Z)
  (h : x ≫ y = w)
  (h' : y ≫ z = y ≫ z') :
  x ≫ y ≫ z = w ≫ z' :=
begin
  -- reassoc_of h : ∀ {X' : C} (f : W ⟶ X'), x ≫ y ≫ f = w ≫ f
  rw [h',reassoc_of h],
end
```

Although `reassoc_of` is not a tactic or a meta program, its type is generated
through meta-programming to make it usable inside normal expressions.


## import_private

`import_private foo from bar` finds a private declaration `foo` in the same file as `bar` and creates a
local notation to refer to it.

`import_private foo`, looks for `foo` in all (imported) files.

When possible, make `foo` non-private rather than using this feature.

## default_dec_tac'

`default_dec_tac'` is a replacement for the core tactic `default_dec_tac`, fixing a bug. This
bug is often indicated by a message `nested exception message: tactic failed, there are no goals to be solved`,and solved by appending `using_well_founded wf_tacs` to the recursive definition.
See also additional documentation of `using_well_founded` in
[docs/extras/well_founded_recursion.md](extras/well_founded_recursion.md).

## simps

* The `@[simps]` attribute automatically derives lemmas specifying the projections of the declaration.
* Example: (note that the forward and reverse functions are specified differently!)
  ```lean
  @[simps] def refl (α) : α ≃ α := ⟨id, λ x, x, λ x, rfl, λ x, rfl⟩
  ```
  derives two simp-lemmas:
  ```lean
  @[simp] lemma refl_to_fun (α) (x : α) : (refl α).to_fun x = id x
  @[simp] lemma refl_inv_fun (α) (x : α) : (refl α).inv_fun x = x
  ```
* It does not derive simp-lemmas for the prop-valued projections.
* It will automatically reduce newly created beta-redexes, but not unfold any definitions.
* If one of the fields itself is a structure, this command will recursively create
  simp-lemmas for all fields in that structure.
* You can use `@[simps proj1 proj2 ...]` to only generate the projection lemmas for the specified
  projections. For example:
  ```lean
  attribute [simps to_fun] refl
  ```
* If one of the values is an eta-expanded structure, we will eta-reduce this structure.
* You can use `@[simps lemmas_only]` to derive the lemmas, but not mark them
  as simp-lemmas.
* You can use `@[simps short_name]` to only use the name of the last projection for the name of the
  generated lemmas.
* The precise syntax is `('simps' 'lemmas_only'? 'short_name'? ident*)`.
* If one of the projections is marked as a coercion, the generated lemmas do *not* use this
  coercion.
* `@[simps]` reduces let-expressions where necessary.
* If one of the fields is a partially applied constructor, we will eta-expand it
  (this likely never happens).
