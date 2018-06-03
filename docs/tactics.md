# Mathlib tactics #

In addition to [core tactics](https://leanprover.github.io/reference/tactics.html),
mathlib provides a number of specific interactive tactics and commands.
Here we document the mostly commonly used ones.

### rcases

The `rcases` tactic is the same as `cases`, but with more flexibility in the
`with` pattern syntax to allow for recursive case splitting. The pattern syntax
uses the following recursive grammar:

```
patt ::= (patt_list "|")* patt_list
patt_list ::= id | "_" | "⟨" (patt ",")* patt "⟩"
```

A pattern like `⟨a, b, c⟩ | ⟨d, e⟩` will do a split over the inductive
datatype, naming the first three parameters of the first constructor as
`a,b,c` and the first two of the second constructor `d,e`. If the list
is not as long as the number of arguments to the constructor or the
number of constructors, the remaining variables will be automatically
named. If there are nested brackets such as `⟨⟨a⟩, b | c⟩ | d` then
these will cause more case splits as necessary. If there are too many
arguments, such as `⟨a, b, c⟩` for splitting on `∃ x, ∃ y, p x`, then it
will be treated as `⟨a, ⟨b, c⟩⟩`, splitting the last parameter as
necessary.

### simpa

This is a "finishing" tactic modification of `simp`. The tactic `simpa
[rules, ...] using e` will simplify the hypothesis `e` using `rules`,
then simplify the goal using `rules`, and try to close the goal using
`assumption`. If `e` is a term instead of a local constant, it is first
added to the local context using `have`.

### replace

Acts like `have`, but removes a hypothesis with the same name as
this one. For example if the state is `h : p ⊢ goal` and `f : p → q`,
then after `replace h := f h` the goal will be `h : q ⊢ goal`,
where `have h := f h` would result in the state `h : p, h : q ⊢ goal`.
This can be used to simulate the `specialize` and `apply at` tactics
of Coq.

### finish/clarify/safe

These tactics do straightforward things: they call the simplifier, split conjunctive assumptions,
eliminate existential quantifiers on the left, and look for contradictions. They rely on ematching
and congruence closure to try to finish off a goal at the end.

The procedures *do* split on disjunctions and recreate the smt state for each terminal call, so
they are only meant to be used on small, straightforward problems.

* finish:  solves the goal or fails
* clarify:  makes as much progress as possible while not leaving more than one goal
* safe:     splits freely, finishes off whatever subgoals it can, and leaves the rest

All accept an optional list of simplifier rules, typically definitions that should be expanded.
(The equations and identities should not refer to the local context.)

### ring

Evaluate expressions in the language of (semi-)rings.
Based on [Proving Equalities in a Commutative Ring Done Right in Coq](http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf) by Benjamin Grégoire and Assia Mahboubi.

### congr'

Same as the `congr` tactic, but takes an optional argument which gives
the depth of recursive applications. This is useful when `congr`
is too aggressive in breaking down the goal. For example, given
`⊢ f (g (x + y)) = f (g (y + x))`, `congr'` produces the goals `⊢ x = y`
and `⊢ y = x`, while `congr' 2` produces the intended `⊢ x + y = y + x`.

### unfold_coes

Unfold coercion-related definitions

### Instance cache tactics

* `resetI`: Reset the instance cache. This allows any new instances
  added to the context to be used in typeclass inference.

* `unfreezeI`: Unfreeze local instances, which allows us to revert
  instances in the context

* `introI`/`introsI`: Like `intro`/`intros`, but uses the introduced variable
  in typeclass inference.

* `haveI`/`letI`: Used to add typeclasses to the context so that they can
  be used in typeclass inference. The syntax is the same as
  `have`/`letI`, but the proof-omitted version of `have` is not supported
  (for this one must write `have : t, { <proof> }, resetI, <proof>`).

* `exactI`: Like `exact`, but uses all variables in the context
  for typeclass inference.

### find

The `find` command from `tactic.find` allows to find lemmas using
pattern matching. For instance:

```lean
import tactic.find

#find _ + _ = _ + _
#find (_ : ℕ) + _ = _ + _
```

### solve_by_elim

The tactic `solve_by_elim` repeatedly applies assumptions to the current goal, and succeeds if this eventually discharges the main goal.
```lean
solve_by_elim `[cc]
```
also attempts to discharge the goal using congruence closure before each round of applying assumptions.

### ext1 / ext

 * `ext1 id` selects and apply one extensionality lemma (with
    attribute `extensionality`), using `id`, if provided, to name a
    local constant introduced by the lemma. If `id` is omitted, the
    local constant is named automatically, as per `intro`.

 * `ext` applies as many extensionality lemmas as possible;
 * `ext ids`, with `ids` a list of identifiers, finds extentionality
    and applies them until it runs out of identifiers in `ids` to name
    the local constants.

When trying to prove:

  ```
  α β : Type,
  f g : α → set β
  ⊢ f = g
  ```

applying `ext x y` yields:

  ```
  α β : Type,
  f g : α → set β,
  x : α,
  y : β
  ⊢ y ∈ f x ↔ y ∈ f x
  ```

by applying functional extensionality and set extensionality.
