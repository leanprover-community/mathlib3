# Mathlib tactics #

In addition to [core tactics](https://leanprover.github.io/reference/tactics.html), 
mathlib provides a number of specific interactive tactics. Here we document
the mostly commonly used ones.

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

### Instance cache tactics

* `resetI`: Reset the instance cache. This allows any new instances
  added to the context to be used in typeclass inference.

* `introI`/`introsI`: Like `intro`/`intros`, but uses the introduced variable
  in typeclass inference. 

* `haveI`: Used to add typeclasses to the context so that they can
  be used in typeclass inference. The syntax is the same as `have`.

* `letI`: Used to add typeclasses to the context so that they can
  be used in typeclass inference. The syntax is the same as `let`. 

* `exactI`: Like `exact`, but uses all variables in the context
  for typeclass inference.
