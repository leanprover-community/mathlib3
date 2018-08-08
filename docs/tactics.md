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

`rcases? e` will perform case splits on `e` in the same way as `rcases e`,
but rather than accepting a pattern, it does a maximal cases and prints the
pattern that would produce this case splitting. The default maximum depth is 5,
but this can be modified with `rcases? e : n`.

### rintro

The `rintro` tactic is a combination of the `intros` tactic with `rcases` to
allow for destructuring patterns while introducing variables. See `rcases` for
a description of supported patterns. For example, `rintros (a | ⟨b, c⟩) ⟨d, e⟩`
will introduce two variables, and then do case splits on both of them producing
two subgoals, one with variables `a d e` and the other with `b c d e`.

`rintro?` will introduce and case split on variables in the same way as
`rintro`, but will also print the `rintro` invocation that would have the same
result. Like `rcases?`, `rintro? : n` allows for modifying the
depth of splitting; the default is 5.

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

A maximum depth can be provided with `ext 3 with x y z`.

### refine_struct

`refine_struct { .. }` acts like `refine` but works only with structure instance
literals. It creates a goal for each missing field and tags it with the name of the
field so that `have_field` can be used to generically refer to the field currently
being refined.

As an example, we can use `refine_struct` to automate the construction semigroup
instances:

```
refine_struct ( { .. } : semigroup α ),
-- case semigroup, mul
-- α : Type u,
-- ⊢ α → α → α

-- case semigroup, mul_assoc
-- α : Type u,
-- ⊢ ∀ (a b c : α), a * b * c = a * (b * c)
```

`have_field`, used after `refine_struct _` poses `field` as a local constant
with the type of the field of the current goal:

```
refine_struct ({ .. } : semigroup α),
{ have_field, ... },
{ have_field, ... },
```
behaves like
```
refine_struct ({ .. } : semigroup α),
{ have field := @semigroup.mul, ... },
{ have field := @semigroup.mul_assoc, ... },
```

### apply_rules

`apply_rules hs n` applies the list of lemmas `hs` and `assumption` on the
first goal and the resulting subgoals, iteratively, at most `n` times.
`n` is optional, equal to 50 by default.
`hs` can contain user attributes: in this case all theorems with this
attribute are added to the list of rules.

For instance:

```
@[user_attribute]
meta def mono_rules : user_attribute :=
{ name := `mono_rules,
  descr := "lemmas usable to prove monotonicity" }

attribute [mono_rules] add_le_add mul_le_mul_of_nonneg_right

lemma my_test {a b c d e : real} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
-- any of the following lines solve the goal:
add_le_add (add_le_add (add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_right h2 h3)) h1 ) h2) h3
by apply_rules [add_le_add, mul_le_mul_of_nonneg_right]
by apply_rules [mono_rules]
by apply_rules mono_rules
```

### h_generalize

`h_generalize Hx : e == x` matches on `cast _ e` in the goal and replaces it with
`x`. It also adds `Hx : e == x` as an assumption. If `cast _ e` appears multiple
times (not necessarily with the same proof), they are all replaced by `x`. `cast`
`eq.mp`, `eq.mpr`, `eq.subst`, `eq.substr`, `eq.rec` and `eq.rec_on` are all treated
as casts.

 - `h_generalize Hx : e == x with h` adds hypothesis `α = β` with `e : α, x : β`;
 - `h_generalize Hx : e == x with _` chooses automatically chooses the name of
    assumption `α = β`;
  - `h_generalize! Hx : e == x` reverts `Hx`;
  - when `Hx` is omitted, assumption `Hx : e == x` is not added.

### pi_instance

`pi_instance` constructs an instance of `my_class (Π i : I, f i)`
where we know `Π i, my_class (f i)`. If an order relation is required,
it defaults to `pi.partial_order`. Any field of the instance that
`pi_instance` cannot construct is left untouched and generated as a
new goal.
