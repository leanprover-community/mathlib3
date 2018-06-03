# Mathlib naming conventions #
Author: [Jeremy Avigad](http://www.andrew.cmu.edu/user/avigad)

### General conventions ###

Identifiers are generally lower case with underscores. For the most
part, we rely on descriptive names. Often the name of theorem simply
describes the conclusion:

- `succ_ne_zero`
- `mul_zero`
- `mul_one`
- `sub_add_eq_add_sub`
- `le_iff_lt_or_eq`

If only a prefix of the description is enough to convey the meaning,
the name may be made even shorter:

- `neg_neg`
- `pred_succ`

Sometimes, to disambiguate the name of theorem or better convey the
intended reference, it is necessary to describe some of the
hypotheses. The word "of" is used to separate these hypotheses:

- `lt_of_succ_le`
- `lt_of_not_ge`
- `lt_of_le_of_ne`
- `add_lt_add_of_lt_of_le`

Sometimes abbreviations or alternative descriptions are easier to work
with. For example, we use `pos`, `neg`, `nonpos`, `nonneg` rather than
`zero_lt`, `lt_zero`, `le_zero`, and `zero_le`.

- `mul_pos`
- `mul_nonpos_of_nonneg_of_nonpos`
- `add_lt_of_lt_of_nonpos`
- `add_lt_of_nonpos_of_lt`

Sometimes the word "left" or "right" is helpful to describe variants
of a theorem.

- `add_le_add_left`
- `add_le_add_right`
- `le_of_mul_le_mul_left`
- `le_of_mul_le_mul_right`

We can also use the word "self" to indicate a repeated argument:

- `mul_inv_self`
- `neg_add_self`


### Dots ###

Dots are used for namespaces, and also automatically generated names
like recursors, eliminators, strutures projections. They can also be
introduced manually, for example, where projector notation is
useful. Thus they are used in all the following situations.

Intro, elim, and destruct rules for logical connectives, whether they
are automatically generated or not:

- `and.intro`
- `and.elim`
- `and.left`
- `and.right`
- `or.inl`
- `or.inr`
- `or.intro_left`
- `or.intro_right`
- `iff.intro`
- `iff.elim`
- `iff.mp`
- `iff.mpr`
- `not.intro`
- `not.elim`
- `eq.refl`
- `eq.rec`
- `eq.subst`
- `heq.refl`
- `heq.rec`
- `heq.subst`
- `exists.intro`
- `exists.elim`
- `true.intro`
- `false.elim`

Places where projection notation is useful, for example:

- `and.symm`
- `or.symm`
- `or.resolve_left`
- `or.resolve_right`
- `eq.symm`
- `eq.trans`
- `heq.symm`
- `heq.trans`
- `iff.symm`
- `iff.refl`

We generally restrict the use of dots to inductive types. So, for example, we use:

- `dvd_intro`
- `dvd_dest`
- `dvd_elim`
- `le_refl`
- `le_trans`

### Axiomatic descriptions ###

Some theorems are described using axiomatic names, rather than
describing their conclusions.

- `def`  (for unfolding a definition)
- `refl`
- `irrefl`
- `symm`
- `trans`
- `antisymm`
- `asymm`
- `congr`
- `comm`
- `assoc`
- `left_comm`
- `right_comm`
- `mul_left_cancel`
- `mul_right_cancel`
- `inj`  (injective)


### Variable conventions ###

- `u`, `v`, `w`, ... for universes
- `α`, `β`, `γ`, ... for types
- `a`, `b`, `c`, ... for propositions
- `x`, `y`, `z`, ... for elements of a generic type
- `h`, `h₁`, ...     for assumptions
- `p`, `q`, `r`, ... for predicates and relations
- `s`, `t`, ...      for lists
- `s`, `t`, ...      for sets
- `m`, `n`, `k`, ... for natural numbers
- `i`, `j`, `k`, ... for integers


### Names for symbols ###

- `imp`: implication
- `forall`
- `exists`
- `ball`: bounded forall
- `bex`: bounded exists


## Identifiers and theorem names ##

We generally use lower case with underscores for theorem names and
definitions. Sometimes upper case is used for bundled structures, such
as `Group`. In that case, use CamelCase for compound names, such as
`AbelianGroup`.

We adopt the following naming guidelines to make it easier for users
to guess the name of a theorem or find it using tab completion. Common
"axiomatic" properties of an operation like conjunction or
multiplication are put in a namespace that begins with the name of the
operation:
```lean
import standard algebra.ordered_ring

check and.comm
check mul.comm
check and.assoc
check mul.assoc
check @mul.left_cancel  -- multiplication is left cancelative
```
In particular, this includes `intro` and `elim` operations for logical
connectives, and properties of relations:
```lean
import standard algebra.ordered_ring

check and.intro
check and.elim
check or.intro_left
check or.intro_right
check or.elim

check eq.refl
check eq.symm
check eq.trans
```

For the most part, however, we rely on descriptive names. Often the
name of theorem simply describes the conclusion:
```lean
import standard algebra.ordered_ring
open nat
check succ_ne_zero
check mul_zero
check mul_one
check @sub_add_eq_add_sub
check @le_iff_lt_or_eq
```
If only a prefix of the description is enough to convey the meaning,
the name may be made even shorter:
```lean
import standard algebra.ordered_ring

check @neg_neg
check nat.pred_succ
```
When an operation is written as infix, the theorem names follow
suit. For example, we write `neg_mul_neg` rather than `mul_neg_neg` to
describe the patter `-a * -b`.

Sometimes, to disambiguate the name of theorem or better convey the
intended reference, it is necessary to describe some of the
hypotheses. The word "of" is used to separate these hypotheses:
```lean
import standard algebra.ordered_ring
open nat
check lt_of_succ_le
check lt_of_not_ge
check lt_of_le_of_ne
check add_lt_add_of_lt_of_le
```
The hypotheses are listed in the order they appear, _not_ reverse
order. For example, the theorem `A → B → C` would be named
`C_of_A_of_B`.

Sometimes abbreviations or alternative descriptions are easier to work
with. For example, we use `pos`, `neg`, `nonpos`, `nonneg` rather than
`zero_lt`, `lt_zero`, `le_zero`, and `zero_le`.
```lean
import standard algebra.ordered_ring
open nat
check mul_pos
check mul_nonpos_of_nonneg_of_nonpos
check add_lt_of_lt_of_nonpos
check add_lt_of_nonpos_of_lt
```

These conventions are not perfect. They cannot distinguish compound
expressions up to associativity, or repeated occurrences in a
pattern. For that, we make do as best we can. For example, `a + b - b = a`
could be named either `add_sub_self` or `add_sub_cancel`.

Sometimes the word "left" or "right" is helpful to describe variants
of a theorem.
```lean
import standard algebra.ordered_ring

check add_le_add_left
check add_le_add_right
check le_of_mul_le_mul_left
check le_of_mul_le_mul_right
```

------
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
