/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import tactic.basic

/-!
# Algebraic quotients

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines notation for algebraic quotients, e.g. quotient groups `G ⧸ H`,
quotient modules `M ⧸ N` and ideal quotients `R ⧸ I`.

The actual quotient structures are defined in the following files:
 * quotient group: `src/group_theory/quotient_group.lean`
 * quotient module: `src/linear_algebra/quotient.lean`
 * quotient ring: `src/ring_theory/ideal/quotient.lean`

## Notations

The following notation is introduced:

* `G ⧸ H` stands for the quotient of the type `G` by some term `H`
  (for example, `H` can be a normal subgroup of `G`).
  To implement this notation for other quotients, you should provide a `has_quotient` instance.
  Note that since `G` can usually be inferred from `H`, `_ ⧸ H` can also be used,
  but this is less readable.

## Tags

quotient, group quotient, quotient group, module quotient, quotient module, ring quotient,
ideal quotient, quotient ring
-/

universes u v

/-- `has_quotient A B` is a notation typeclass that allows us to write `A ⧸ b` for `b : B`.
This allows the usual notation for quotients of algebraic structures,
such as groups, modules and rings.

`A` is a parameter, despite being unused in the definition below, so it appears in the notation.
-/
class has_quotient (A : out_param $ Type u) (B : Type v) :=
(quotient' : B → Type (max u v))

/-- `has_quotient.quotient A b` (with notation `A ⧸ b`) is the quotient of the type `A` by `b`.

This differs from `has_quotient.quotient'` in that the `A` argument is explicit, which is necessary
to make Lean show the notation in the goal state.
-/
@[reducible, nolint has_nonempty_instance] -- Will be provided by e.g. `ideal.quotient.inhabited`
def has_quotient.quotient (A : out_param $ Type u) {B : Type v} [has_quotient A B] (b : B) :
  Type (max u v) :=
has_quotient.quotient' b

notation G ` ⧸ `:35 H:34 := has_quotient.quotient G H
