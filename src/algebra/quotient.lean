/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import data.set_like.basic

/-!
# Algebraic quotients

This file defines notation for algebraic quotients, e.g. quotient groups `G /// H`,
quotient modules `M /// N` and ideal quotients `R /// I`.

The actual quotient structures are defined in the following files:
 * quotient group: `src/group_theory/quotient_group.lean`
 * quotient module: `src/linear_algebra/quotient.lean`
 * quotient ring: `src/ring_theory/ideal/quotient.lean`

## Notations

The following notation is introduced:

* `G /// H` stands for the quotient of the type `G` by the `set_like` element H.
  To implement this notation for other quotients, you should provide a `has_quotient` instance.

## Tags

quotient, group quotient, quotient group, module quotient, quotient module, ring quotient,
ideal quotient, quotient ring
-/

universes u v

/-- `has_quotient A B` is a notation typeclass that allows us to write `A /// b` for `b : B`.
This allows the usual notation for quotients of algebraic structures,
such as groups, modules and rings.

`A` is a parameter, despite being unused in the definition below, so it appears in the notation.
-/
class has_quotient (A : out_param $ Type u) (B : Type v) :=
(quotient' : B → Type (max u v))

/-- `has_quotient.quotient A b` (with notation `A /// b`) is the quotient of the type `A` by `b`.

`A` is a parameter, despite being unused in the definition below, so it appears in the notation.
-/
@[reducible, nolint has_inhabited_instance] -- Will be provided by e.g. `ideal.quotient.inhabited`
def has_quotient.quotient (A : out_param $ Type u) {B : Type v} [has_quotient A B] (b : B) :
  Type (max u v) :=
has_quotient.quotient' b

notation G ` /// `:35 H:34 := has_quotient.quotient G H
