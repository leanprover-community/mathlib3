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

## Notations

The following notation is introduced:

* `G /// H` stands for the quotient of the type `G` by the `set_like` element H

## Tags

quotient, group quotient, quotient group, module quotient, quotient module, ring quotient,
ideal quotient, quotient ring
-/

universes u v

class has_quotient (A : Type u) (B : Type v) [set_like B A] :=
(quotient : B → Type (max u v))

notation G `///`:35 H:34 := has_quotient.quotient G H
