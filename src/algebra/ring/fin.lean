/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import logic.equiv.fin
import algebra.ring.equiv
import algebra.group.prod

/-!
# Rings and `fin`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file collects some basic results involving rings and the `fin` type

## Main results

 * `ring_equiv.fin_two`: The product over `fin 2` of some rings is the cartesian product

-/

/-- The product over `fin 2` of some rings is just the cartesian product of these rings. -/
@[simps]
def ring_equiv.pi_fin_two (R : fin 2 → Type*) [Π i, semiring (R i)] :
  (Π (i : fin 2), R i) ≃+* R 0 × R 1 :=
{ to_fun := pi_fin_two_equiv R,
  map_add' := λ a b, rfl,
  map_mul' := λ a b, rfl,
  .. pi_fin_two_equiv R }
