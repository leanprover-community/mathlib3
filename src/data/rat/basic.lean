/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import algebra.field.defs
import data.rat.defs

/-!
# Field Structure on the Rational Numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We put the (discrete) field structure on the type `ℚ` of rational numbers that
was defined in `data.rat.defs`.

## Main Definitions

- `rat.field` is the field structure on `ℚ`.

## Implementation notes

We have to define the field structure in a separate file to avoid cyclic imports:
the `field` class contains a map from `ℚ` (see `field`'s docstring for the rationale),
so we have a dependency `rat.field → field → rat` that is reflected in the import
hierarchy `data.rat.basic → algebra.field.basic → data.rat.defs`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/

namespace rat

instance : field ℚ :=
{ zero             := 0,
  add              := (+),
  neg              := has_neg.neg,
  one              := 1,
  mul              := (*),
  inv              := has_inv.inv,
  rat_cast         := id,
  rat_cast_mk      := λ a b h1 h2, (num_div_denom _).symm,
  qsmul            := (*),
  .. rat.comm_ring,
  .. rat.comm_group_with_zero}

/- Extra instances to short-circuit type class resolution -/
instance : division_ring ℚ      := by apply_instance

end rat
