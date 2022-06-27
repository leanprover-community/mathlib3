/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import algebra.euclidean_domain
import data.int.cast
import data.nat.gcd
import data.rat.defs
import logic.encodable.basic

/-!
# Basic lemmas for the Rational Numbers

## Summary

We put the (discrete) field structure on the type `ℚ` of rational numbers that
was defined in `data.rat.defs`.

## Main Definitions

- `rat.field` is the field structure on `ℚ`.

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
  .. rat.comm_ring,
  .. rat.comm_group_with_zero}

/- Extra instances to short-circuit type class resolution -/
instance : division_ring ℚ      := by apply_instance

end rat
