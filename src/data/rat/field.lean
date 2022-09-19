/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import algebra.euclidean_domain
import algebra.order.field
import data.int.cast
import data.nat.gcd
import data.rat.defs
import logic.encodable.basic

/-!
# Field Structure on the Rational Numbers

## Summary

We put the (discrete) field structure on the type `ℚ` of rational numbers that
was defined in `data.rat.defs`.

## Main Definitions

- `rat.field` is the field structure on `ℚ`.

## Implementation notes

We have to define the field structure in a separate file to avoid cyclic imports:
the `field` class contains a map from `ℚ` (see `field`'s docstring for the rationale),
so we have a dependency `rat.field → field → rat` that is reflected in the import
hierarchy `data.rat.field → algebra.field.basic → data.rat.nnrat → data.rat.order → data.rat.basic`.

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

instance : linear_ordered_field ℚ :=
{ zero_le_one     := dec_trivial,
  add_le_add_left := assume a b ab c, rat.add_le_add_left.2 ab,
  mul_pos         := assume a b ha hb, lt_of_le_of_ne
    (rat.mul_nonneg (le_of_lt ha) (le_of_lt hb))
    (mul_ne_zero (ne_of_lt ha).symm (ne_of_lt hb).symm).symm,
  ..rat.field,
  ..rat.linear_order,
  ..rat.semiring }

/- Extra instances to short-circuit type class resolution -/
instance : division_ring ℚ      := by apply_instance

end rat
