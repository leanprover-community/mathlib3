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

/-- Denominator as `ℕ+`. -/
def pnat_denom (x : ℚ) : ℕ+ := ⟨x.denom, x.pos⟩

@[simp] lemma pnat_denom_eq_denom (x : ℚ) : (x.pnat_denom : ℕ) = x.denom :=
begin
  unfold rat.pnat_denom,
  rw pnat.mk_coe,
end

@[simp] lemma one_pnat_denom : (1 : ℚ).pnat_denom = 1 :=
begin
  unfold rat.pnat_denom,
  simp only [rat.denom_one, pnat.mk_one],
end

end rat
