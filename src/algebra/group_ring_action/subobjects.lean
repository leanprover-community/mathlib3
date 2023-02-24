/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.group_ring_action.basic
import group_theory.subgroup.basic

/-!
# Instances of `mul_semiring_action` for subobjects

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These are defined in this file as `semiring`s are not available yet where `submonoid` and `subgroup`
are defined.

Instances for `subsemiring` and `subring` are provided next to the other scalar actions instances
for those subobjects.

-/
variables {M G R : Type*}
variables [monoid M] [group G] [semiring R]

/-- A stronger version of `submonoid.distrib_mul_action`. -/
instance submonoid.mul_semiring_action [mul_semiring_action M R] (H : submonoid M) :
  mul_semiring_action H R :=
{ smul := (•),
  .. H.mul_distrib_mul_action,
  .. H.distrib_mul_action }

/-- A stronger version of `subgroup.distrib_mul_action`. -/
instance subgroup.mul_semiring_action [mul_semiring_action G R] (H : subgroup G) :
  mul_semiring_action H R :=
H.to_submonoid.mul_semiring_action
