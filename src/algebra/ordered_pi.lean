/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import algebra.group.pi
import algebra.ordered_group
import tactic.pi_instances
/-!
# Pi instances for ordered groups and monoids

This file defines instances for ordered group, monoid, and related structures on Pi types.
-/

universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

namespace pi

/-- The product of a family of ordered commutative monoids is an ordered commutative monoid. -/
@[to_additive "The product of a family of ordered additive commutative monoids is
  an ordered additive commutative monoid."]
instance ordered_comm_monoid {ι : Type*} {Z : ι → Type*} [∀ i, ordered_comm_monoid (Z i)] :
  ordered_comm_monoid (Π i, Z i) :=
{ mul_le_mul_left := λ f g w h i, mul_le_mul_left' (w i) _,
  ..pi.partial_order,
  ..pi.comm_monoid, }

/-- The product of a family of canonically ordered monoids is a canonically ordered monoid. -/
@[to_additive "The product of a family of canonically ordered additive monoids is
  a canonically ordered additive monoid."]
instance {ι : Type*} {Z : ι → Type*} [∀ i, canonically_ordered_monoid (Z i)] :
  canonically_ordered_monoid (Π i, Z i) :=
{ le_iff_exists_mul := λ f g, begin
    fsplit,
    { intro w,
      fsplit,
      { exact λ i, (le_iff_exists_mul.mp (w i)).some, },
      { ext i,
        exact (le_iff_exists_mul.mp (w i)).some_spec, }, },
    { rintro ⟨h, rfl⟩,
      exact λ i, le_mul_right (le_refl _), },
  end,
  ..pi.order_bot,
  ..pi.ordered_comm_monoid, }

@[to_additive]
instance ordered_cancel_comm_monoid [∀ i, ordered_cancel_comm_monoid $ f i] :
  ordered_cancel_comm_monoid (Π i : I, f i) :=
by refine_struct { mul := (*), one := (1 : Π i, f i), le := (≤), lt := (<),
  npow := λ n x i, npow n (x i), .. pi.partial_order, .. pi.monoid };
  tactic.pi_instance_derive_field

@[to_additive]
instance ordered_comm_group [∀ i, ordered_comm_group $ f i] :
  ordered_comm_group (Π i : I, f i) :=
{ mul := (*), one := (1 : Π i, f i), le := (≤), lt := (<),
  npow := λ n x i, npow n (x i),
  ..pi.comm_group,
  ..pi.ordered_comm_monoid, }

end pi
