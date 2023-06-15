/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import group_theory.submonoid.operations
import group_theory.subsemigroup.center

/-!
# Centers of monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `submonoid.center`: the center of a monoid
* `add_submonoid.center`: the center of an additive monoid

We provide `subgroup.center`, `add_subgroup.center`, `subsemiring.center`, and `subring.center` in
other files.
-/

namespace submonoid
section
variables (M : Type*) [monoid M]

/-- The center of a monoid `M` is the set of elements that commute with everything in `M` -/
@[to_additive "The center of a monoid `M` is the set of elements that commute with everything in
`M`"]
def center : submonoid M :=
{ carrier := set.center M,
  one_mem' := set.one_mem_center M,
  mul_mem' := λ a b, set.mul_mem_center }

@[to_additive] lemma coe_center : ↑(center M) = set.center M := rfl

@[simp]
lemma center_to_subsemigroup : (center M).to_subsemigroup = subsemigroup.center M := rfl

lemma _root_.add_submonoid.center_to_add_subsemigroup (M) [add_monoid M] :
  (add_submonoid.center M).to_add_subsemigroup = add_subsemigroup.center M := rfl

attribute [to_additive add_submonoid.center_to_add_subsemigroup] submonoid.center_to_subsemigroup

variables {M}

@[to_additive] lemma mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g := iff.rfl

@[to_additive] instance decidable_mem_center (a) [decidable $ ∀ b : M, b * a = a * b] :
  decidable (a ∈ center M) :=
decidable_of_iff' _ mem_center_iff

/-- The center of a monoid is commutative. -/
instance : comm_monoid (center M) :=
{ mul_comm := λ a b, subtype.ext $ b.prop _,
  .. (center M).to_monoid }

/-- The center of a monoid acts commutatively on that monoid. -/
instance center.smul_comm_class_left : smul_comm_class (center M) M M :=
{ smul_comm := λ m x y, (commute.left_comm (m.prop x) y).symm }

/-- The center of a monoid acts commutatively on that monoid. -/
instance center.smul_comm_class_right : smul_comm_class M (center M) M :=
smul_comm_class.symm _ _ _

/-! Note that `smul_comm_class (center M) (center M) M` is already implied by
`submonoid.smul_comm_class_right` -/
example : smul_comm_class (center M) (center M) M := by apply_instance

end

section
variables (M : Type*) [comm_monoid M]

@[simp] lemma center_eq_top : center M = ⊤ :=
set_like.coe_injective (set.center_eq_univ M)

end

end submonoid

-- Guard against import creep
assert_not_exists finset
