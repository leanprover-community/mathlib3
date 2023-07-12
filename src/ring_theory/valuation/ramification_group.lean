/-
Copyright (c) 2022 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import ring_theory.ideal.local_ring
import ring_theory.valuation.valuation_subring

/-!
# Ramification groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The decomposition subgroup and inertia subgroups.

TODO: Define higher ramification groups in lower numbering
-/

namespace valuation_subring

open_locale pointwise

variables (K : Type*) {L : Type*} [field K] [field L] [algebra K L]

/-- The decomposition subgroup defined as the stabilizer of the action
on the type of all valuation subrings of the field. -/
@[reducible] def decomposition_subgroup (A : valuation_subring L) :
  subgroup (L ≃ₐ[K] L) :=
mul_action.stabilizer (L ≃ₐ[K] L) A

/-- The valuation subring `A` (considered as a subset of `L`)
is stable under the action of the decomposition group. -/
def sub_mul_action (A : valuation_subring L) :
  sub_mul_action (A.decomposition_subgroup K) L :=
{ carrier := A,
  smul_mem' := λ g l h, set.mem_of_mem_of_subset (set.smul_mem_smul_set h) g.prop.le }

/-- The multiplicative action of the decomposition subgroup on `A`. -/
instance decomposition_subgroup_mul_semiring_action (A : valuation_subring L) :
  mul_semiring_action (A.decomposition_subgroup K) A :=
{ smul_add :=  λ g k l, subtype.ext $ smul_add g k l,
  smul_zero := λ g, subtype.ext $ smul_zero g,
  smul_one := λ g, subtype.ext $ smul_one g,
  smul_mul := λ g k l, subtype.ext $ smul_mul' g k l,
   ..(sub_mul_action.mul_action (A.sub_mul_action K)) }

/-- The inertia subgroup defined as the kernel of the group homomorphism from
the decomposition subgroup to the group of automorphisms of the residue field of `A`. -/
def inertia_subgroup (A : valuation_subring L) :
  subgroup (A.decomposition_subgroup K) :=
monoid_hom.ker $
  mul_semiring_action.to_ring_aut (A.decomposition_subgroup K) (local_ring.residue_field A)

end valuation_subring
