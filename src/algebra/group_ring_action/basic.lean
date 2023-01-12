/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.ring.equiv
import algebra.field.defs
import group_theory.group_action.group

/-!
# Group action on rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the typeclass of monoid acting on semirings `mul_semiring_action M R`,
and the corresponding typeclass of invariant subrings.

Note that `algebra` does not satisfy the axioms of `mul_semiring_action`.

## Implementation notes

There is no separate typeclass for group acting on rings, group acting on fields, etc.
They are all grouped under `mul_semiring_action`.

## Tags

group action, invariant subring

-/

universes u v

/-- Typeclass for multiplicative actions by monoids on semirings.

This combines `distrib_mul_action` with `mul_distrib_mul_action`. -/
class mul_semiring_action (M : Type u) (R : Type v) [monoid M] [semiring R]
  extends distrib_mul_action M R :=
(smul_one : ∀ (g : M), (g • 1 : R) = 1)
(smul_mul : ∀ (g : M) (x y : R), g • (x * y) = (g • x) * (g • y))

section semiring

variables (M N G : Type*) [monoid M] [monoid N] [group G]
variables (A R S F : Type v) [add_monoid A] [semiring R] [comm_semiring S] [division_ring F]

-- note we could not use `extends` since these typeclasses are made with `old_structure_cmd`
@[priority 100]
instance mul_semiring_action.to_mul_distrib_mul_action [h : mul_semiring_action M R] :
  mul_distrib_mul_action M R :=
{ ..h }

/-- Each element of the monoid defines a semiring homomorphism. -/
@[simps]
def mul_semiring_action.to_ring_hom [mul_semiring_action M R] (x : M) : R →+* R :=
{ .. mul_distrib_mul_action.to_monoid_hom R x,
  .. distrib_mul_action.to_add_monoid_hom R x }

theorem to_ring_hom_injective [mul_semiring_action M R] [has_faithful_smul M R] :
  function.injective (mul_semiring_action.to_ring_hom M R) :=
λ m₁ m₂ h, eq_of_smul_eq_smul $ λ r, ring_hom.ext_iff.1 h r

/-- Each element of the group defines a semiring isomorphism. -/
@[simps]
def mul_semiring_action.to_ring_equiv [mul_semiring_action G R] (x : G) : R ≃+* R :=
{ .. distrib_mul_action.to_add_equiv R x,
  .. mul_semiring_action.to_ring_hom G R x }

section
variables {M N}

/-- Compose a `mul_semiring_action` with a `monoid_hom`, with action `f r' • m`.
See note [reducible non-instances]. -/
@[reducible] def mul_semiring_action.comp_hom (f : N →* M) [mul_semiring_action M R] :
  mul_semiring_action N R :=
{ smul := has_smul.comp.smul f,
  ..distrib_mul_action.comp_hom R f,
  ..mul_distrib_mul_action.comp_hom R f }

end

section simp_lemmas

variables {M G A R F}

attribute [simp] smul_one smul_mul' smul_zero smul_add

/-- Note that `smul_inv'` refers to the group case, and `smul_inv` has an additional inverse
on `x`. -/
@[simp] lemma smul_inv'' [mul_semiring_action M F] (x : M) (m : F) : x • m⁻¹ = (x • m)⁻¹ :=
map_inv₀ (mul_semiring_action.to_ring_hom M F x) _

end simp_lemmas

end semiring
