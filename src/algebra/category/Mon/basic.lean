/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import category_theory.concrete_category
import algebra.group

/-!
# Category instances for monoid, add_monoid, comm_monoid, and add_comm_monoid.

We introduce the bundled categories:
* `Mon`
* `AddMon`
* `CommMon`
* `AddCommMon`
along with the relevant forgetful functors between them.

## Implementation notes

### Note [locally reducible category instances]

We make SemiRing (and the other categories) locally reducible in order
to define its instances. This is because writing, for example,

  instance : concrete_category SemiRing := by { delta SemiRing, apply_instance }

results in an instance of the form `id (bundled_hom.concrete_category _)`
and this `id`, not being [reducible], prevents a later instance search
(once SemiRing is no longer reducible) from seeing that the morphisms of
SemiRing are really semiring morphisms (`→+*`), and therefore have a coercion
to functions, for example. It's especially important that the `has_coe_to_sort`
instance not contain an extra `id` as we want the `semiring ↥R` instance to
also apply to `semiring R.α` (it seems to be impractical to guarantee that
we always access `R.α` through the coercion rather than directly).

TODO: Probably @[derive] should be able to create instances of the
required form (without `id`), and then we could use that instead of
this obscure `local attribute [reducible]` method.
-/

universes u v

open category_theory

/-- The category of monoids and monoid morphisms. -/
@[to_additive AddMon]
def Mon : Type (u+1) := bundled monoid

namespace Mon

/-- Construct a bundled Mon from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [monoid M] : Mon := bundled.of M

local attribute [reducible] Mon

@[to_additive]
instance : has_coe_to_sort Mon := infer_instance

@[to_additive add_monoid]
instance (M : Mon) : monoid M := M.str

@[to_additive]
instance bundled_hom : bundled_hom @monoid_hom :=
⟨@monoid_hom.to_fun, @monoid_hom.id, @monoid_hom.comp, @monoid_hom.coe_inj⟩

@[to_additive]
instance : concrete_category Mon := infer_instance

end Mon

/-- The category of commutative monoids and monoid morphisms. -/
@[to_additive AddCommMon]
def CommMon : Type (u+1) := induced_category Mon (bundled.map @comm_monoid.to_monoid)

namespace CommMon

/-- Construct a bundled CommMon from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [comm_monoid M] : CommMon := bundled.of M

local attribute [reducible] CommMon

@[to_additive]
instance : has_coe_to_sort CommMon := infer_instance

@[to_additive add_comm_monoid]
instance (M : CommMon) : comm_monoid M := M.str

@[to_additive]
instance : concrete_category CommMon := infer_instance

@[to_additive has_forget_to_AddMon]
instance has_forget_to_Mon : has_forget₂ CommMon Mon := infer_instance

end CommMon
