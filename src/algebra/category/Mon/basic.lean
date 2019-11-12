/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import category_theory.concrete_category
import algebra.group
import data.equiv.algebra

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

-- We verify that the coercions of morphisms to functions work correctly:
example {R S : Mon}     (f : R ⟶ S) : (R : Type) → (S : Type) := f
example {R S : CommMon} (f : R ⟶ S) : (R : Type) → (S : Type) := f


variables {X Y : Type u}

section
variables [monoid X] [monoid Y]

/-- Build an isomorphism in the category `Mon` from a `mul_equiv` between `monoid`s. -/
@[to_additive add_equiv.to_AddMon_iso "Build an isomorphism in the category `AddMon` from a `add_equiv` between `add_monoid`s."]
def mul_equiv.to_Mon_iso (e : X ≃* Y) : Mon.of X ≅ Mon.of Y :=
{ hom := e.to_monoid_hom,
  inv := e.symm.to_monoid_hom }

@[simp, to_additive add_equiv.to_AddMon_iso_hom]
lemma mul_equiv.to_Mon_iso_hom {e : X ≃* Y} : e.to_Mon_iso.hom = e.to_monoid_hom := rfl
@[simp, to_additive add_equiv.to_AddMon_iso_inv]
lemma mul_equiv.to_Mon_iso_inv {e : X ≃* Y} : e.to_Mon_iso.inv = e.symm.to_monoid_hom := rfl
end

section
variables [comm_monoid X] [comm_monoid Y]

/-- Build an isomorphism in the category `CommMon` from a `mul_equiv` between `comm_monoid`s. -/
@[to_additive add_equiv.to_AddCommMon_iso "Build an isomorphism in the category `AddCommMon` from a `add_equiv` between `add_comm_monoid`s."]
def mul_equiv.to_CommMon_iso (e : X ≃* Y) : CommMon.of X ≅ CommMon.of Y :=
{ hom := e.to_monoid_hom,
  inv := e.symm.to_monoid_hom }

@[simp, to_additive add_equiv.to_AddCommMon_iso_hom]
lemma mul_equiv.to_CommMon_iso_hom {e : X ≃* Y} : e.to_CommMon_iso.hom = e.to_monoid_hom := rfl
@[simp, to_additive add_equiv.to_AddCommMon_iso_inv]
lemma mul_equiv.to_CommMon_iso_inv {e : X ≃* Y} : e.to_CommMon_iso.inv = e.symm.to_monoid_hom := rfl
end

namespace category_theory.iso

/-- Build a `mul_equiv` from an isomorphism in the category `Mon`. -/
@[to_additive AddMond_iso_to_add_equiv "Build an `add_equiv` from an isomorphism in the category `AddMon`."]
def Mon_iso_to_mul_equiv {X Y : Mon.{u}} (i : X ≅ Y) : X ≃* Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  map_mul'  := by tidy }.

/-- Build a `mul_equiv` from an isomorphism in the category `CommMon`. -/
@[to_additive AddCommMon_iso_to_add_equiv "Build an `add_equiv` from an isomorphism in the category `AddCommMon`."]
def CommMon_iso_to_mul_equiv {X Y : CommMon.{u}} (i : X ≅ Y) : X ≃* Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  map_mul'  := by tidy }.

end category_theory.iso

/-- multiplicative equivalences between `monoid`s are the same as (isomorphic to) isomorphisms in `Mon` -/
@[to_additive add_equiv_iso_AddMon_iso "additive equivalences between `add_monoid`s are the same as (isomorphic to) isomorphisms in `AddMon`"]
def mul_equiv_iso_Mon_iso {X Y : Type u} [monoid X] [monoid Y] :
  (X ≃* Y) ≅ (Mon.of X ≅ Mon.of Y) :=
{ hom := λ e, e.to_Mon_iso,
  inv := λ i, i.Mon_iso_to_mul_equiv, }

/-- multiplicative equivalences between `comm_monoid`s are the same as (isomorphic to) isomorphisms in `CommMon` -/
@[to_additive add_equiv_iso_AddCommMon_iso "additive equivalences between `add_comm_monoid`s are the same as (isomorphic to) isomorphisms in `AddCommMon`"]
def mul_equiv_iso_CommMon_iso {X Y : Type u} [comm_monoid X] [comm_monoid Y] :
  (X ≃* Y) ≅ (CommMon.of X ≅ CommMon.of Y) :=
{ hom := λ e, e.to_CommMon_iso,
  inv := λ i, i.CommMon_iso_to_mul_equiv, }
