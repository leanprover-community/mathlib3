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
-/

universes u v

open category_theory

/-- The category of monoids and monoid morphisms. -/
@[to_additive AddMon]
def Mon : Type (u+1) := bundled monoid

namespace Mon
local attribute [reducible] Mon

@[to_additive]
instance bundled_hom : bundled_hom @monoid_hom :=
⟨@monoid_hom.to_fun, @monoid_hom.id, @monoid_hom.comp, @monoid_hom.ext⟩

-- Setup instances while `Group` is reducible:
@[to_additive] instance : concrete_category Mon.{u} := infer_instance
@[to_additive] instance (M : Mon) : monoid M := M.str
@[to_additive] instance : has_coe_to_sort Mon.{u} := infer_instance
@[to_additive] instance (X Y : Mon.{u}) : has_coe_to_fun (X ⟶ Y) := concrete_category.has_coe_to_fun

/-- Construct a bundled Mon from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [monoid M] : Mon := bundled.of M

end Mon

/-- The category of commutative monoids and monoid morphisms. -/
@[to_additive AddCommMon]
def CommMon : Type (u+1) := induced_category Mon (bundled.map comm_monoid.to_monoid.{u})

namespace CommMon
local attribute [reducible] CommMon

-- Setup instances while `CommMon` is reducible:
@[to_additive] instance : concrete_category CommMon.{u} := infer_instance
@[to_additive] instance : has_forget₂ CommMon.{u} Mon.{u} := infer_instance
@[to_additive] instance (M : CommMon) : comm_monoid M := M.str
@[to_additive] instance : has_coe_to_sort CommMon.{u} := infer_instance
@[to_additive] instance (M N : CommMon.{u}) : has_coe_to_fun (M ⟶ N) := concrete_category.has_coe_to_fun

/-- Construct a bundled CommMon from the underlying type and typeclass. -/
@[to_additive]
def of (X : Type u) [comm_monoid X] : CommMon := bundled.of X

-- FIXME I wish this wasn't necessary, but the more general lemma in bundled_hom.lean doesn't fire.
@[simp, to_additive] lemma coe_comp {X Y Z : CommMon} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g) x = g (f x) :=
congr_fun ((forget CommMon).map_comp _ _) x

end CommMon

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
