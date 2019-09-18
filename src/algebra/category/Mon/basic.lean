/- Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

Introduce Mon -- the category of monoids.

Currently only the basic setup.
-/

import category_theory.concrete_category
import algebra.group

universes u v

open category_theory

/-- The category of monoids and monoid morphisms. -/
@[reducible, to_additive AddMon]
def Mon : Type (u+1) := bundled monoid

namespace Mon

@[to_additive add_monoid]
instance (x : Mon) : monoid x := x.str

@[to_additive]
def of (M : Type u) [monoid M] : Mon := bundled.of M

@[to_additive]
instance bundled_hom : bundled_hom @monoid_hom :=
⟨@monoid_hom.to_fun, @monoid_hom.id, @monoid_hom.comp, @monoid_hom.ext⟩

-- TODO generalize this!
@[simp] lemma hom_inv_id {X Y : Mon} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x :=
congr_fun (congr_arg monoid_hom.to_fun (f.hom_inv_id) : (f.hom ≫ f.inv).to_fun = _) x
@[simp] lemma inv_hom_id {X Y : Mon} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y :=
congr_fun (congr_arg monoid_hom.to_fun (f.inv_hom_id) : (f.inv ≫ f.hom).to_fun = _) y

end Mon

/-- The category of commutative monoids and monoid morphisms. -/
@[reducible, to_additive AddCommMon]
def CommMon : Type (u+1) := bundled comm_monoid

namespace CommMon

@[to_additive add_comm_monoid]
instance (x : CommMon) : comm_monoid x := x.str

@[to_additive]
def of (X : Type u) [comm_monoid X] : CommMon := bundled.of X

@[to_additive]
instance bundled_hom : bundled_hom _ :=
Mon.bundled_hom.full_subcategory @comm_monoid.to_monoid

@[to_additive has_forget_to_AddMon]
instance has_forget_to_Mon : has_forget CommMon.{u} Mon.{u} :=
Mon.bundled_hom.full_subcategory_has_forget _

-- TODO understand why this is necessary?
@[simp, to_additive] lemma coe_comp {X Y Z : CommMon} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g) x = g (f x) :=
congr_fun ((forget CommMon).map_comp _ _) x

-- TODO generalize this!
@[simp] lemma hom_inv_id {X Y : CommMon} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x :=
congr_fun (congr_arg monoid_hom.to_fun (f.hom_inv_id) : (f.hom ≫ f.inv).to_fun = _) x
@[simp] lemma inv_hom_id {X Y : CommMon} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y :=
congr_fun (congr_arg monoid_hom.to_fun (f.inv_hom_id) : (f.inv ≫ f.hom).to_fun = _) y

end CommMon

namespace mul_equiv

variables {X Y : Type u}

section
variables [monoid X] [monoid Y]

def to_Mon_iso (e : X ≃* Y) : Mon.of X ≅ Mon.of Y :=
{ hom := e.to_monoid_hom,
  inv := e.symm.to_monoid_hom }

@[simp] lemma to_Mon_iso_hom {e : X ≃* Y} : e.to_Mon_iso.hom = e.to_monoid_hom := rfl
@[simp] lemma to_Mon_iso_inv {e : X ≃* Y} : e.to_Mon_iso.inv = e.symm.to_monoid_hom := rfl
end

section
variables [comm_monoid X] [comm_monoid Y]

def to_CommMon_iso (e : X ≃* Y) : CommMon.of X ≅ CommMon.of Y :=
{ hom := e.to_monoid_hom,
  inv := e.symm.to_monoid_hom }

@[simp] lemma to_CommMon_iso_hom {e : X ≃* Y} : e.to_CommMon_iso.hom = e.to_monoid_hom := rfl
@[simp] lemma to_CommMon_iso_inv {e : X ≃* Y} : e.to_CommMon_iso.inv = e.symm.to_monoid_hom := rfl
end

end mul_equiv

namespace category_theory.iso

def Mon_iso_to_mul_equiv {X Y : Mon.{u}} (i : X ≅ Y) : X ≃* Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  map_mul'  := by tidy }.

def CommMon_iso_to_mul_equiv {X Y : CommMon.{u}} (i : X ≅ Y) : X ≃* Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  map_mul'  := by tidy }.

end category_theory.iso

/-- multiplicative equivalences are the same as (isomorphic to) isomorphisms of monoids -/
def mul_equiv_iso_Mon_iso {X Y : Type u} [monoid X] [monoid Y] :
  (X ≃* Y) ≅ (Mon.of X ≅ Mon.of Y) :=
{ hom := λ e, e.to_Mon_iso,
  inv := λ i, i.Mon_iso_to_mul_equiv, }

def mul_equiv_iso_CommMon_iso {X Y : Type u} [comm_monoid X] [comm_monoid Y] :
  (X ≃* Y) ≅ (CommMon.of X ≅ CommMon.of Y) :=
{ hom := λ e, e.to_CommMon_iso,
  inv := λ i, i.CommMon_iso_to_mul_equiv, }
