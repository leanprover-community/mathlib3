/- Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

Introduce Group -- the category of groups.

Currently only the basic setup.
Copied from `algebra/category/Mon/basic.lean`.
-/

import algebra.punit_instances
import algebra.category.Mon.basic

universes u v

open category_theory

/-- The category of groups and group morphisms. -/
@[reducible, to_additive AddGroup]
def Group : Type (u+1) := bundled group

namespace Group

@[to_additive add_group]
instance (G : Group) : group G := G.str

@[to_additive] def of (X : Type u) [group X] : Group := bundled.of X

@[to_additive]
instance bundled_hom : bundled_hom _ :=
Mon.bundled_hom.full_subcategory @group.to_monoid

@[to_additive]
instance : has_one Group := ⟨Group.of punit⟩

end Group


/-- The category of commutative groups and group morphisms. -/
@[reducible, to_additive AddCommGroup]
def CommGroup : Type (u+1) := bundled comm_group

namespace CommGroup

@[to_additive add_comm_group]
instance (G : CommGroup) : comm_group G := G.str

@[to_additive] def of (G : Type u) [comm_group G] : CommGroup := bundled.of G

@[to_additive] instance : bundled_hom _ :=
Group.bundled_hom.full_subcategory @comm_group.to_group

@[to_additive has_forget_to_AddGroup]
instance has_forget_to_Group : has_forget CommGroup.{u} Group.{u} :=
Group.bundled_hom.full_subcategory_has_forget _

@[to_additive] instance : has_one CommGroup := ⟨CommGroup.of punit⟩

end CommGroup

namespace mul_equiv

variables {X Y : Type u}

section
variables [group X] [group Y]

def to_Group_iso (e : X ≃* Y) : Group.of X ≅ Group.of Y :=
{ hom := e.to_monoid_hom,
  inv := e.symm.to_monoid_hom }

@[simp] lemma to_Group_iso_hom {e : X ≃* Y} : e.to_Group_iso.hom = e.to_monoid_hom := rfl
@[simp] lemma to_Group_iso_inv {e : X ≃* Y} : e.to_Group_iso.inv = e.symm.to_monoid_hom := rfl
end

section
variables [comm_group X] [comm_group Y]

def to_CommGroup_iso (e : X ≃* Y) : CommGroup.of X ≅ CommGroup.of Y :=
{ hom := e.to_monoid_hom,
  inv := e.symm.to_monoid_hom }

@[simp] lemma to_CommGroup_iso_hom {e : X ≃* Y} : e.to_CommGroup_iso.hom = e.to_monoid_hom := rfl
@[simp] lemma to_CommGroup_iso_inv {e : X ≃* Y} : e.to_CommGroup_iso.inv = e.symm.to_monoid_hom := rfl
end

end mul_equiv

namespace category_theory.iso

def Group_iso_to_mul_equiv {X Y : Group.{u}} (i : X ≅ Y) : X ≃* Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  map_mul'  := by tidy }.

def CommGroup_iso_to_mul_equiv {X Y : CommGroup.{u}} (i : X ≅ Y) : X ≃* Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  map_mul'  := by tidy }.

end category_theory.iso

/-- multiplicative equivalences are the same as (isomorphic to) isomorphisms of monoids -/
def mul_equiv_iso_Group_iso {X Y : Type u} [group X] [group Y] :
  (X ≃* Y) ≅ (Group.of X ≅ Group.of Y) :=
{ hom := λ e, e.to_Group_iso,
  inv := λ i, i.Group_iso_to_mul_equiv, }

def mul_equiv_iso_CommGroup_iso {X Y : Type u} [comm_group X] [comm_group Y] :
  (X ≃* Y) ≅ (CommGroup.of X ≅ CommGroup.of Y) :=
{ hom := λ e, e.to_CommGroup_iso,
  inv := λ i, i.CommGroup_iso_to_mul_equiv, }

namespace category_theory.Aut

def iso_perm {α : Type u} : Group.of (Aut α) ≅ Group.of (equiv.perm α) :=
{ to_fun    := iso.to_equiv,
  inv_fun   := equiv.to_iso,
  left_inv  := by tidy, -- I miss `auto_param`s
  right_inv := by tidy,
  map_mul'  := by tidy, }

def mul_equiv_perm {α : Type u} : Aut α ≃* equiv.perm α :=
Aut_iso_perm.Group_iso_to_mul_equiv

end category_theory.Aut
