/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import algebra.punit_instances
import algebra.category.Mon.basic

/-!
# Category instances for group, add_group, comm_group, and add_comm_group.

We introduce the bundled categories:
* `Group`
* `AddGroup`
* `CommGroup`
* `AddCommGroup`
along with the relevant forgetful functors between them, and to the bundled monoid categories.
-/

universes u v

open category_theory

/-- The category of groups and group morphisms. -/
@[reducible, to_additive AddGroup]
def Group : Type (u+1) := induced_category Mon (bundled.map group.to_monoid.{u})

namespace Group

/-- Construct a bundled Group from the underlying type and typeclass. -/
@[to_additive] def of (X : Type u) [group X] : Group := bundled.of X

@[to_additive add_group]
instance (G : Group) : group G := G.str

@[to_additive]
instance : has_one Group := ⟨Group.of punit⟩

-- These examples verify that we have successfully provided the expected instances.
example : concrete_category Group.{u} := infer_instance
example : has_forget₂ Group.{u} Mon.{u} := infer_instance

end Group


/-- The category of commutative groups and group morphisms. -/
@[reducible, to_additive AddCommGroup]
def CommGroup : Type (u+1) := induced_category Group (bundled.map comm_group.to_group.{u})

namespace CommGroup

/-- Construct a bundled CommGroup from the underlying type and typeclass. -/
@[to_additive] def of (G : Type u) [comm_group G] : CommGroup := bundled.of G

@[to_additive add_comm_group]
instance (G : CommGroup) : comm_group G := G.str

-- These examples verify that we have successfully provided the expected instances.
example : concrete_category CommGroup.{u} := infer_instance
example : has_forget₂ CommGroup.{u} Group.{u} := infer_instance

@[to_additive has_forget_to_AddCommMon]
instance has_forget_to_CommMon : has_forget₂ CommGroup.{u} CommMon.{u} :=
induced_category.has_forget₂ (λ G : CommGroup, CommMon.of G)

@[to_additive] instance : has_one CommGroup := ⟨CommGroup.of punit⟩

-- TODO I wish this wasn't necessary, but the more general lemma in bundled_hom.lean doesn't fire.
@[simp, to_additive] lemma coe_comp {X Y Z : CommGroup} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g) x = g (f x) :=
congr_fun ((forget CommGroup).map_comp _ _) x

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
{ hom := ⟨λ g, g.to_equiv, (by tidy), (by tidy)⟩,
  inv := ⟨λ g, g.to_iso, (by tidy), (by tidy)⟩ }

def mul_equiv_perm {α : Type u} : Aut α ≃* equiv.perm α :=
iso_perm.Group_iso_to_mul_equiv

end category_theory.Aut
