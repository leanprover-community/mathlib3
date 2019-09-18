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
@[reducible] def Mon : Type (u+1) := bundled monoid

/-- The category of commutative monoids and monoid morphisms. -/
@[reducible] def CommMon : Type (u+1) := bundled comm_monoid

namespace Mon

instance (x : Mon) : monoid x := x.str

instance concrete_is_monoid_hom : concrete_category @is_monoid_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

def of (X : Type u) [monoid X] : Mon := ⟨X⟩

abbreviation forget : Mon.{u} ⥤ Type u := forget

instance hom_is_monoid_hom {R S : Mon} (f : R ⟶ S) : is_monoid_hom (f : R → S) := f.2

/-- Morphisms in `Mon` are defined using `subtype is_monoid_hom`,
so we provide a canonical bijection with `R →* S`. -/
def hom_equiv_monoid_hom (R S : Mon) : (R ⟶ S) ≃ (R →* S) :=
{ to_fun := λ f, @as_monoid_hom _ _ _ _ f.val f.property,
  inv_fun := λ f, ⟨f, f.is_monoid_hom⟩,
  right_inv := λ f, by rcases f; refl,
  left_inv := λ f, by rcases f; refl }

end Mon

namespace CommMon

instance (x : CommMon) : comm_monoid x := x.str

@[reducible] def is_comm_monoid_hom {α β} [comm_monoid α] [comm_monoid β] (f : α → β) : Prop :=
is_monoid_hom f

instance concrete_is_comm_monoid_hom : concrete_category @is_comm_monoid_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

def of (X : Type u) [comm_monoid X] : CommMon := ⟨X⟩

abbreviation forget : CommMon.{u} ⥤ Type u := forget

instance hom_is_comm_monoid_hom {R S : CommMon} (f : R ⟶ S) :
  is_comm_monoid_hom (f : R → S) := f.2

/-- The forgetful functor from commutative monoids to monoids. -/
def forget_to_Mon : CommMon ⥤ Mon :=
concrete_functor
  (by intros _ c; exact { ..c })
  (by introsI _ _ _ _ f i;  exact { ..i })

instance : faithful (forget_to_Mon) := {}

end CommMon

namespace mul_equiv

variables {X Y : Type u} [monoid X] [monoid Y]

def to_Mon_iso (e : X ≃* Y) : Mon.of X ≅ Mon.of Y :=
{ hom := e.to_monoid_hom,
  inv := ⟨e.inv_fun, by apply_instance⟩,
  hom_inv_id' := by { ext, exact e.left_inv x, },
  inv_hom_id' := funext e.right_inv }

@[simp] lemma to_Mon_iso_hom {e : X ≃* Y} : e.to_Mon_iso.hom = e := rfl
@[simp] lemma to_Mon_iso_inv {e : X ≃* Y} : e.to_Mon_iso.inv = e.symm := rfl

def to_CommMon_iso (e : X ≃* Y) : CommMon.of X ≅ CommMon.of Y :=
{ hom := e.to_fun,
  inv := e.inv_fun,
  hom_inv_id' := funext e.left_inv,
  inv_hom_id' := funext e.right_inv }

@[simp] lemma to_CommMon_iso_hom {e : X ≃* Y} : e.to_CommMon_iso.hom = e := rfl
@[simp] lemma to_CommMon_iso_inv {e : X ≃* Y} : e.to_CommMon_iso.inv = e.symm := rfl


end mul_equiv

universe u

namespace Mon.iso
variables {X Y : Mon.{u}}

def to_mul_equiv (i : X ≅ Y) : X ≃* Y :=
{ to_fun := i.hom,
  inv_fun := i.inv,
  left_inv := λ x, congr_fun i.hom_inv_id x,
  right_inv := λ y, congr_fun i.inv_hom_id y }

@[simp] lemma to_equiv_fun (i : X ≅ Y) : (i.to_equiv : X → Y) = i.hom := rfl
@[simp] lemma to_equiv_symm_fun (i : X ≅ Y) : (i.to_equiv.symm : Y → X) = i.inv := rfl
end Mon.iso

namespace CommMon.iso
variables {X Y : CommMon.{u}}

def to_mul_equiv (i : X ≅ Y) : X ≃* Y :=
{ to_fun := i.hom,
  inv_fun := i.inv,
  left_inv := λ x, congr_fun i.hom_inv_id x,
  right_inv := λ y, congr_fun i.inv_hom_id y }

@[simp] lemma to_equiv_fun (i : X ≅ Y) : (i.to_equiv : X → Y) = i.hom := rfl
@[simp] lemma to_equiv_symm_fun (i : X ≅ Y) : (i.to_equiv.symm : Y → X) = i.inv := rfl
end CommMon.iso

/-- multiplicative equivalences are the same as (isomorphic to) isomorphisms of monoids -/
-- TODO Anything in `Mul`, `Semigroup`, `Mon`, `CommMon`, `Group`, `CommGroup` would work here in place of `Mon`.
def mul_equiv_iso_Mon_iso {X Y : Type u} [monoid X] [monoid Y] : (X ≃* Y) ≅ (Mon.of X ≅ Mon.of Y) :=
{ hom := λ e, e.to_iso,
  inv := λ i, i.to_equiv, }
