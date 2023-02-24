/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Scott Morrison, Simon Hudon
-/
import algebra.hom.equiv.basic
import category_theory.groupoid
import category_theory.opposites
import group_theory.group_action.defs

/-!
# Endomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Definition and basic properties of endomorphisms and automorphisms of an object in a category.

For each `X : C`, we provide `End X := X ⟶ X` with a monoid structure,
and `Aut X := X ≅ X ` with a group structure.
-/

universes v v' u u'

namespace category_theory

/-- Endomorphisms of an object in a category. Arguments order in multiplication agrees with
`function.comp`, not with `category.comp`. -/
def End {C : Type u} [category_struct.{v} C] (X : C) := X ⟶ X

namespace End

section struct

variables {C : Type u} [category_struct.{v} C] (X : C)

instance has_one : has_one (End X) := ⟨𝟙 X⟩
instance inhabited : inhabited (End X) := ⟨𝟙 X⟩

/-- Multiplication of endomorphisms agrees with `function.comp`, not `category_struct.comp`. -/
instance has_mul : has_mul (End X) := ⟨λ x y, y ≫ x⟩

variable {X}

/-- Assist the typechecker by expressing a morphism `X ⟶ X` as a term of `End X`. -/
def of (f : X ⟶ X) : End X := f

/-- Assist the typechecker by expressing an endomorphism `f : End X` as a term of `X ⟶ X`. -/
def as_hom (f : End X) : X ⟶ X := f

@[simp] lemma one_def : (1 : End X) = 𝟙 X := rfl

@[simp] lemma mul_def (xs ys : End X) : xs * ys = ys ≫ xs := rfl

end struct

/-- Endomorphisms of an object form a monoid -/
instance monoid {C : Type u} [category.{v} C] {X : C} : monoid (End X) :=
{ mul_one := category.id_comp,
  one_mul := category.comp_id,
  mul_assoc := λ x y z, (category.assoc z y x).symm,
  ..End.has_mul X, ..End.has_one X }

section mul_action
variables {C : Type u} [category.{v} C]

open opposite

instance mul_action_right {X Y : C} : mul_action (End Y) (X ⟶ Y) :=
{ smul := λ r f, f ≫ r,
  one_smul := category.comp_id,
  mul_smul := λ r s f, eq.symm $ category.assoc _ _ _ }

instance mul_action_left {X : Cᵒᵖ} {Y : C} : mul_action (End X) (unop X ⟶ Y) :=
{ smul := λ r f, r.unop ≫ f,
  one_smul := category.id_comp,
  mul_smul := λ r s f, category.assoc _ _ _ }

lemma smul_right {X Y : C} {r : End Y} {f : X ⟶ Y} : r • f = f ≫ r := rfl
lemma smul_left {X : Cᵒᵖ} {Y : C} {r : (End X)} {f : unop X ⟶ Y} : r • f = r.unop ≫ f := rfl

end mul_action

/-- In a groupoid, endomorphisms form a group -/
instance group {C : Type u} [groupoid.{v} C] (X : C) : group (End X) :=
{ mul_left_inv := groupoid.comp_inv, inv := groupoid.inv, ..End.monoid }

end End

lemma is_unit_iff_is_iso {C : Type u} [category.{v} C] {X : C} (f : End X) :
  is_unit (f : End X) ↔ is_iso f :=
⟨λ h, { out := ⟨h.unit.inv, ⟨h.unit.inv_val, h.unit.val_inv⟩⟩ },
  λ h, by exactI ⟨⟨f, inv f, by simp, by simp⟩, rfl⟩⟩

variables {C : Type u} [category.{v} C] (X : C)

/--
Automorphisms of an object in a category.

The order of arguments in multiplication agrees with
`function.comp`, not with `category.comp`.
-/
def Aut (X : C) := X ≅ X

namespace Aut

instance inhabited : inhabited (Aut X) := ⟨iso.refl X⟩

instance : group (Aut X) :=
by refine_struct
{ one := iso.refl X,
  inv := iso.symm,
  mul := flip iso.trans,
  div := _,
  npow := @npow_rec (Aut X) ⟨iso.refl X⟩ ⟨flip iso.trans⟩,
  zpow := @zpow_rec (Aut X) ⟨iso.refl X⟩ ⟨flip iso.trans⟩ ⟨iso.symm⟩ };
intros; try { refl }; ext;
simp [flip, (*), monoid.mul, mul_one_class.mul, mul_one_class.one, has_one.one, monoid.one,
  has_inv.inv]

lemma Aut_mul_def (f g : Aut X) : f * g = g.trans f := rfl

lemma Aut_inv_def (f : Aut X) : f ⁻¹ = f.symm := rfl

/--
Units in the monoid of endomorphisms of an object
are (multiplicatively) equivalent to automorphisms of that object.
-/
def units_End_equiv_Aut : (End X)ˣ ≃* Aut X :=
{ to_fun := λ f, ⟨f.1, f.2, f.4, f.3⟩,
  inv_fun := λ f, ⟨f.1, f.2, f.4, f.3⟩,
  left_inv := λ ⟨f₁, f₂, f₃, f₄⟩, rfl,
  right_inv := λ ⟨f₁, f₂, f₃, f₄⟩, rfl,
  map_mul' := λ f g, by rcases f; rcases g; refl }

/-- Isomorphisms induce isomorphisms of the automorphism group -/
def Aut_mul_equiv_of_iso {X Y : C} (h : X ≅ Y) : Aut X ≃* Aut Y :=
{ to_fun := λ x, ⟨h.inv ≫ x.hom ≫ h.hom, h.inv ≫ x.inv ≫ h.hom⟩,
  inv_fun := λ y, ⟨h.hom ≫ y.hom ≫ h.inv, h.hom ≫ y.inv ≫ h.inv⟩,
  left_inv := by tidy,
  right_inv := by tidy,
  map_mul' := by simp [Aut_mul_def] }

end Aut

namespace functor

variables {D : Type u'} [category.{v'} D] (f : C ⥤ D) (X)

/-- `f.map` as a monoid hom between endomorphism monoids. -/
@[simps] def map_End : End X →* End (f.obj X) :=
{ to_fun := functor.map f,
  map_mul' := λ x y, f.map_comp y x,
  map_one' := f.map_id X }

/-- `f.map_iso` as a group hom between automorphism groups. -/
def map_Aut : Aut X →* Aut (f.obj X) :=
{ to_fun := f.map_iso,
  map_mul' := λ x y, f.map_iso_trans y x,
  map_one' := f.map_iso_refl X }

end functor

end category_theory
