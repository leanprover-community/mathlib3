/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Scott Morrison, Simon Hudon
-/
import category_theory.groupoid
import data.equiv.mul_add

/-!
# Endomorphisms

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

attribute [ext Aut] iso.ext

namespace Aut

instance inhabited : inhabited (Aut X) := ⟨iso.refl X⟩

instance : group (Aut X) :=
by refine_struct
{ one := iso.refl X,
  inv := iso.symm,
  mul := flip iso.trans,
  div := _,
  npow := @npow_rec (Aut X) ⟨iso.refl X⟩ ⟨flip iso.trans⟩,
  gpow := @gpow_rec (Aut X) ⟨iso.refl X⟩ ⟨flip iso.trans⟩ ⟨iso.symm⟩ };
intros; try { refl }; ext;
simp [flip, (*), monoid.mul, mul_one_class.mul, mul_one_class.one, has_one.one, monoid.one,
  has_inv.inv]

/--
Units in the monoid of endomorphisms of an object
are (multiplicatively) equivalent to automorphisms of that object.
-/
def units_End_equiv_Aut : units (End X) ≃* Aut X :=
{ to_fun := λ f, ⟨f.1, f.2, f.4, f.3⟩,
  inv_fun := λ f, ⟨f.1, f.2, f.4, f.3⟩,
  left_inv := λ ⟨f₁, f₂, f₃, f₄⟩, rfl,
  right_inv := λ ⟨f₁, f₂, f₃, f₄⟩, rfl,
  map_mul' := λ f g, by rcases f; rcases g; refl }

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
