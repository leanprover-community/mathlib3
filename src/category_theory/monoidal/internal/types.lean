/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Mon.basic
import category_theory.monoidal.internal
import category_theory.monoidal.types

universes v u

open category_theory
open category_theory.monoidal

variables (C : Type u) [category.{v} C] [monoidal_category.{v} C]

namespace Mon_Type_equivalence_Mon

/--
Converting a monoid object in `Type` to a bundled monoid.
-/
def functor : Mon_ (Type u) ⥤ Mon.{u} :=
{ obj := λ A, ⟨A.X,
  { one := A.one punit.star,
    mul := λ x y, A.mul (x, y),
    one_mul := λ x, by convert congr_fun A.one_mul (punit.star, x),
    mul_one := λ x, by convert congr_fun A.mul_one (x, punit.star),
    mul_assoc := λ x y z, by convert congr_fun A.mul_assoc ((x, y), z), }⟩,
  map := λ A B f,
  { to_fun := f.hom,
    map_one' := congr_fun f.one_hom punit.star,
    map_mul' := λ x y, congr_fun f.mul_hom (x, y), }, }.

/--
Converting bundled monoid to a monoid object in `Type`.
-/
def inverse : Mon.{u} ⥤ Mon_ (Type u) :=
{ obj := λ A,
  { X := A,
    one := λ _, 1,
    mul := λ p, p.1 * p.2,
    mul_assoc' := by { ext ⟨⟨x, y⟩, z⟩, simp [mul_assoc], }, },
  map := λ A B f,
  { hom := f, }, }.

end Mon_Type_equivalence_Mon

open Mon_Type_equivalence_Mon

/--
The category of internal monoid objects in `Type`
is equivalent to the category of "native" bundled monoids.
-/
def Mon_Type_equivalence_Mon : Mon_ (Type u) ≌ Mon.{u} :=
{ functor := functor,
  inverse := inverse,
  unit_iso := nat_iso.of_components
    (λ A, { hom := { hom := 𝟙 _, }, inv := { hom := 𝟙 _, }})
    (by tidy),
  counit_iso := nat_iso.of_components (λ A,
  { hom := { to_fun := id, map_one' := rfl, map_mul' := λ x y, rfl, },
    inv := { to_fun := id, map_one' := rfl, map_mul' := λ x y, rfl, }}) (by tidy), }.

/--
The equivalence `Mon_ (Type u) ≌ Mon.{u}`
is naturally compatible with the forgetful functors to `Type u`.
-/
def Mon_Type_equivalence_Mon_forget :
  Mon_Type_equivalence_Mon.functor ⋙ forget Mon ≅ Mon_.forget :=
nat_iso.of_components (λ A, iso.refl _) (by tidy)

instance Mon_Type_inhabited : inhabited (Mon_ (Type u)) :=
Mon_Type_equivalence_Mon.functor.obj (Mon.of punit)
