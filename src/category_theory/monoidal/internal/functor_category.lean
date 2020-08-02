/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.internal
import category_theory.monoidal.functor_category

/-!
# `Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`

When `D` is a monoidal category,
monoid objects in `C ⥤ D` are the same thing as functors from `C` into the monoid objects of `D`.

This is formalised as:
* `Mon_functor_category_equivalence : Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`

The intended application is that as `Ring ≌ Mon_ Ab` (not yet constructed!),
we have `presheaf Ring X ≌ presheaf (Mon_ Ab) X ≌ Mon_ (presheaf Ab X)`,
and we can model a module over a presheaf of rings as a module object in `presheaf Ab X`.

## Future work
Presumably this statement is not specific to monoids,
and could be generalised to any internal algebraic objects,
if the appropriate framework was available.
-/

universes v₁ v₂ u₁ u₂

open category_theory
open category_theory.monoidal_category

namespace category_theory.monoidal

variables {C : Type u₁} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D] [monoidal_category.{v₂} D]

namespace Mon_functor_category_equivalence

/--
Functor translating a monoid object in a functor category
to a functor into the category of monoid objects.
-/
@[simps]
def functor : Mon_ (C ⥤ D) ⥤ (C ⥤ Mon_ D) :=
{ obj := λ A,
  { obj := λ X,
    { X := A.X.obj X,
      one := A.one.app X,
      mul := A.mul.app X,
      one_mul' := congr_app A.one_mul X,
      mul_one' := congr_app A.mul_one X,
      mul_assoc' := congr_app A.mul_assoc X, },
    map := λ X Y f,
    { hom := A.X.map f,
      one_hom' := by { rw [←A.one.naturality, tensor_unit_map], dsimp, rw [category.id_comp], },
      mul_hom' := by { dsimp, rw [←A.mul.naturality, tensor_obj_map], }, },
    map_id' := λ X, by { ext, dsimp, rw [category_theory.functor.map_id], },
    map_comp' := λ X Y Z f g, by { ext, dsimp, rw [functor.map_comp], }, },
  map := λ A B f,
  { app := λ X,
    { hom := f.hom.app X,
      one_hom' := congr_app f.one_hom X,
      mul_hom' := congr_app f.mul_hom X, }, }, }

/--
Functor translating a functor into the category of monoid objects
to a monoid object in the functor category
-/
@[simps]
def inverse : (C ⥤ Mon_ D) ⥤ Mon_ (C ⥤ D) :=
{ obj := λ F,
  { X :=
    { obj := λ X, (F.obj X).X,
      map := λ X Y f, (F.map f).hom, },
    one :=
    { app := λ X, (F.obj X).one, },
    mul :=
    { app := λ X, (F.obj X).mul, },
    one_mul' := by { ext X, exact (F.obj X).one_mul, },
    mul_one' := by { ext X, exact (F.obj X).mul_one, },
    mul_assoc' := by { ext X, exact (F.obj X).mul_assoc, }, },
  map := λ F G α,
  { hom :=
    { app := λ X, (α.app X).hom,
      naturality' := λ X Y f, congr_arg Mon_.hom.hom (α.naturality f), },
    one_hom' := by { ext x, dsimp, rw [(α.app x).one_hom], },
    mul_hom' := by { ext x, dsimp, rw [(α.app x).mul_hom], }, }, }

/--
The unit for the equivalence `Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`.
-/
@[simps {rhs_md := semireducible}]
def unit_iso : 𝟭 (Mon_ (C ⥤ D)) ≅ functor ⋙ inverse :=
nat_iso.of_components (λ A,
  { hom :=
    { hom := { app := λ _, 𝟙 _ },
      one_hom' := by { ext X, dsimp, simp, },
      mul_hom' := by { ext X, dsimp, simp, }, },
    inv :=
    { hom := { app := λ _, 𝟙 _ },
      one_hom' := by { ext X, dsimp, simp, },
      mul_hom' := by { ext X, dsimp, simp, }, }, })
  (by tidy)

/--
The counit for the equivalence `Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`.
-/
@[simps {rhs_md := semireducible}]
def counit_iso : inverse ⋙ functor ≅ 𝟭 (C ⥤ Mon_ D) :=
nat_iso.of_components (λ A,
  nat_iso.of_components (λ X,
  { hom := { hom := 𝟙 _ },
    inv := { hom := 𝟙 _ } })
  (by tidy))
  (by tidy)

end Mon_functor_category_equivalence

open Mon_functor_category_equivalence

/--
When `D` is a monoidal category,
monoid objects in `C ⥤ D` are the same thing
as functors from `C` into the monoid objects of `D`.
-/
@[simps]
def Mon_functor_category_equivalence : Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D :=
{ functor := functor,
  inverse := inverse,
  unit_iso := unit_iso,
  counit_iso := counit_iso, }

end category_theory.monoidal
