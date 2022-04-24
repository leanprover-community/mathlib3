/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.CommMon_
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

variables (C : Type u₁) [category.{v₁} C]
variables (D : Type u₂) [category.{v₂} D] [monoidal_category.{v₂} D]

namespace Mon_functor_category_equivalence

variables {C D}

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
  { X := F ⋙ Mon_.forget D,
    one := { app := λ X, (F.obj X).one, },
    mul := { app := λ X, (F.obj X).mul, },
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
@[simps]
def unit_iso : 𝟭 (Mon_ (C ⥤ D)) ≅ functor ⋙ inverse :=
nat_iso.of_components (λ A,
  { hom :=
    { hom := { app := λ _, 𝟙 _ },
      one_hom' := by { ext X, dsimp, simp only [category.comp_id], },
      mul_hom' :=
        by { ext X, dsimp, simp only [tensor_id, category.id_comp, category.comp_id], }, },
    inv :=
    { hom := { app := λ _, 𝟙 _ },
      one_hom' := by { ext X, dsimp, simp only [category.comp_id], },
      mul_hom' :=
        by { ext X, dsimp, simp only [tensor_id, category.id_comp, category.comp_id], }, }, })
  (λ A B f,
  begin
    ext X,
    simp only [functor.id_map, functor.comp_map, functor_map_app_hom, Mon_.comp_hom',
      category.id_comp, category.comp_id, inverse_map_hom_app, nat_trans.comp_app],
  end)

/--
The counit for the equivalence `Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`.
-/
@[simps]
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

variables [braided_category.{v₂} D]

namespace CommMon_functor_category_equivalence

variables {C D}

/--
Functor translating a commutative monoid object in a functor category
to a functor into the category of commutative monoid objects.
-/
@[simps]
def functor : CommMon_ (C ⥤ D) ⥤ (C ⥤ CommMon_ D) :=
{ obj := λ A,
  { obj := λ X,
    { mul_comm' := congr_app A.mul_comm X,
      ..((Mon_functor_category_equivalence C D).functor.obj A.to_Mon_).obj X, },
    ..((Mon_functor_category_equivalence C D).functor.obj A.to_Mon_) },
  map := λ A B f,
  { app := λ X, ((Mon_functor_category_equivalence C D).functor.map f).app X, }, }

/--
Functor translating a functor into the category of commutative monoid objects
to a commutative monoid object in the functor category
-/
@[simps]
def inverse : (C ⥤ CommMon_ D) ⥤ CommMon_ (C ⥤ D) :=
{ obj := λ F,
  { mul_comm' := by { ext X, exact (F.obj X).mul_comm, },
    ..(Mon_functor_category_equivalence C D).inverse.obj (F ⋙ CommMon_.forget₂_Mon_ D), },
  map := λ F G α, (Mon_functor_category_equivalence C D).inverse.map (whisker_right α _), }

/--
The unit for the equivalence `CommMon_ (C ⥤ D) ≌ C ⥤ CommMon_ D`.
-/
@[simps]
def unit_iso : 𝟭 (CommMon_ (C ⥤ D)) ≅ functor ⋙ inverse :=
nat_iso.of_components (λ A,
  { hom :=
    { hom := { app := λ _, 𝟙 _ },
      one_hom' := by { ext X, dsimp, simp only [category.comp_id], },
      mul_hom' :=
      by { ext X, dsimp, simp only [tensor_id, category.id_comp, category.comp_id], }, },
    inv :=
    { hom := { app := λ _, 𝟙 _ },
      one_hom' := by { ext X, dsimp, simp only [category.comp_id], },
      mul_hom' :=
      by { ext X, dsimp, simp only [tensor_id, category.id_comp, category.comp_id], }, }, })
  (λ A B f,
  begin
    ext X,
    dsimp,
    simp only [category.id_comp, category.comp_id],
  end)

/--
The counit for the equivalence `CommMon_ (C ⥤ D) ≌ C ⥤ CommMon_ D`.
-/
@[simps]
def counit_iso : inverse ⋙ functor ≅ 𝟭 (C ⥤ CommMon_ D) :=
nat_iso.of_components (λ A,
  nat_iso.of_components (λ X,
  { hom := { hom := 𝟙 _ },
    inv := { hom := 𝟙 _ } })
  (by tidy))
  (by tidy)

end CommMon_functor_category_equivalence

open CommMon_functor_category_equivalence

/--
When `D` is a braided monoidal category,
commutative monoid objects in `C ⥤ D` are the same thing
as functors from `C` into the commutative monoid objects of `D`.
-/
@[simps]
def CommMon_functor_category_equivalence : CommMon_ (C ⥤ D) ≌ C ⥤ CommMon_ D :=
{ functor := functor,
  inverse := inverse,
  unit_iso := unit_iso,
  counit_iso := counit_iso, }

end category_theory.monoidal
