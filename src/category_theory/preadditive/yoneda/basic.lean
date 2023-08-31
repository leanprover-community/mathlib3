/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.limits.yoneda
import category_theory.preadditive.opposite
import algebra.category.Module.basic
import algebra.category.Group.preadditive

/-!
# The Yoneda embedding for preadditive categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End Y`-module
structure.

We also show that this presheaf is additive and that it is compatible with the normal Yoneda
embedding in the expected way and deduce that the preadditive Yoneda embedding is fully faithful.

## TODO
* The Yoneda embedding is additive itself

-/

universes v u

open category_theory.preadditive opposite category_theory.limits

noncomputable theory

namespace category_theory

variables {C : Type u} [category.{v} C] [preadditive C]

/--
The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the `End Y`-module of morphisms `X ⟶ Y`.
-/
@[simps]
def preadditive_yoneda_obj (Y : C) : Cᵒᵖ ⥤ Module.{v} (End Y) :=
{ obj := λ X, Module.of _ (X.unop ⟶ Y),
  map := λ X X' f,
  { to_fun := λ g, f.unop ≫ g,
    map_add' := λ g g', comp_add _ _ _ _ _ _,
    map_smul' := λ r g, eq.symm $ category.assoc _ _ _ } }

/--
The Yoneda embedding for preadditive categories sends an object `Y` to the presheaf sending an
object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End Y`-module
structure, see `preadditive_yoneda_obj`.
-/
@[simps]
def preadditive_yoneda : C ⥤ (Cᵒᵖ ⥤ AddCommGroup.{v}) :=
{ obj := λ Y, preadditive_yoneda_obj Y ⋙ forget₂ _ _,
  map := λ Y Y' f,
  { app := λ X,
    { to_fun := λ g, g ≫ f,
      map_zero' := limits.zero_comp,
      map_add' := λ g g', add_comp _ _ _ _ _ _ },
    naturality' := λ X X' g, AddCommGroup.ext _ _ _ _ $ λ x, category.assoc _ _ _ },
  map_id' := λ X, by { ext, simp },
  map_comp' := λ X Y Z f g, by { ext, simp } }

/--
The Yoneda embedding for preadditive categories sends an object `X` to the copresheaf sending an
object `Y` to the `End X`-module of morphisms `X ⟶ Y`.
-/
@[simps]
def preadditive_coyoneda_obj (X : Cᵒᵖ) : C ⥤ Module.{v} (End X) :=
{ obj := λ Y, Module.of _ (unop X ⟶ Y),
  map := λ Y Y' f,
  { to_fun := λ g, g ≫ f,
    map_add' := λ g g', add_comp _ _ _ _ _ _,
    map_smul' := λ r g, category.assoc _ _ _ } }

/--
The Yoneda embedding for preadditive categories sends an object `X` to the copresheaf sending an
object `Y` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End X`-module
structure, see `preadditive_coyoneda_obj`.
-/
@[simps]
def preadditive_coyoneda : Cᵒᵖ ⥤ (C ⥤ AddCommGroup.{v}) :=
{ obj := λ X, preadditive_coyoneda_obj X ⋙ forget₂ _ _,
  map := λ X X' f,
  { app := λ Y,
    { to_fun := λ g, f.unop ≫ g,
      map_zero' := limits.comp_zero,
      map_add' := λ g g', comp_add _ _ _ _ _ _ },
    naturality' := λ Y Y' g, AddCommGroup.ext _ _ _ _ $ λ x, eq.symm $ category.assoc _ _ _ },
  map_id' := λ X, by { ext, simp },
  map_comp' := λ X Y Z f g, by { ext, simp } }

instance additive_yoneda_obj (X : C) : functor.additive (preadditive_yoneda_obj X) := {}
instance additive_yoneda_obj' (X : C) : functor.additive (preadditive_yoneda.obj X) := {}
instance additive_coyoneda_obj (X : Cᵒᵖ) : functor.additive (preadditive_coyoneda_obj X) := {}
instance additive_coyoneda_obj' (X : Cᵒᵖ) : functor.additive (preadditive_coyoneda.obj X) := {}

/--
Composing the preadditive yoneda embedding with the forgetful functor yields the regular
Yoneda embedding.
-/
@[simp] lemma whiskering_preadditive_yoneda : preadditive_yoneda ⋙
  (whiskering_right Cᵒᵖ AddCommGroup (Type v)).obj (forget AddCommGroup) = yoneda :=
rfl

/--
Composing the preadditive yoneda embedding with the forgetful functor yields the regular
Yoneda embedding.
-/
@[simp] lemma whiskering_preadditive_coyoneda : preadditive_coyoneda ⋙
  (whiskering_right C AddCommGroup (Type v)).obj (forget AddCommGroup) = coyoneda :=
rfl

instance preadditive_yoneda_full : full (preadditive_yoneda : C ⥤ Cᵒᵖ ⥤ AddCommGroup) :=
let yoneda_full : full (preadditive_yoneda ⋙
  (whiskering_right Cᵒᵖ AddCommGroup (Type v)).obj (forget AddCommGroup)) := yoneda.yoneda_full in
by exactI full.of_comp_faithful preadditive_yoneda
  ((whiskering_right Cᵒᵖ AddCommGroup (Type v)).obj (forget AddCommGroup))

instance preadditive_coyoneda_full : full (preadditive_coyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGroup) :=
let coyoneda_full : full (preadditive_coyoneda ⋙
  (whiskering_right C AddCommGroup (Type v)).obj (forget AddCommGroup)) :=
    coyoneda.coyoneda_full in
by exactI full.of_comp_faithful preadditive_coyoneda
  ((whiskering_right C AddCommGroup (Type v)).obj (forget AddCommGroup))

instance preadditive_yoneda_faithful : faithful (preadditive_yoneda : C ⥤ Cᵒᵖ ⥤ AddCommGroup) :=
faithful.of_comp_eq whiskering_preadditive_yoneda

instance preadditive_coyoneda_faithful :
  faithful (preadditive_coyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGroup) :=
faithful.of_comp_eq whiskering_preadditive_coyoneda

end category_theory
