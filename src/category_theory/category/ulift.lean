/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.category
import category_theory.equivalence

/-!
# Basic API for ulift

This file contains a very basic API for working with the categorical 
instance on `ulift C` where `C` is a type with a category instance.

1. `category_theory.ulift.up` is the functorial version of the usual `ulift.up`. 
2. `category_theory.ulift.down` is the functorial version of the usual `ulift.down`. 
3. `category_theory.ulift.equivalence` is the categorical equivalence between 
  `C` and `ulift C`.
-/

-- The order of the universes matters... yet again.
universes v u2 u1

namespace category_theory

variables {C : Type u1} [category.{v} C]

/-- The functorial version of `ulift.up`. -/
@[simps]
def ulift.up : C ⥤ (ulift.{u2} C) :=
{ obj := ulift.up,
  map := λ X Y f, f }

/-- The functorial version of `ulift.down`. -/
@[simps]
def ulift.down : (ulift.{u2} C) ⥤ C :=
{ obj := ulift.down,
  map := λ X Y f, f }

/-- The categorical equivalence between `C` and `ulift C`. -/
@[simps]
def ulift.equivalence : C ≌ (ulift.{u2} C) :=
{ functor := ulift.up,
  inverse := ulift.down,
  unit_iso :=
  { hom := 𝟙 _,
    inv := 𝟙 _ },
  counit_iso :=
  { hom :=
    { app := λ X, 𝟙 _,
      naturality' := λ X Y f, by {change f ≫ 𝟙 _ = 𝟙 _ ≫ f, simp} },
    inv :=
    { app := λ X, 𝟙 _,
      naturality' := λ X Y f, by {change f ≫ 𝟙 _ = 𝟙 _ ≫ f, simp} },
  hom_inv_id' := by {ext, change (𝟙 _) ≫ (𝟙 _) = 𝟙 _, simp},
  inv_hom_id' := by {ext, change (𝟙 _) ≫ (𝟙 _) = 𝟙 _, simp} },
  functor_unit_iso_comp' := λ X, by {change (𝟙 X) ≫ (𝟙 X) = 𝟙 X, simp} }

section ulift'

variables (D : Type u1) [small_category D]

-- We enforse a small category instance on `D` to be able to use `ulift'`.
/-- An alias for `ulift D`, used to lift a small category to a small category. -/
@[nolint nolint unused_arguments]
def ulift' := ulift.{u2} D

variables {D}

instance ulift'_inhabited [inhabited D] : inhabited (ulift' D) := by {unfold ulift', apply_instance}

@[simps]
instance : small_category (ulift'.{u2} D) :=
{ hom := λ X Y, ulift $ X.down ⟶ Y.down,
  id := λ X, _root_.ulift.up $ 𝟙 _,
  comp := λ X Y Z f g, _root_.ulift.up $ f.down ≫ g.down }

/-- A functorial version of ulift.up. -/
@[simps]
def ulift'.up : D ⥤ (ulift'.{u2} D) :=
{ obj := _root_.ulift.up,
  map := λ X Y, _root_.ulift.up }

/-- A functorial version of ulift.down. -/
@[simps]
def ulift'.down : (ulift'.{u2} D) ⥤ D :=
{ obj := _root_.ulift.down,
  map := λ X Y, _root_.ulift.down }

/-- The categorical equivalence between `C` and `ulift' C`. -/
@[simps]
def ulift'.equivalence {D : Type*} [small_category D] : D ≌ ulift'.{u2} D :=
{ functor := ulift'.up,
  inverse := ulift'.down,
  unit_iso :=
  { hom := { app := λ X, 𝟙 _ },
    inv := { app := λ X, 𝟙 _ } },
  counit_iso :=
  { hom := { app := λ X, _root_.ulift.up (𝟙 _) },
    inv := { app := λ X, _root_.ulift.up (𝟙 _) } } }

end ulift'

end category_theory
