/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.limits.shapes.terminal

/-!

# `with_init` and `with_term`

Given a category `C`, this file constructs two objects:
1. `with_term C`, the category built from `C` by formally adjoining a terminal object.
2. `with_init C`, the category built from `C` by formally adjoining an initial object.

The terminal resp. initial object is `with_term.star` resp. `with_init.star`, and 
the proofs that these are terminal resp. initial are in `with_term.star_terminal`
and `with_init.star_initial`.

The inclusion from `C` intro `with_term C` resp. `with_init C` is denoted
`with_term.incl` resp. `with_init.incl`.

The relevant constructions needed for the universal properties of these constructions are:
1. `lift`, which lifts `F : C ⥤ D` to a functor from `with_term C` resp. `with_init C` in
  the case where the user provides an object `Z : D` with an associated `is_terminal Z`
  resp. `is_initial Z`.
2. `incl_lift` shows that the composition of `lift` with `incl` is isomorphic to the
  functor which was lifted.
3. `lift_unique` provides the uniqueness property of `lift`.

In addition to this, we provide `with_term.map` and `with_init.map` providing the functoriality
of these constructions with respect to functors on the base categories.

-/

namespace category_theory

universes v u

variables (C : Type u) [category.{v} C]

/-- Formally adjoin a terminal object to a category. -/
@[derive inhabited]
inductive with_term : Type u
| of : C → with_term
| star : with_term

/-- Formally adjoin an initial object to a category. -/
@[derive inhabited]
inductive with_init : Type u
| of : C → with_init
| star : with_init

namespace with_term

local attribute [tidy] tactic.case_bash
variable {C}

/-- Morphisms for `with_term C`. -/
@[simp, nolint has_inhabited_instance]
def hom : with_term C → with_term C → Type v
| (of X) (of Y) := X ⟶ Y
| star (of X) := pempty
| _ star := punit

/-- Identity morphisms for `with_term C`. -/
@[simp]
def id : Π (X : with_term C), hom X X
| (of X) := 𝟙 _
| star := punit.star

/-- Composition of morphisms for `with_term C`. -/
@[simp]
def comp : Π {X Y Z : with_term C}, hom X Y → hom Y Z → hom X Z
| (of X) (of Y) (of Z) := λ f g, f ≫ g
| (of X) _ star := λ f g, punit.star
| star (of X) _ := λ f g, pempty.elim f
| _ star (of Y) := λ f g, pempty.elim g
| star star star := λ _ _, punit.star

instance : category.{v} (with_term C) :=
{ hom := λ X Y, hom X Y,
  id := λ X, id _,
  comp := λ X Y Z f g, comp f g }

/-- The inclusion from `C` into `with_term C`. -/
def incl : C ⥤ (with_term C) :=
{ obj := of,
  map := λ X Y f, f }

instance : full (incl : C ⥤ _) :=
{ preimage := λ X Y f, f }

instance : faithful (incl : C ⥤ _) := {}

/-- Map `with_term` with respect to a functor `F : C ⥤ D`. -/
def map {D : Type*} [category D] (F : C ⥤ D) : with_term C ⥤ with_term D :=
{ obj := λ X,
    match X with
    | of x := of $ F.obj x
    | star := star
    end,
  map := λ X Y f,
    match X, Y, f with
    | of x, of y, f := F.map f
    | of x, star, punit.star := punit.star
    | star, star, punit.star := punit.star
    end }

instance {X : with_term C} : unique (X ⟶ star) :=
{ default :=
    match X with
    | of x := punit.star
    | star := punit.star
    end,
  uniq := by tidy }

/-- `with_term.star` is terminal. -/
def star_terminal : limits.is_terminal (star : with_term C) :=
limits.is_terminal.of_unique _

/-- Lift a functor `F : C ⥤ D` to `with_term C ⥤ D`, given a terminal object of `D`. -/
@[simps]
def lift {D : Type*} [category D] {Z : D} (hZ : limits.is_terminal Z) (F : C ⥤ D) :
  (with_term C) ⥤ D :=
{ obj := λ X,
    match X with
    | of x := F.obj x
    | star := Z
    end,
  map := λ X Y f,
    match X, Y, f with
    | of x, of y, f := F.map f
    | of x, star, punit.star := hZ.from _
    | star, star, punit.star := hZ.from _
    end,
  map_id' := begin
    rintros (X|X),
    apply F.map_id,
    apply hZ.hom_ext,
  end,
  map_comp' := begin
    rintros (X|X) (Y|Y) (Z|Z) f g,
    any_goals {apply hZ.hom_ext},
    tidy,
  end }

/-- The isomorphism between `incl ⋙ lift _ F` with `F`. -/
@[simps]
def incl_lift {D : Type*} [category D] {Z : D} (hZ : limits.is_terminal Z) (F : C ⥤ D) :
  incl ⋙ lift hZ F ≅ F :=
{ hom := { app := λ X, 𝟙 _ },
  inv := { app := λ X, 𝟙 _ } }

/-- The uniqueness of `lift _ F`. -/
@[simps]
def lift_unique {D : Type*} [category D] {Z : D} (hZ : limits.is_terminal Z) (F : C ⥤ D)
  (G : with_term C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) : G ≅ lift hZ F :=
{ hom :=
  { app := λ X,
      match X with
      | of x := h.hom.app x
      | star := hG.hom
      end,
    naturality' := begin
      rintros (X|X) (Y|Y) f,
      any_goals {apply hZ.hom_ext},
      apply h.hom.naturality,
      cases f,
    end },
  inv :=
  { app := λ X,
      match X with
      | of x := h.symm.hom.app x
      | star := hG.symm.hom
      end,
    naturality' := begin
      rintros (X|X) (Y|Y) f,
      any_goals {apply (limits.is_terminal.of_iso hZ hG.symm).hom_ext},
      apply h.symm.hom.naturality,
      cases f,
    end },
  hom_inv_id' := by {ext (X|X), tidy},
  inv_hom_id' := by {ext (X|X), tidy} }

end with_term

namespace with_init

local attribute [tidy] tactic.case_bash
variable {C}

/-- Morphisms for `with_init C`. -/
@[simp, nolint has_inhabited_instance]
def hom : with_init C → with_init C → Type v
| (of X) (of Y) := X ⟶ Y
| (of X) _ := pempty
| star _ := punit

/-- Identity morphisms for `with_init C`. -/
@[simp]
def id : Π (X : with_init C), hom X X
| (of X) := 𝟙 _
| star := punit.star

/-- Composition of morphisms for `with_init C`. -/
@[simp]
def comp : Π {X Y Z : with_init C}, hom X Y → hom Y Z → hom X Z
| (of X) (of Y) (of Z) := λ f g, f ≫ g
| star _ (of X) := λ f g, punit.star
| _ (of X) star := λ f g, pempty.elim g
| (of Y) star _ := λ f g, pempty.elim f
| star star star := λ _ _, punit.star

instance : category.{v} (with_init C) :=
{ hom := λ X Y, hom X Y,
  id := λ X, id _,
  comp := λ X Y Z f g, comp f g }

/-- The inclusion of `C` into `with_init C`. -/
def incl : C ⥤ (with_init C) :=
{ obj := of,
  map := λ X Y f, f }

instance : full (incl : C ⥤ _) :=
{ preimage := λ X Y f, f }

instance : faithful (incl : C ⥤ _) := {}

/-- Map `with_init` with respect to a functor `F : C ⥤ D`. -/
def map {D : Type*} [category D] (F : C ⥤ D) : with_init C ⥤ with_init D :=
{ obj := λ X,
    match X with
    | of x := of $ F.obj x
    | star := star
    end,
  map := λ X Y f,
    match X, Y, f with
    | of x, of y, f := F.map f
    | star, of x, punit.star := punit.star
    | star, star, punit.star := punit.star
    end }

instance {X : with_init C} : unique (star ⟶ X) :=
{ default :=
    match X with
    | of x := punit.star
    | star := punit.star
    end,
  uniq := by tidy }

/-- `with_init.star` is initial. -/
def star_initial : limits.is_initial (star : with_init C) :=
limits.is_initial.of_unique _

/-- Lift a functor `F : C ⥤ D` to `with_init C ⥤ D`, given an initial object of `D`. -/
@[simps]
def lift {D : Type*} [category D] {Z : D} (hZ : limits.is_initial Z) (F : C ⥤ D) :
  (with_init C) ⥤ D :=
{ obj := λ X,
    match X with
    | of x := F.obj x
    | star := Z
    end,
  map := λ X Y f,
    match X, Y, f with
    | of x, of y, f := F.map f
    | star, of x, punit.star := hZ.to _
    | star, star, punit.star := hZ.to _
    end,
  map_id' := begin
    rintros (X|X),
    apply F.map_id,
    apply hZ.hom_ext,
  end,
  map_comp' := begin
    rintros (X|X) (Y|Y) (Z|Z) f g,
    any_goals {apply hZ.hom_ext},
    tidy,
  end }

/-- The isomorphism between `incl ⋙ lift _ F` with `F`. -/
@[simps]
def incl_lift {D : Type*} [category D] {Z : D} (hZ : limits.is_initial Z) (F : C ⥤ D) :
  incl ⋙ lift hZ F ≅ F :=
{ hom := { app := λ X, 𝟙 _ },
  inv := { app := λ X, 𝟙 _ } }

/-- The uniqueness of `lift _ F`. -/
@[simps]
def lift_unique {D : Type*} [category D] {Z : D} (hZ : limits.is_initial Z) (F : C ⥤ D)
  (G : with_init C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) : G ≅ lift hZ F :=
{ hom :=
  { app := λ X,
      match X with
      | of x := h.hom.app x
      | star := hG.hom
      end,
    naturality' := begin
      rintros (X|X) (Y|Y) f,
      apply h.hom.naturality,
      any_goals {apply (limits.is_initial.of_iso hZ hG.symm).hom_ext},
      cases f,
    end },
  inv :=
  { app := λ X,
      match X with
      | of x := h.symm.hom.app x
      | star := hG.symm.hom
      end,
    naturality' := begin
      rintros (X|X) (Y|Y) f,
      any_goals {apply hZ.hom_ext},
      apply h.symm.hom.naturality,
      cases f,
    end },
  hom_inv_id' := by {ext (X|X), tidy},
  inv_hom_id' := by {ext (X|X), tidy} }

end with_init

end category_theory
#lint
