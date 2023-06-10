/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.limits.shapes.terminal

/-!

# `with_initial` and `with_terminal`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a category `C`, this file constructs two objects:
1. `with_terminal C`, the category built from `C` by formally adjoining a terminal object.
2. `with_initial C`, the category built from `C` by formally adjoining an initial object.

The terminal resp. initial object is `with_terminal.star` resp. `with_initial.star`, and
the proofs that these are terminal resp. initial are in `with_terminal.star_terminal`
and `with_initial.star_initial`.

The inclusion from `C` intro `with_terminal C` resp. `with_initial C` is denoted
`with_terminal.incl` resp. `with_initial.incl`.

The relevant constructions needed for the universal properties of these constructions are:
1. `lift`, which lifts `F : C ⥤ D` to a functor from `with_terminal C` resp. `with_initial C` in
  the case where an object `Z : D` is provided satisfying some additional conditions.
2. `incl_lift` shows that the composition of `lift` with `incl` is isomorphic to the
  functor which was lifted.
3. `lift_unique` provides the uniqueness property of `lift`.

In addition to this, we provide `with_terminal.map` and `with_initinal.map` providing the
functoriality of these constructions with respect to functors on the base categories.

-/

namespace category_theory

universes v u

variables (C : Type u) [category.{v} C]

/-- Formally adjoin a terminal object to a category. -/
@[derive inhabited]
inductive with_terminal : Type u
| of : C → with_terminal
| star : with_terminal

/-- Formally adjoin an initial object to a category. -/
@[derive inhabited]
inductive with_initial : Type u
| of : C → with_initial
| star : with_initial

namespace with_terminal

local attribute [tidy] tactic.case_bash
variable {C}

/-- Morphisms for `with_terminal C`. -/
@[simp, nolint has_nonempty_instance]
def hom : with_terminal C → with_terminal C → Type v
| (of X) (of Y) := X ⟶ Y
| star (of X) := pempty
| _ star := punit

/-- Identity morphisms for `with_terminal C`. -/
@[simp]
def id : Π (X : with_terminal C), hom X X
| (of X) := 𝟙 _
| star := punit.star

/-- Composition of morphisms for `with_terminal C`. -/
@[simp]
def comp : Π {X Y Z : with_terminal C}, hom X Y → hom Y Z → hom X Z
| (of X) (of Y) (of Z) := λ f g, f ≫ g
| (of X) _ star := λ f g, punit.star
| star (of X) _ := λ f g, pempty.elim f
| _ star (of Y) := λ f g, pempty.elim g
| star star star := λ _ _, punit.star

instance : category.{v} (with_terminal C) :=
{ hom := λ X Y, hom X Y,
  id := λ X, id _,
  comp := λ X Y Z f g, comp f g }

/-- The inclusion from `C` into `with_terminal C`. -/
def incl : C ⥤ (with_terminal C) :=
{ obj := of,
  map := λ X Y f, f }

instance : full (incl : C ⥤ _) :=
{ preimage := λ X Y f, f }

instance : faithful (incl : C ⥤ _) := {}

/-- Map `with_terminal` with respect to a functor `F : C ⥤ D`. -/
def map {D : Type*} [category D] (F : C ⥤ D) : with_terminal C ⥤ with_terminal D :=
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

instance {X : with_terminal C} : unique (X ⟶ star) :=
{ default :=
    match X with
    | of x := punit.star
    | star := punit.star
    end,
  uniq := by tidy }

/-- `with_terminal.star` is terminal. -/
def star_terminal : limits.is_terminal (star : with_terminal C) :=
limits.is_terminal.of_unique _

/-- Lift a functor `F : C ⥤ D` to `with_term C ⥤ D`. -/
@[simps]
def lift {D : Type*} [category D] {Z : D} (F : C ⥤ D) (M : Π (x : C), F.obj x ⟶ Z)
  (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) :
  (with_terminal C) ⥤ D :=
{ obj := λ X,
    match X with
    | of x := F.obj x
    | star := Z
    end,
  map := λ X Y f,
    match X, Y, f with
    | of x, of y, f := F.map f
    | of x, star, punit.star := M x
    | star, star, punit.star := 𝟙 Z
    end }

/-- The isomorphism between `incl ⋙ lift F _ _` with `F`. -/
@[simps]
def incl_lift {D : Type*} [category D] {Z : D} (F : C ⥤ D) (M : Π (x : C), F.obj x ⟶ Z)
  (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) :
  incl ⋙ lift F M hM ≅ F :=
{ hom := { app := λ X, 𝟙 _ },
  inv := { app := λ X, 𝟙 _ } }

/-- The isomorphism between `(lift F _ _).obj with_terminal.star` with `Z`. -/
@[simps]
def lift_star {D : Type*} [category D] {Z : D} (F : C ⥤ D) (M : Π (x : C), F.obj x ⟶ Z)
  (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) :
  (lift F M hM).obj star ≅ Z := eq_to_iso rfl

lemma lift_map_lift_star {D : Type*} [category D] {Z : D} (F : C ⥤ D) (M : Π (x : C), F.obj x ⟶ Z)
  (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x) (x : C) :
  (lift F M hM).map (star_terminal.from (incl.obj x)) ≫ (lift_star F M hM).hom =
  (incl_lift F M hM).hom.app x ≫ M x :=
begin
  erw [category.id_comp, category.comp_id],
  refl,
end

/-- The uniqueness of `lift`. -/
@[simp]
def lift_unique {D : Type*} [category D] {Z : D} (F : C ⥤ D)
  (M : Π (x : C), F.obj x ⟶ Z) (hM : ∀ (x y : C) (f : x ⟶ y), F.map f ≫ M y = M x)
  (G : with_terminal C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z)
  (hh : ∀ x : C, G.map (star_terminal.from (incl.obj x)) ≫ hG.hom = h.hom.app x ≫ M x) :
  G ≅ lift F M hM :=
nat_iso.of_components (λ X,
  match X with
  | of x := h.app x
  | star := hG
  end)
begin
  rintro (X|X) (Y|Y) f,
  { apply h.hom.naturality },
  { cases f, exact hh _ },
  { cases f, },
  { cases f,
    change G.map (𝟙 _) ≫ hG.hom = hG.hom ≫ 𝟙 _,
    simp }
end

/-- A variant of `lift` with `Z` a terminal object. -/
@[simps]
def lift_to_terminal {D : Type*} [category D] {Z : D} (F : C ⥤ D) (hZ : limits.is_terminal Z) :
  with_terminal C ⥤ D :=
lift F (λ x, hZ.from _) (λ x y f, hZ.hom_ext _ _)

/-- A variant of `incl_lift` with `Z` a terminal object. -/
@[simps]
def incl_lift_to_terminal {D : Type*} [category D] {Z : D} (F : C ⥤ D) (hZ : limits.is_terminal Z) :
  incl ⋙ lift_to_terminal F hZ ≅ F := incl_lift _ _ _

/-- A variant of `lift_unique` with `Z` a terminal object. -/
@[simps]
def lift_to_terminal_unique {D : Type*} [category D] {Z : D} (F : C ⥤ D) (hZ : limits.is_terminal Z)
  (G : with_terminal C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) :
  G ≅ lift_to_terminal F hZ :=
lift_unique F (λ z, hZ.from _) (λ x y f, hZ.hom_ext _ _) G h hG (λ x, hZ.hom_ext _ _)

/-- Constructs a morphism to `star` from `of X`. -/
@[simp]
def hom_from (X : C) : incl.obj X ⟶ star := star_terminal.from _

instance is_iso_of_from_star {X : with_terminal C} (f : star ⟶ X) : is_iso f :=
by tidy

end with_terminal

namespace with_initial

local attribute [tidy] tactic.case_bash
variable {C}

/-- Morphisms for `with_initial C`. -/
@[simp, nolint has_nonempty_instance]
def hom : with_initial C → with_initial C → Type v
| (of X) (of Y) := X ⟶ Y
| (of X) _ := pempty
| star _ := punit

/-- Identity morphisms for `with_initial C`. -/
@[simp]
def id : Π (X : with_initial C), hom X X
| (of X) := 𝟙 _
| star := punit.star

/-- Composition of morphisms for `with_initial C`. -/
@[simp]
def comp : Π {X Y Z : with_initial C}, hom X Y → hom Y Z → hom X Z
| (of X) (of Y) (of Z) := λ f g, f ≫ g
| star _ (of X) := λ f g, punit.star
| _ (of X) star := λ f g, pempty.elim g
| (of Y) star _ := λ f g, pempty.elim f
| star star star := λ _ _, punit.star

instance : category.{v} (with_initial C) :=
{ hom := λ X Y, hom X Y,
  id := λ X, id _,
  comp := λ X Y Z f g, comp f g }

/-- The inclusion of `C` into `with_initial C`. -/
def incl : C ⥤ (with_initial C) :=
{ obj := of,
  map := λ X Y f, f }

instance : full (incl : C ⥤ _) :=
{ preimage := λ X Y f, f }

instance : faithful (incl : C ⥤ _) := {}

/-- Map `with_initial` with respect to a functor `F : C ⥤ D`. -/
def map {D : Type*} [category D] (F : C ⥤ D) : with_initial C ⥤ with_initial D :=
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

instance {X : with_initial C} : unique (star ⟶ X) :=
{ default :=
    match X with
    | of x := punit.star
    | star := punit.star
    end,
  uniq := by tidy }

/-- `with_initial.star` is initial. -/
def star_initial : limits.is_initial (star : with_initial C) :=
limits.is_initial.of_unique _

/-- Lift a functor `F : C ⥤ D` to `with_initial C ⥤ D`. -/
@[simps]
def lift {D : Type*} [category D] {Z : D} (F : C ⥤ D) (M : Π (x : C), Z ⟶ F.obj x)
  (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) :
  (with_initial C) ⥤ D :=
{ obj := λ X,
    match X with
    | of x := F.obj x
    | star := Z
    end,
  map := λ X Y f,
    match X, Y, f with
    | of x, of y, f := F.map f
    | star, of x, punit.star := M _
    | star, star, punit.star := 𝟙 _
    end }

/-- The isomorphism between `incl ⋙ lift F _ _` with `F`. -/
@[simps]
def incl_lift {D : Type*} [category D] {Z : D} (F : C ⥤ D)
  (M : Π (x : C), Z ⟶ F.obj x) (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) :
  incl ⋙ lift F M hM ≅ F :=
{ hom := { app := λ X, 𝟙 _ },
  inv := { app := λ X, 𝟙 _ } }

/-- The isomorphism between `(lift F _ _).obj with_term.star` with `Z`. -/
@[simps]
def lift_star {D : Type*} [category D] {Z : D} (F : C ⥤ D)
  (M : Π (x : C), Z ⟶ F.obj x) (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) :
  (lift F M hM).obj star ≅ Z := eq_to_iso rfl

lemma lift_star_lift_map {D : Type*} [category D] {Z : D} (F : C ⥤ D)
  (M : Π (x : C), Z ⟶ F.obj x) (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y) (x : C) :
  (lift_star F M hM).hom ≫ (lift F M hM).map (star_initial.to (incl.obj x)) =
  M x ≫ (incl_lift F M hM).hom.app x :=
begin
  erw [category.id_comp, category.comp_id],
  refl,
end

/-- The uniqueness of `lift`. -/
@[simp]
def lift_unique {D : Type*} [category D] {Z : D} (F : C ⥤ D)
  (M : Π (x : C), Z ⟶ F.obj x) (hM : ∀ (x y : C) (f : x ⟶ y), M x ≫ F.map f = M y)
  (G : with_initial C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z)
  (hh : ∀ x : C, hG.symm.hom ≫ G.map (star_initial.to (incl.obj x)) = M x ≫ h.symm.hom.app x) :
  G ≅ lift F M hM :=
nat_iso.of_components
(λ X,
  match X with
  | of x := h.app x
  | star := hG
  end)
begin
  rintro (X|X) (Y|Y) f,
  { apply h.hom.naturality },
  { cases f, },
  { cases f,
    change G.map _ ≫ h.hom.app _ = hG.hom ≫ _,
    symmetry,
    erw [← iso.eq_inv_comp, ← category.assoc, hh],
    simpa },
  { cases f,
    change G.map (𝟙 _) ≫ hG.hom = hG.hom ≫ 𝟙 _,
    simp }
end

/-- A variant of `lift` with `Z` an initial object. -/
@[simps]
def lift_to_initial {D : Type*} [category D] {Z : D} (F : C ⥤ D) (hZ : limits.is_initial Z) :
  with_initial C ⥤ D :=
lift F (λ x, hZ.to _) (λ x y f, hZ.hom_ext _ _)

/-- A variant of `incl_lift` with `Z` an initial object. -/
@[simps]
def incl_lift_to_initial {D : Type*} [category D] {Z : D} (F : C ⥤ D) (hZ : limits.is_initial Z) :
  incl ⋙ lift_to_initial F hZ ≅ F := incl_lift _ _ _

/-- A variant of `lift_unique` with `Z` an initial object. -/
@[simps]
def lift_to_initial_unique {D : Type*} [category D] {Z : D} (F : C ⥤ D) (hZ : limits.is_initial Z)
  (G : with_initial C ⥤ D) (h : incl ⋙ G ≅ F) (hG : G.obj star ≅ Z) :
  G ≅ lift_to_initial F hZ :=
lift_unique F (λ z, hZ.to _) (λ x y f, hZ.hom_ext _ _) G h hG (λ x, hZ.hom_ext _ _)

/-- Constructs a morphism from `star` to `of X`. -/
@[simp]
def hom_to (X : C) : star ⟶ incl.obj X := star_initial.to _

instance is_iso_of_to_star {X : with_initial C} (f : X ⟶ star) : is_iso f :=
by tidy

end with_initial

end category_theory
