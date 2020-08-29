/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.pempty
import category_theory.limits.limits

/-!
# Initial and terminal objects in a category.
-/

universes v u

open category_theory

namespace category_theory.limits

variables {C : Type u} [category.{v} C]

/-- Construct a cone for the empty diagram given an object. -/
def as_empty_cone (X : C) : cone (functor.empty C) := { X := X, π := by tidy }
/-- Construct a cocone for the empty diagram given an object. -/
def as_empty_cocone (X : C) : cocone (functor.empty C) := { X := X, ι := by tidy }

/-- `X` is terminal if the cone it induces on the empty diagram is limiting. -/
abbreviation is_terminal (X : C) := is_limit (as_empty_cone X)
/-- `X` is initial if the cocone it induces on the empty diagram is colimiting. -/
abbreviation is_initial (X : C) := is_colimit (as_empty_cocone X)

/-- Give the morphism to a terminal object from any other. -/
def is_terminal.from {X : C} (t : is_terminal X) (Y : C) : Y ⟶ X :=
t.lift (as_empty_cone Y)

/-- Any two morphisms to a terminal object are equal. -/
lemma is_terminal.hom_ext {X Y : C} (t : is_terminal X) (f g : Y ⟶ X) : f = g :=
t.hom_ext (by tidy)

/-- Give the morphism from an initial object to any other. -/
def is_initial.to {X : C} (t : is_initial X) (Y : C) : X ⟶ Y :=
t.desc (as_empty_cocone Y)

/-- Any two morphisms from an initial object are equal. -/
lemma is_initial.hom_ext {X Y : C} (t : is_initial X) (f g : X ⟶ Y) : f = g :=
t.hom_ext (by tidy)

/-- Any morphism from a terminal object is mono. -/
lemma is_terminal.mono_from {X Y : C} (t : is_terminal X) (f : X ⟶ Y) : mono f :=
⟨λ Z g h eq, t.hom_ext _ _⟩

/-- Any morphism to an initial object is epi. -/
lemma is_initial.epi_to {X Y : C} (t : is_initial X) (f : Y ⟶ X) : epi f :=
⟨λ Z g h eq, t.hom_ext _ _⟩

variable (C)

/--
A category has a terminal object if it has a limit over the empty diagram.
Use `has_terminal_of_unique` to construct instances.
-/
abbreviation has_terminal := has_limits_of_shape (discrete pempty) C
/--
A category has an initial object if it has a colimit over the empty diagram.
Use `has_initial_of_unique` to construct instances.
-/
abbreviation has_initial := has_colimits_of_shape (discrete pempty) C

/--
The chosen terminal object, if it exists.
You can use the notation `⊤_ C`.
This object is characterized by having a unique morphism from any object.
-/
abbreviation terminal [has_terminal C] : C := limit (functor.empty C)
/--
The chosen initial object, if it exists.
You can use the notation `⊥_ C`.
This object is characterized by having a unique morphism to any object.
-/
abbreviation initial [has_initial C] : C := colimit (functor.empty C)

notation `⊤_` C:20 := terminal C
notation `⊥_` C:20 := initial C

section
variables {C}

/-- We can more explicitly show that a category has a terminal object by specifying the object,
and showing there is a unique morphism to it from any other object. -/
def has_terminal_of_unique (X : C) [h : Π Y : C, unique (Y ⟶ X)] : has_terminal C :=
{ has_limit := λ F,
  { cone     := { X := X, π := { app := pempty.rec _ } },
    is_limit := { lift := λ s, (h s.X).default } } }

/-- We can more explicitly show that a category has an initial object by specifying the object,
and showing there is a unique morphism from it to any other object. -/
def has_initial_of_unique (X : C) [h : Π Y : C, unique (X ⟶ Y)] : has_initial C :=
{ has_colimit := λ F,
  { cocone     := { X := X, ι := { app := pempty.rec _ } },
    is_colimit := { desc := λ s, (h s.X).default } } }

/-- The map from an object to the terminal object. -/
abbreviation terminal.from [has_terminal C] (P : C) : P ⟶ ⊤_ C :=
limit.lift (functor.empty C) (as_empty_cone P)
/-- The map to an object from the initial object. -/
abbreviation initial.to [has_initial C] (P : C) : ⊥_ C ⟶ P :=
colimit.desc (functor.empty C) (as_empty_cocone P)

instance unique_to_terminal [has_terminal C] (P : C) : unique (P ⟶ ⊤_ C) :=
{ default := terminal.from P,
  uniq := λ m, by { apply limit.hom_ext, rintro ⟨⟩ } }

instance unique_from_initial [has_initial C] (P : C) : unique (⊥_ C ⟶ P) :=
{ default := initial.to P,
  uniq := λ m, by { apply colimit.hom_ext, rintro ⟨⟩ } }

/-- The chosen terminal object is terminal. -/
def terminal_is_terminal [has_terminal C] : is_terminal (⊤_ C) :=
{ lift := λ s, terminal.from _ }

/-- The chosen initial object is terminal. -/
def initial_is_initial [has_initial C] : is_initial (⊥_ C) :=
{ desc := λ s, initial.to _ }

/-- Any morphism from a terminal object is mono. -/
instance terminal.mono_from {Y : C} [has_terminal C] (f : ⊤_ C ⟶ Y) : mono f :=
is_terminal.mono_from terminal_is_terminal _

/-- Any morphism to an initial object is epi. -/
instance initial.epi_to {Y : C} [has_initial C] (f : Y ⟶ ⊥_ C) : epi f :=
is_initial.epi_to initial_is_initial _

end

end category_theory.limits
