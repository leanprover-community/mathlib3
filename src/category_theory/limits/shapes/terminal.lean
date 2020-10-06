/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.pempty
import category_theory.limits.limits

/-!
# Initial and terminal objects in a category.

## References
* [Stacks: Initial and final objects](https://stacks.math.columbia.edu/tag/002B)
-/

noncomputable theory

universes v u

open category_theory

namespace category_theory.limits

variables {C : Type u} [category.{v} C]

/-- Construct a cone for the empty diagram given an object. -/
@[simps] def as_empty_cone (X : C) : cone (functor.empty C) := { X := X, π := by tidy }
/-- Construct a cocone for the empty diagram given an object. -/
@[simps] def as_empty_cocone (X : C) : cocone (functor.empty C) := { X := X, ι := by tidy }

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
An arbitrary choice of terminal object, if one exists.
You can use the notation `⊤_ C`.
This object is characterized by having a unique morphism from any object.
-/
abbreviation terminal [has_terminal C] : C := limit (functor.empty C)
/--
An arbitrary choice of initial object, if one exists.
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
lemma has_terminal_of_unique (X : C) [h : Π Y : C, unique (Y ⟶ X)] : has_terminal C :=
{ has_limit := λ F, has_limit.mk
  { cone     := { X := X, π := { app := pempty.rec _ } },
    is_limit := { lift := λ s, (h s.X).default } } }

/-- We can more explicitly show that a category has an initial object by specifying the object,
and showing there is a unique morphism from it to any other object. -/
lemma has_initial_of_unique (X : C) [h : Π Y : C, unique (X ⟶ Y)] : has_initial C :=
{ has_colimit := λ F, has_colimit.mk
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

/-- A terminal object is terminal. -/
def terminal_is_terminal [has_terminal C] : is_terminal (⊤_ C) :=
{ lift := λ s, terminal.from _ }

/-- An initial object is initial. -/
def initial_is_initial [has_initial C] : is_initial (⊥_ C) :=
{ desc := λ s, initial.to _ }

/-- Any morphism from a terminal object is mono. -/
instance terminal.mono_from {Y : C} [has_terminal C] (f : ⊤_ C ⟶ Y) : mono f :=
is_terminal.mono_from terminal_is_terminal _

/-- Any morphism to an initial object is epi. -/
instance initial.epi_to {Y : C} [has_initial C] (f : Y ⟶ ⊥_ C) : epi f :=
is_initial.epi_to initial_is_initial _

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, construct a cone for `J`.
In `limit_of_diagram_initial` we show it is a limit cone. -/
@[simps]
def cone_of_diagram_initial {J : Type v} [small_category J]
  {X : J} (tX : is_initial X) (F : J ⥤ C) : cone F :=
{ X := F.obj X,
  π :=
  { app := λ j, F.map (tX.to j),
    naturality' := λ j j' k,
    begin
      dsimp,
      rw [← F.map_comp, category.id_comp, tX.hom_ext (tX.to j ≫ k) (tX.to j')],
    end } }

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, show the cone
`cone_of_diagram_initial` is a limit. -/
def limit_of_diagram_initial {J : Type v} [small_category J]
  {X : J} (tX : is_initial X) (F : J ⥤ C) :
is_limit (cone_of_diagram_initial tX F) :=
{ lift := λ s, s.π.app X,
  uniq' := λ s m w,
    begin
      rw [← w X, cone_of_diagram_initial_π_app, tX.hom_ext (tX.to X) (𝟙 _)],
      dsimp, simp -- See note [dsimp, simp]
    end}

-- This is reducible to allow usage of lemmas about `cone_point_unique_up_to_iso`.
/-- For a functor `F : J ⥤ C`, if `J` has an initial object then the image of it is isomorphic
to the limit of `F`. -/
@[reducible]
def limit_of_initial {J : Type v} [small_category J] (F : J ⥤ C)
  [has_initial J] [has_limit F] :
limit F ≅ F.obj (⊥_ J) :=
is_limit.cone_point_unique_up_to_iso
  (limit.is_limit _)
  (limit_of_diagram_initial initial_is_initial F)

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, construct a cocone for `J`.
In `colimit_of_diagram_terminal` we show it is a colimit cocone. -/
@[simps]
def cocone_of_diagram_terminal {J : Type v} [small_category J]
  {X : J} (tX : is_terminal X) (F : J ⥤ C) : cocone F :=
{ X := F.obj X,
  ι :=
  { app := λ j, F.map (tX.from j),
    naturality' := λ j j' k,
    begin
      dsimp,
      rw [← F.map_comp, category.comp_id, tX.hom_ext (k ≫ tX.from j') (tX.from j)],
    end } }

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, show the cocone
`cocone_of_diagram_terminal` is a colimit. -/
def colimit_of_diagram_terminal {J : Type v} [small_category J]
  {X : J} (tX : is_terminal X) (F : J ⥤ C) :
is_colimit (cocone_of_diagram_terminal tX F) :=
{ desc := λ s, s.ι.app X,
  uniq' := λ s m w,
    by { rw [← w X, cocone_of_diagram_terminal_ι_app, tX.hom_ext (tX.from X) (𝟙 _)], simp } }

-- This is reducible to allow usage of lemmas about `cocone_point_unique_up_to_iso`.
/-- For a functor `F : J ⥤ C`, if `J` has a terminal object then the image of it is isomorphic
to the colimit of `F`. -/
@[reducible]
def colimit_of_terminal {J : Type v} [small_category J] (F : J ⥤ C)
  [has_terminal J] [has_colimit F] :
colimit F ≅ F.obj (⊤_ J) :=
is_colimit.cocone_point_unique_up_to_iso
  (colimit.is_colimit _)
  (colimit_of_diagram_terminal terminal_is_terminal F)

end

end category_theory.limits
