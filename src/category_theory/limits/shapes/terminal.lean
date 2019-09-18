/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.finite_products
import category_theory.pempty

/-!
# Initial and terminal objects in a category.
-/

universes v u

open category_theory

namespace category_theory.limits

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

/-- A category has a terminal object if it has a limit over the empty diagram. -/
-- Use `has_terminal_of_unique` to construct instances.
class has_terminal :=
(has_limits_of_shape : has_limits_of_shape.{v} pempty C)
/-- A category has an initial object if it has a colimit over the empty diagram. -/
-- Use `has_initial_of_unique` to construct instances.
class has_initial :=
(has_colimits_of_shape : has_colimits_of_shape.{v} pempty C)

attribute [instance] has_terminal.has_limits_of_shape has_initial.has_colimits_of_shape

instance has_terminal_of_has_finite_products [has_finite_products.{v} C] : has_terminal.{v} C :=
{ has_limits_of_shape :=
  { has_limit := λ F, has_limit_of_equivalence_comp ((functor.empty (discrete pempty)).as_equivalence.symm) } }
instance has_initial_of_has_finite_coproducts [has_finite_coproducts.{v} C] : has_initial.{v} C :=
{ has_colimits_of_shape :=
  { has_colimit := λ F, has_colimit_of_equivalence_comp ((functor.empty (discrete pempty)).as_equivalence.symm) } }

abbreviation terminal [has_terminal.{v} C] : C := limit (functor.empty C)
abbreviation initial [has_initial.{v} C] : C := colimit (functor.empty C)

notation `⊤_` C:20 := terminal C
notation `⊥_` C:20 := initial C

section
variables {C}

/-- We can more explicitly show that a category has a terminal object by specifying the object,
and showing there is a unique morphism to it from any other object. -/
def has_terminal_of_unique (X : C) [h : Π Y : C, unique (Y ⟶ X)] : has_terminal.{v} C :=
{ has_limits_of_shape :=
  { has_limit := λ F,
    { cone     := { X := X, π := { app := pempty.rec _ } },
      is_limit := { lift := λ s, (h s.X).default } } } }
/-- We can more explicitly show that a category has an initial object by specifying the object,
and showing there is a unique morphism from it to any other object. -/
def has_initial_of_unique (X : C) [h : Π Y : C, unique (X ⟶ Y)] : has_initial.{v} C :=
{ has_colimits_of_shape :=
  { has_colimit := λ F,
    { cocone     := { X := X, ι := { app := pempty.rec _ } },
      is_colimit := { desc := λ s, (h s.X).default } } } }

/-- The map from an object to the terminal object. -/
abbreviation terminal.from [has_terminal.{v} C] (P : C) : P ⟶ ⊤_ C :=
limit.lift (functor.empty C) { X := P, π := by tidy }.
/-- The map to an object from the initial object. -/
abbreviation initial.to [has_initial.{v} C] (P : C) : ⊥_ C ⟶ P :=
colimit.desc (functor.empty C) { X := P, ι := by tidy }.

instance unique_to_terminal [has_terminal.{v} C] (P : C) : unique (P ⟶ ⊤_ C) :=
{ default := terminal.from P,
  uniq := λ m, by { apply limit.hom_ext, rintro ⟨⟩ } }

instance unique_from_initial [has_initial.{v} C] (P : C) : unique (⊥_ C ⟶ P) :=
{ default := initial.to P,
  uniq := λ m, by { apply colimit.hom_ext, rintro ⟨⟩ } }
end

end category_theory.limits
