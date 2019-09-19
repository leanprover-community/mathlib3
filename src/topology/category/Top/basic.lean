/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro
-/
import category_theory.concrete_category.unbundled_hom
import topology.opens

open category_theory
open topological_space

universe u

/-- The category of topological spaces and continuous maps. -/
@[reducible] def Top : Type (u+1) := bundled topological_space

namespace Top

instance concrete_category_continuous : unbundled_hom @continuous :=
⟨@continuous_id, @continuous.comp⟩

instance topological_space_unbundled (x : Top) : topological_space x := x.str

instance hom_has_coe_to_fun (X Y : Top.{u}) : has_coe_to_fun (X ⟶ Y) :=
{ F := _, coe := subtype.val }

@[simp] lemma id_app (X : Top.{u}) (x : X) :
  @coe_fn (X ⟶ X) (Top.hom_has_coe_to_fun X X) (𝟙 X) x = x := rfl

/-- Construct a bundled `Top` from the underlying type and the typeclass. -/
def of (X : Type u) [topological_space X] : Top := ⟨X⟩

/-- The discrete topology on any type. -/
def discrete : Type u ⥤ Top.{u} :=
{ obj := λ X, ⟨X, ⊥⟩,
  map := λ X Y f, ⟨f, continuous_bot⟩ }

/-- The trivial topology on any type. -/
def trivial : Type u ⥤ Top.{u} :=
{ obj := λ X, ⟨X, ⊤⟩,
  map := λ X Y f, ⟨f, continuous_top⟩ }

end Top
