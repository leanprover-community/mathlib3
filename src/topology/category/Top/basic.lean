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
def Top : Type (u+1) := bundled topological_space

namespace Top
local attribute [reducible] Top

-- Setup instances while `Top` is reducible:
instance : unbundled_hom @continuous := ⟨@continuous_id, @continuous.comp⟩
instance : concrete_category Top.{u} := infer_instance
instance (X : Top) : topological_space X := X.str
instance : has_coe_to_sort Top.{u} := infer_instance
instance (X Y : Top.{u}) : has_coe_to_fun (X ⟶ Y) := concrete_category.has_coe_to_fun

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
