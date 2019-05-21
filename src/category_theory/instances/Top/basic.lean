-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Patrick Massot, Scott Morrison, Mario Carneiro

import category_theory.concrete_category
import category_theory.full_subcategory
import topology.opens

open category_theory
open topological_space

universe u

/-- The category of topological spaces and continuous maps. -/
@[reducible] def Top : Type (u+1) := bundled topological_space

namespace Top

instance topological_space_unbundled (x : Top) : topological_space x := x.str

instance concrete_category_continuous : concrete_category @continuous := ⟨@continuous_id, @continuous.comp⟩

def of (X : Type u) [topological_space X] : Top := ⟨X⟩

def discrete : Type u ⥤ Top.{u} :=
{ obj := λ X, ⟨X, ⊤⟩,
  map := λ X Y f, ⟨f, continuous_top⟩ }

def trivial : Type u ⥤ Top.{u} :=
{ obj := λ X, ⟨X, ⊥⟩,
  map := λ X Y f, ⟨f, continuous_bot⟩ }

end Top
