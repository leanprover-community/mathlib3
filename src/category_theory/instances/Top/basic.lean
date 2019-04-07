-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Patrick Massot, Scott Morrison, Mario Carneiro

import category_theory.concrete_category
import category_theory.full_subcategory
import topology.opens

open category_theory
open topological_space

universe u

namespace category_theory.instances

/-- The category of topological spaces and continuous maps. -/
@[reducible] def Top : Type (u+1) := bundled topological_space

instance topological_space_unbundled (x : Top) : topological_space x := x.str

namespace Top
instance concrete_category_continuous : concrete_category @continuous := ⟨@continuous_id, @continuous.comp⟩

def discrete : Type u ⥤ Top.{u} :=
{ obj := λ X, ⟨X, ⊤⟩,
  map := λ X Y f, ⟨f, continuous_top⟩ }

def trivial : Type u ⥤ Top.{u} :=
{ obj := λ X, ⟨X, ⊥⟩,
  map := λ X Y f, ⟨f, continuous_bot⟩ }
end Top

variables {X : Top.{u}}

instance opens_category : category.{u+1} (opens X) :=
{ hom  := λ U V, ulift (plift (U ≤ V)),
  id   := λ X, ⟨ ⟨ le_refl X ⟩ ⟩,
  comp := λ X Y Z f g, ⟨ ⟨ le_trans f.down.down g.down.down ⟩ ⟩ }

def open_nhds (x : X.α) := { U : opens X // x ∈ U }
instance open_nhds_category (x : X.α) : category.{u+1} (open_nhds x) := begin unfold open_nhds, apply_instance end

end category_theory.instances
