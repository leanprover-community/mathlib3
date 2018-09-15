-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Patrick Massot, Scott Morrison

import category_theory.full_subcategory
import analysis.topology.topological_space
import analysis.topology.continuity

open category_theory
universe u

namespace category_theory.examples

@[reducible] def Top : Type (u + 1) := Σ α : Type u, topological_space α

namespace Top
instance : concrete_category @continuous := ⟨@continuous_id, @continuous.comp⟩

instance : large_category Top := infer_instance

instance (X : Top) : topological_space X.1 := X.2

end Top

structure open_set (α : Type u) [X : topological_space α] : Type u :=
(s : set α)
(is_open : topological_space.is_open X s)

variables {α : Type*} [topological_space α]

namespace open_set
instance : has_coe (open_set α) (set α) := { coe := λ U, U.s }

instance : has_subset (open_set α) :=
{ subset := λ U V, U.s ⊆ V.s }

instance : preorder (open_set α) := by refine { le := (⊆), .. } ; tidy

instance open_sets : small_category (open_set α) := by apply_instance

instance : has_mem α (open_set α) :=
{ mem := λ a V, a ∈ V.s }

def nbhd (x : α) := { U : open_set α // x ∈ U }
def nbhds (x : α) : small_category (nbhd x) := begin unfold nbhd, apply_instance end

end open_set

end category_theory.examples
