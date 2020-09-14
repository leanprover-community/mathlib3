/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.presheaf
import category_theory.limits.limits

universes v u

noncomputable theory

open category_theory
open category_theory.limits
open topological_space
open opposite
open topological_space.opens

namespace Top

variables {C : Type u} [category.{v} C] [has_limits C]
variables {X : Top.{v}} (F : presheaf C X) {ι : Type v} (U : ι → opens X)

namespace sheaf_condition

/--
The category of open sets contained in some element of the cover.
-/
@[derive category]
def opens_le_cover : Type v := { V : opens X // ∃ i, V ≤ U i }

/--
`supr U` as a cocone over the opens sets contained in some element of the cover.

(In fact this is a colimit cocone.)
-/
def opens_le_cover_cone : cocone (full_subcategory_inclusion _ : opens_le_cover U ⥤ opens X) :=
{ X := supr U,
  ι := { app := λ V, hom_of_le (by { obtain ⟨V, i, h⟩ := V, exact le_trans h (le_supr U i), }) } }

end sheaf_condition

open sheaf_condition

@[derive subsingleton]
def sheaf_condition' : Type (max u (v+1)) :=
Π ⦃ι : Type v⦄ (U : ι → opens X), is_limit (F.map_cone (opens_le_cover_cone U).op)

-- It seems that proving this is equivalent to the usual sheaf condition should use cofinality.

end Top
