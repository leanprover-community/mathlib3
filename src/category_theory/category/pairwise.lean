/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import category_theory.limits.preserves.basic
import category_theory.limits.lattice

/-!
# The category of "pairwise intersections".

Given `ι : Type v`, we build the diagram category `pairwise ι`
with objects `single i` and `pair i j`, for `i j : ι`,
whose only non-identity morphisms are
`left : pair i j ⟶ single i` and `right : pair i j ⟶ single j`.

We use this later in describing (one formulation of) the sheaf condition.

Given any function `U : ι → α`, where `α` is some complete lattice (e.g. `(opens X)ᵒᵖ`),
we produce a functor `pairwise ι ⥤ α` in the obvious way,
and show that `supr U` provides a colimit cocone over this functor.
-/

noncomputable theory

universes v u

open category_theory
open category_theory.limits

namespace category_theory

/--
An inductive type representing either a single term of a type `ι`, or a pair of terms.
We use this as the objects of a category to describe the sheaf condition.
-/
inductive pairwise (ι : Type v)
| single : ι → pairwise
| pair : ι → ι → pairwise

variables {ι : Type v}

namespace pairwise

instance pairwise_inhabited [inhabited ι] : inhabited (pairwise ι) := ⟨single (default ι)⟩

/--
Morphisms in the category `pairwise ι`. The only non-identity morphisms are
`left i j : single i ⟶ pair i j` and `right i j : single j ⟶ pair i j`.
-/
inductive hom : pairwise ι → pairwise ι → Type v
| id_single : Π i, hom (single i) (single i)
| id_pair : Π i j, hom (pair i j) (pair i j)
| left : Π i j, hom (pair i j) (single i)
| right : Π i j, hom (pair i j) (single j)

open hom

instance hom_inhabited [inhabited ι] : inhabited (hom (single (default ι)) (single (default ι))) :=
⟨id_single (default ι)⟩

/--
The identity morphism in `pairwise ι`.
-/
def id : Π (o : pairwise ι), hom o o
| (single i) := id_single i
| (pair i j) := id_pair i j

/-- Composition of morphisms in `pairwise ι`. -/
def comp : Π {o₁ o₂ o₃ : pairwise ι} (f : hom o₁ o₂) (g : hom o₂ o₃), hom o₁ o₃
| _ _ _ (id_single i) g := g
| _ _ _ (id_pair i j) g := g
| _ _ _ (left i j) (id_single _) := left i j
| _ _ _ (right i j) (id_single _) := right i j

section
local attribute [tidy] tactic.case_bash

instance : category (pairwise ι) :=
{ hom := hom,
  id := id,
  comp := λ X Y Z f g, comp f g, }

end

variables {α : Type v} (U : ι → α)

section
variables [semilattice_inf α]

/-- Auxiliary definition for `diagram`. -/
@[simp]
def diagram_obj : pairwise ι → α
| (single i) := U i
| (pair i j) := U i ⊓ U j

/-- Auxiliary definition for `diagram`. -/
@[simp]
def diagram_map : Π {o₁ o₂ : pairwise ι} (f : o₁ ⟶ o₂), diagram_obj U o₁ ⟶ diagram_obj U o₂
| _ _ (id_single i) := 𝟙 _
| _ _ (id_pair i j) := 𝟙 _
| _ _ (left i j) := hom_of_le inf_le_left
| _ _ (right i j) := hom_of_le inf_le_right

/--
Given a function `U : ι → α` for `[semilattice_inf α]`, we obtain a functor `pairwise ι ⥤ α`,
sending `single i` to `U i` and `pair i j` to `U i ⊓ U j`,
and the morphisms to the obvious inequalities.
-/
@[simps]
def diagram : pairwise ι ⥤ α :=
{ obj := diagram_obj U,
  map := λ X Y f, diagram_map U f, }

end

section
-- `complete_lattice` is not really needed, as we only ever use `inf`,
-- but the appropriate structure has not been defined.
variables [complete_lattice α]

/-- Auxiliary definition for `cocone`. -/
def cocone_ι_app : Π (o : pairwise ι), diagram_obj U o ⟶ supr U
| (single i) := hom_of_le (le_supr U i)
| (pair i j) := hom_of_le inf_le_left ≫ hom_of_le (le_supr U i)

/--
Given a function `U : ι → α` for `[complete_lattice α]`,
`supr U` provides a cocone over `diagram U`.
-/
@[simps]
def cocone : cocone (diagram U) :=
{ X := supr U,
  ι := { app := cocone_ι_app U, } }

/--
Given a function `U : ι → α` for `[complete_lattice α]`,
`infi U` provides a limit cone over `diagram U`.
-/
def cocone_is_colimit : is_colimit (cocone U) :=
{ desc := λ s, hom_of_le
  begin
    apply complete_lattice.Sup_le,
    rintros _ ⟨j, rfl⟩,
    exact (s.ι.app (single j)).le
  end }

end

end pairwise

end category_theory
