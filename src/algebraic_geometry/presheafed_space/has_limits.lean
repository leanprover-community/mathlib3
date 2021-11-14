/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import algebraic_geometry.presheafed_space
import topology.category.Top.limits
import topology.sheaves.limits
import category_theory.limits.concrete_category

/-!
# `PresheafedSpace C` has limits.

If `C` has colimits, then the category `PresheafedSpace C` has limits,
and the forgetful functor to `Top` preserves these colimits.

Given a diagram `F : J ⥤ PresheafedSpace C`,
we first build the limit of the underlying topological spaces,
as `limit (F ⋙ PresheafedSpace.forget C)`. Call that limit space `X`.

Our strategy is to pull each of the presheaves `F.obj j`
back along the continuous map `limit.ι (F ⋙ PresheafedSpace.forget C) j` to `X`.
Since pullback is functorial, we obtain a diagram `J ⥤ (presheaf C X)ᵒᵖ`
of presheaves on a single space `X`.
(Note that the arrows now point the other direction,
because this is the way `PresheafedSpace C` is set up.)

The colimit of this diagram then constitutes the limit presheaf.
-/

noncomputable theory

universes v u

open category_theory
open Top
open Top.presheaf
open topological_space
open opposite
open category_theory.category
open category_theory.limits
open category_theory.functor

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v} C] [has_colimits C]


namespace algebraic_geometry

namespace PresheafedSpace

/-
def pushforward_diagram_to_colimit (F : J ⥤ PresheafedSpace C) :
  J ⥤ (presheaf C (limit (F ⋙ PresheafedSpace.forget C)))ᵒᵖ :=
{ obj := λ j, op (pullback_obj (limit.π (F ⋙ PresheafedSpace.forget C) j) (F.obj j).presheaf),
  map := λ j j' f, by {  }
}-/


end PresheafedSpace

end algebraic_geometry
