import algebraic_geometry.presheafed_space
import topology.Top.limits

universes v u

open category_theory
open Top
open topological_space
open algebraic_geometry
open opposite

variables (C : Type u) [𝒞 : category.{v+1} C] (J : Type v) [small_category J]
include 𝒞

namespace algebraic_geometry.PresheafedSpace

def colimit (F : J ⥤ PresheafedSpace.{v} C) : PresheafedSpace.{v} C :=
{ to_Top := limits.colimit (F ⋙ PresheafedSpace.forget),
  𝒪 := sorry }

end algebraic_geometry.PresheafedSpace
