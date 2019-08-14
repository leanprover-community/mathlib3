import topology.Top.presheaf.cover

universes v u

open category_theory
open category_theory.limits
open topological_space
open opposite

namespace Top

open cover.intersections

variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞
variables {X : Top.{v}}

namespace presheaf
variables (F : X.presheaf C)

/--
The sheaf condition on a presheaf `F` asserts that `F` preserves limits for the
pairwise intersection diagram associated to any collection of open sets in `X`.
-/
def sheaf_condition := Π (c : cover.{v} X), preserves_limit c.diagram F
end presheaf

variables (C) (X)

/--
A sheaf is a presheaf satisfying the sheaf condition.
-/
structure sheaf : Type (max (v+1) u) :=
(F : X.presheaf C)
(condition : F.sheaf_condition)

instance preserves_limit_cover_diagram (c : cover.{v} X) (ℱ : sheaf.{v} C X) :
  preserves_limit c.diagram ℱ.F :=
ℱ.condition c
instance preserves_limit_cover_diagram_map
  {X Y : Top.{v}} (c : cover.{v} Y) (f : X ⟶ Y) (ℱ : sheaf.{v} C X) :
  preserves_limit (cover.diagram c ⋙ functor.op (opens.map f)) (ℱ.F) :=
begin
  apply limits.preserves_limit_of_iso (c.map_diagram f).symm,
  apply_instance
end

namespace sheaf

/--
Morphisms of sheaves are just morphisms of the underlying presheaves, so we
transfer the category structure using `induced_category.category`.
-/
instance category_sheaf (X : Top.{v}) : category (sheaf.{v} C X) :=
induced_category.category sheaf.F

/--
The pushforward of a sheaf is still a sheaf.
-/
def pushforward {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : sheaf.{v} C X) : sheaf.{v} C Y :=
{ F := f _* ℱ.F,
  condition := λ c, by { dsimp [presheaf.pushforward], apply_instance } }

infix ` _* `: 80 := pushforward

end sheaf

end Top
