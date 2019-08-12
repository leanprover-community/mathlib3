import topology.Top.presheaf

universes v u

open category_theory
open category_theory.limits
open topological_space
open opposite

namespace Top

variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞
variables {X : Top.{v}}

-- def plus_obj (ℱ : X.presheaf C) : X.presheaf C :=
-- { obj := sorry,
--   map := sorry }

end Top
