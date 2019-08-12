import topology.Top.presheaf.cech

universes v u

open category_theory
open category_theory.limits
open topological_space
open opposite

namespace Top

variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞
variables [has_limits.{v} C]
variables {X : Top.{v}}

def plus_obj_obj_aux (ℱ : X.presheaf C) (U : (opens X)ᵒᵖ) : {c : cover X // c.total = unop U}ᵒᵖ ⥤ C :=
((full_subcategory_inclusion (λ c : cover X, c.total = unop U)).op ⋙ ℱ.cech_zero)

-- Uh oh... universes.

set_option pp.universes true
#check λ U : (opens X)ᵒᵖ, {c : cover X // c.total = unop U}ᵒᵖ

def plus_obj_obj (ℱ : X.presheaf C) (U : (opens X)ᵒᵖ) : C :=
colimit.{v} (plus_obj_obj_aux ℱ U)

def plus_obj (ℱ : X.presheaf C) : X.presheaf C :=
{ obj := plus_obj_obj ℱ,
  map := sorry }

end Top
