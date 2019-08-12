import topology.Top.presheaf.cover

open category_theory
open category_theory.limits
open opposite
open topological_space
open Top

universes v u

namespace Top.presheaf

variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞
variables [has_limits.{v} C]
variables {X : Top.{v}}
variables (F : X.presheaf C)

def cech_zero_obj (c : (cover X)ᵒᵖ) := limit ((unop c).diagram ⋙ F)

def cech_zero_map {c d : (cover X)ᵒᵖ} (f : c ⟶ d) : cech_zero_obj F c ⟶ cech_zero_obj F d := sorry

def cech_zero : (cover X)ᵒᵖ ⥤ C :=
{ obj := cech_zero_obj F,
  map := sorry,
  map_id' := sorry,
  map_comp' := sorry, }

end Top.presheaf
