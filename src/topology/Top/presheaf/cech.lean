import topology.Top.presheaf.cover

open category_theory
open category_theory.limits
open opposite
open topological_space
open Top

universes v u

namespace Top.presheaf

open Top.cover

variables {X : Top.{v}}

variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞
variables [has_limits.{v} C]
variables (F : X.presheaf C)

def cech_zero_obj (c : (cover X)ᵒᵖ) := limit ((unop c).diagram ⋙ F)

def cech_zero_map (c d : (cover X)ᵒᵖ) (f : c ⟶ d) : cech_zero_obj F c ⟶ cech_zero_obj F d :=
limit.pre ((unop c).diagram ⋙ F) (intersections.map f.unop.s) ≫
  limits.lim.map (whisker_right (intersections.map_diagram f.unop) F)

@[simp, reassoc] lemma cech_zero_map_π (c d : (cover X)ᵒᵖ) (f : c ⟶ d) (j) :
  cech_zero_map F c d f ≫ limit.π (diagram (unop d) ⋙ F) j =
    limit.π ((unop c).diagram ⋙ F) ((intersections.map (f.unop.s)).obj j) ≫
      F.map ((intersections.map_diagram f.unop).app j) :=
by { dsimp [cech_zero_map], simp }

-- Unfortunately, propositional simp lemmas that involve inductive types don't seem to fire reliably
-- inside dependent (implicit) arguments. On the other hand, rfl-lemmas work fine, but this means we
-- need to run `cases` on the inductive types involved so that the rfl-lemmas actually apply. Hence
-- to prove the axioms here, we add `cases_intersection` to the list of tactics used by `tidy.
local attribute [tidy] cases_intersection
def cech_zero : (cover X)ᵒᵖ ⥤ C :=
{ obj := cech_zero_obj F,
  map := cech_zero_map F }

end Top.presheaf
