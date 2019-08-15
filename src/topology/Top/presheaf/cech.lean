import topology.Top.presheaf.cover

open category_theory
open category_theory.limits
open opposite
open topological_space
open Top

universes v u

namespace Top.presheaf

variables {X : Top.{v}}

lemma foo {c d : cover X} (f : d ⟶ c) (j : cover.intersections (d.ι)) :
 (c.diagram.obj (cover.intersections.map._match_1 (f.s) j) ⟶
    (d.diagram.obj j :=
begin
  rcases j with j | ⟨j₁,j₂⟩,
  dsimp,
  exact (f.unop.r j).op,
  dsimp,
  apply has_hom.hom.op,
  -- yuck!
  exact ⟨⟨opens.inter_subset_inter (f.unop.r j₁).down.down (f.unop.r j₂).down.down⟩⟩
end


variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞
variables [has_limits.{v} C]
variables (F : X.presheaf C)

def cech_zero_obj (c : (cover X)ᵒᵖ) := limit ((unop c).diagram ⋙ F)

-- example (A B C D : opens X) (h₁ : A ⊆ B) (h₂ : C ⊆ D) : A ⊓ C ⊆ B ⊓ D := by library_search


def cech_zero_map (c d : (cover X)ᵒᵖ) (f : c ⟶ d) : cech_zero_obj F c ⟶ cech_zero_obj F d :=
limit.lift ((unop d).diagram ⋙ F)
{ X := limit ((unop c).diagram ⋙ F),
  π :=
  { app := λ j,
    begin
      dsimp,
      transitivity,
      { apply limit.π,
        exact (cover.intersections.map f.unop.s).obj j },
      { dsimp,
        apply F.map,
        exact foo f j,
      }
    end,
    naturality' := sorry } }

#exit

def cech_zero : (cover X)ᵒᵖ ⥤ C :=
{ obj := cech_zero_obj F,
  map := cech_zero_map F,
  map_id' := sorry,
  map_comp' := sorry, }

end Top.presheaf
