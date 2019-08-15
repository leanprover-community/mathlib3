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
limit.lift ((unop d).diagram ⋙ F)
{ X := limit ((unop c).diagram ⋙ F),
  π :=
  { app := λ j,
    begin
      dsimp,
      transitivity,
      { apply limit.π,
        exact (intersections.map f.unop.s).obj j },
      { dsimp,
        apply F.map,
        exact (intersections.map_diagram f.unop).app j,
      }
    end,
    naturality' := λ j j' g,
    begin
      cases j; cases j'; cases g,
      { dsimp, simp only [category.id_comp, category.assoc], rw ←F.map_comp, congr, },
      { dsimp, simp only [category.id_comp, category.assoc],
        rw [←F.map_comp, ←nat_trans.naturality, F.map_comp, ←category.assoc], erw limit.w, refl, },
      { dsimp, simp only [category.id_comp, category.assoc],
        rw [←F.map_comp, ←nat_trans.naturality, F.map_comp, ←category.assoc], erw limit.w, refl, },
      { dsimp, simp only [category.id_comp, category.assoc], rw ←F.map_comp, congr, },
    end } }.

local attribute [simp] cech_zero_map

def cech_zero : (cover X)ᵒᵖ ⥤ C :=
{ obj := cech_zero_obj F,
  map := cech_zero_map F,
  map_id' := λ 𝒰,
  begin
    dsimp, ext, dsimp, simp only [limit.lift_π],
    erw [category.id_comp, intersections.map_diagram_id, limit.w],
  end,
  map_comp' := sorry, }

end Top.presheaf
