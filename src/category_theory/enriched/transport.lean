/-
-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
-/
import category_theory.enriched.enriched_over

universes v u

open category_theory

namespace category_theory

variables (V : Type (v+1)) [large_category V] [concrete_category V]
variables (W : Type (v+1)) [large_category W] [concrete_category W]
variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

namespace enriched_over

def transport [enriched_over V C] [has_forget₂ V W] : enriched_over W C :=
{ enriched_hom := λ X Y, (forget₂ V W).obj (X ⟶[V] Y),
  comp_left := λ X Y f Z, (forget₂ V W).map (comp_left V f Z),
  comp_right := λ X Y Z g, (forget₂ V W).map (comp_right V X g),
  enriched_hom_forget' := λ X Y, by simp,
  comp_left_forget' := λ X Y f Z,
  begin
    change _ ≫ (forget₂ V W ⋙ forget W).map _ ≫ _ = _,
    -- Much easier will be to modify `forget₂`
    -- to have a natural isomorphism,
    -- instead of an equality.
    sorry,
  end,
  comp_right_forget' := sorry, }

end enriched_over

end category_theory
