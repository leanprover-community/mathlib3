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

/-- We can transport enrichment along a forgetful functor `V ⥤ W`. -/
def transport [enriched_over V C] [has_forget₂ V W] : enriched_over W C :=
{ enriched_hom := λ X Y, (forget₂ V W).obj (X ⟶[V] Y),
  comp_left := λ X Y f Z, (forget₂ V W).map (comp_left V f Z),
  comp_right := λ X Y Z g, (forget₂ V W).map (comp_right V X g),
  enriched_hom_forget' := λ X Y, by simp,
  comp_left_forget' := λ X Y f Z,
  begin
    change _ ≫ (forget₂ V W ⋙ forget W).map _ ≫ _ = _,
    let i : forget₂ V W ⋙ forget W ≅ _ := eq_to_iso has_forget₂.forget_comp,
    rw ←nat_iso.naturality_1 i.symm,
    simp only [forget_map_eq_coe, eq_to_iso.inv, iso.symm_hom, iso.symm_inv,
      eq_to_hom_app, eq_to_hom_trans, eq_to_hom_trans_assoc, eq_to_iso.hom, category.assoc],
    exact enriched_over.comp_left_forget _ _ _ _,
  end,
  comp_right_forget' := λ X Y Z g,
  begin
    change _ ≫ (forget₂ V W ⋙ forget W).map _ ≫ _ = _,
    let i : forget₂ V W ⋙ forget W ≅ _ := eq_to_iso has_forget₂.forget_comp,
    rw ←nat_iso.naturality_1 i.symm,
    simp only [forget_map_eq_coe, eq_to_iso.inv, iso.symm_hom, iso.symm_inv,
      eq_to_hom_app, eq_to_hom_trans, eq_to_hom_trans_assoc, eq_to_iso.hom, category.assoc],
    exact enriched_over.comp_right_forget _ _ _ _,
  end, }

end enriched_over

end category_theory
