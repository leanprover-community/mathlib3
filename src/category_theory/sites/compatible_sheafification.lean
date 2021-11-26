/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.sites.sheafification
import category_theory.sites.whiskering

/-!

In this file, we prove that sheafification is compatible with functors which
preserve the correct limits and colimits.

-/

namespace category_theory.grothendieck_topology

open category_theory
open category_theory.limits
open opposite

universes w₁ w₂ v u
variables {C : Type u} [category.{v} C] (J : grothendieck_topology C)
variables {D : Type w₁} [category.{max v u} D]
variables {E : Type w₂} [category.{max v u} E]
variables (F : D ⥤ E)

noncomputable theory

variables [∀ (α β) (fst snd : β → α), has_limits_of_shape (walking_multicospan fst snd) D]
variables [∀ (α β) (fst snd : β → α), has_limits_of_shape (walking_multicospan fst snd) E]
variables [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]
variables [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ E]
variables [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ F]
variables [∀ (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D), preserves_limit (W.index P).multicospan F]

variables (P : Cᵒᵖ ⥤ D)

@[simps]
lemma diagram_comp_iso (X : C) : J.diagram P X ⋙ F ≅ J.diagram (P ⋙ F) X :=
nat_iso.of_components
(λ W, begin
  refine _ ≪≫ has_limit.iso_of_nat_iso (W.unop.multicospan_comp _ _).symm,
  refine (is_limit_of_preserves F (limit.is_limit _)).cone_point_unique_up_to_iso
    (limit.is_limit _)
end) begin
  intros A B f,
  ext,
  dsimp,
  simp only [functor.map_cone_π_app, multiequalizer.multifork_π_app_left,
    iso.symm_hom, multiequalizer.lift_ι, eq_to_hom_refl, category.comp_id,
    limit.cone_point_unique_up_to_iso_hom_comp,
    grothendieck_topology.cover.multicospan_comp_hom_inv_left,
    has_limit.iso_of_nat_iso_hom_π, category.assoc],
  simp only [← F.map_comp, multiequalizer.lift_ι],
end

def plus_comp_iso : J.plus_obj P ⋙ F ≅ J.plus_obj (P ⋙ F) :=
nat_iso.of_components
(λ X, begin
  refine _ ≪≫ has_colimit.iso_of_nat_iso (J.diagram_comp_iso F P X.unop),
  refine (is_colimit_of_preserves F (colimit.is_colimit
    (J.diagram P (unop X)))).cocone_point_unique_up_to_iso (colimit.is_colimit _)
end) begin
  intros X Y f,
  apply (is_colimit_of_preserves F (colimit.is_colimit (J.diagram P X.unop))).hom_ext,
  intros W,
  dsimp [colimit.pre, colim_map, is_colimit.map],
  simp only [← functor.map_comp, ← category.assoc, colimit.ι_desc,
    cocones.precompose_obj_ι],
  dsimp [is_colimit.cocone_point_unique_up_to_iso],
  erw (is_colimit_of_preserves F (colimit.is_colimit (J.diagram P X.unop))).fac,
  simp only [category.assoc, colimit.ι_desc],
  dsimp [cocone.whisker_ι, whisker_left],
  rw [F.map_comp, category.assoc],
  slice_lhs 2 3 { erw (is_colimit_of_preserves F (colimit.is_colimit (J.diagram P Y.unop))).fac },
  dsimp [has_colimit.iso_of_nat_iso, is_colimit.map],
  simp only [category.assoc, colimit.ι_desc, colimit.ι_desc_assoc],
  dsimp [cocones.precompose],
  simp only [cocone.whisker_ι, grothendieck_topology.diagram_pullback_app, colimit.cocone_ι,
    whisker_left_app, colimit.ι_desc, colimit.ι_desc_assoc, nat_trans.comp_app, category.assoc],
  simp only [← category.assoc],
  congr' 1,
  ext,
  dsimp,
  simp only [category.assoc, multiequalizer.lift_ι, diagram_comp_iso_hom_app],
  dsimp [is_limit.cone_point_unique_up_to_iso, has_limit.iso_of_nat_iso,
    cones.postcompose, is_limit.map],
  delta multiequalizer.ι,
  simp only [limit.lift_π],
  dsimp,
  simp only [category.comp_id, limit.lift_π],
  dsimp [functor.map_cone],
  simp only [← F.map_comp, multiequalizer.lift_ι],
end

lemma plus_comp_iso_whisker {F G : D ⥤ E} (η : F ⟶ G) (P : Cᵒᵖ ⥤ D)
  [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ F]
  [∀ (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D), preserves_limit (W.index P).multicospan F]
  [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ G]
  [∀ (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D), preserves_limit (W.index P).multicospan G] :
  (J.plus_comp_iso F P).hom ≫ J.plus_map (whisker_left _ η) =
  whisker_left _ η ≫ (J.plus_comp_iso G P).hom := sorry

end category_theory.grothendieck_topology
