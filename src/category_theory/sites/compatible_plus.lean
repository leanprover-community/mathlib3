/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.sites.whiskering
import category_theory.sites.plus

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.


In this file, we prove that the plus functor is compatible with functors which
preserve the correct limits and colimits.

See `category_theory/sites/compatible_sheafification` for the compatibility
of sheafification, which follows easily from the content in this file.

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

variables [∀ (α β : Type (max v u)) (fst snd : β → α),
  has_limits_of_shape (walking_multicospan fst snd) D]
variables [∀ (α β : Type (max v u)) (fst snd : β → α),
  has_limits_of_shape (walking_multicospan fst snd) E]
variables [∀ (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D), preserves_limit (W.index P).multicospan F]

variables (P : Cᵒᵖ ⥤ D)

/-- The diagram used to define `P⁺`, composed with `F`, is isomorphic
to the diagram used to define `P ⋙ F`. -/
def diagram_comp_iso (X : C) : J.diagram P X ⋙ F ≅ J.diagram (P ⋙ F) X :=
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

@[simp, reassoc]
lemma diagram_comp_iso_hom_ι (X : C) (W : (J.cover X)ᵒᵖ) (i : W.unop.arrow):
  (J.diagram_comp_iso F P X).hom.app W ≫ multiequalizer.ι _ i =
  F.map (multiequalizer.ι _ _) :=
begin
  delta diagram_comp_iso,
  dsimp,
  simp,
end

variables [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]
variables [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ E]
variables [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ F]

/-- The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`. -/
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
  dsimp [plus_obj, plus_map],
  simp only [functor.map_comp, category.assoc],
  slice_rhs 1 2
  { erw (is_colimit_of_preserves F (colimit.is_colimit (J.diagram P X.unop))).fac },
  slice_lhs 1 3
  { simp only [← F.map_comp],
    dsimp [colim_map, is_colimit.map, colimit.pre],
    simp only [colimit.ι_desc_assoc, colimit.ι_desc],
    dsimp [cocones.precompose],
    rw [category.assoc, colimit.ι_desc],
    dsimp [cocone.whisker],
    rw F.map_comp },
  simp only [category.assoc],
  slice_lhs 2 3
  { erw (is_colimit_of_preserves F (colimit.is_colimit (J.diagram P Y.unop))).fac },
  dsimp,
  simp only [has_colimit.iso_of_nat_iso_ι_hom_assoc,
    grothendieck_topology.diagram_pullback_app, colimit.ι_pre,
    has_colimit.iso_of_nat_iso_ι_hom, ι_colim_map_assoc],
  simp only [← category.assoc],
  congr' 1,
  ext,
  dsimp,
  simp only [category.assoc],
  erw [multiequalizer.lift_ι, diagram_comp_iso_hom_ι, diagram_comp_iso_hom_ι,
    ← F.map_comp, multiequalizer.lift_ι],
end

@[simp, reassoc]
lemma ι_plus_comp_iso_hom (X) (W) : F.map (colimit.ι _ W) ≫ (J.plus_comp_iso F P).hom.app X =
  (J.diagram_comp_iso F P X.unop).hom.app W ≫ colimit.ι _ W :=
begin
  delta diagram_comp_iso plus_comp_iso,
  simp only [is_colimit.desc_cocone_morphism_hom, is_colimit.unique_up_to_iso_hom,
    cocones.forget_map, iso.trans_hom, nat_iso.of_components_hom_app, functor.map_iso_hom,
    ← category.assoc],
  erw (is_colimit_of_preserves F (colimit.is_colimit (J.diagram P (unop X)))).fac,
  simp only [category.assoc, has_limit.iso_of_nat_iso_hom_π, iso.symm_hom,
    cover.multicospan_comp_hom_inv_left, eq_to_hom_refl, category.comp_id,
    limit.cone_point_unique_up_to_iso_hom_comp, functor.map_cone_π_app,
    multiequalizer.multifork_π_app_left, multiequalizer.lift_ι, functor.map_comp, eq_self_iff_true,
    category.assoc, iso.trans_hom, iso.cancel_iso_hom_left, nat_iso.of_components_hom_app,
    colimit.cocone_ι, category.assoc, has_colimit.iso_of_nat_iso_ι_hom],

end

@[simp, reassoc]
lemma plus_comp_iso_whisker_left {F G : D ⥤ E} (η : F ⟶ G) (P : Cᵒᵖ ⥤ D)
  [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ F]
  [∀ (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D), preserves_limit (W.index P).multicospan F]
  [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ G]
  [∀ (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D), preserves_limit (W.index P).multicospan G] :
  whisker_left _ η ≫ (J.plus_comp_iso G P).hom =
  (J.plus_comp_iso F P).hom ≫ J.plus_map (whisker_left _ η) :=
begin
  ext X,
  apply (is_colimit_of_preserves F (colimit.is_colimit (J.diagram P X.unop))).hom_ext,
  intros W,
  dsimp [plus_obj, plus_map],
  simp only [ι_plus_comp_iso_hom, ι_colim_map, whisker_left_app, ι_plus_comp_iso_hom_assoc,
    nat_trans.naturality_assoc, grothendieck_topology.diagram_nat_trans_app],
  simp only [← category.assoc],
  congr' 1,
  ext,
  dsimp,
  simpa,
end

/-- The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`, functorially in `F`. -/
@[simps hom_app inv_app]
def plus_functor_whisker_left_iso (P : Cᵒᵖ ⥤ D)
  [∀ (F : D ⥤ E) (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ F]
  [∀ (F : D ⥤ E) (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D),
    preserves_limit (W.index P).multicospan F] :
  (whiskering_left _ _ E).obj (J.plus_obj P) ≅
  (whiskering_left _ _ _).obj P ⋙ J.plus_functor E :=
nat_iso.of_components
(λ X, plus_comp_iso _ _ _) $ λ F G η, plus_comp_iso_whisker_left _ _ _

@[simp, reassoc]
lemma plus_comp_iso_whisker_right {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
  whisker_right (J.plus_map η) F ≫ (J.plus_comp_iso F Q).hom =
  (J.plus_comp_iso F P).hom ≫ J.plus_map (whisker_right η F) :=
begin
  ext X,
  apply (is_colimit_of_preserves F (colimit.is_colimit (J.diagram P X.unop))).hom_ext,
  intros W,
  dsimp [plus_obj, plus_map],
  simp only [ι_colim_map, whisker_right_app, ι_plus_comp_iso_hom_assoc,
    grothendieck_topology.diagram_nat_trans_app],
  simp only [← category.assoc, ← F.map_comp],
  dsimp [colim_map, is_colimit.map],
  simp only [colimit.ι_desc],
  dsimp [cocones.precompose],
  simp only [functor.map_comp, category.assoc, ι_plus_comp_iso_hom],
  simp only [← category.assoc],
  congr' 1,
  ext,
  dsimp,
  simp only [diagram_comp_iso_hom_ι_assoc, multiequalizer.lift_ι,
    diagram_comp_iso_hom_ι, category.assoc],
  simp only [← F.map_comp, multiequalizer.lift_ι],
end

/-- The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`, functorially in `P`. -/
@[simps hom_app inv_app]
def plus_functor_whisker_right_iso : J.plus_functor D ⋙ (whiskering_right _ _ _).obj F ≅
  (whiskering_right _ _ _).obj F ⋙ J.plus_functor E :=
nat_iso.of_components (λ P, J.plus_comp_iso _ _) $ λ P Q η, plus_comp_iso_whisker_right _ _ _

@[simp, reassoc]
lemma whisker_right_to_plus_comp_plus_comp_iso_hom :
  whisker_right (J.to_plus _) _ ≫ (J.plus_comp_iso F P).hom = J.to_plus _ :=
begin
  ext,
  dsimp [to_plus],
  simp only [ι_plus_comp_iso_hom, functor.map_comp, category.assoc],
  simp only [← category.assoc],
  congr' 1,
  ext,
  delta cover.to_multiequalizer,
  simp only [diagram_comp_iso_hom_ι, category.assoc, ← F.map_comp],
  erw [multiequalizer.lift_ι, multiequalizer.lift_ι],
  refl,
end

@[simp]
lemma to_plus_comp_plus_comp_iso_inv : J.to_plus _ ≫ (J.plus_comp_iso F P).inv =
  whisker_right (J.to_plus _) _ :=
by simp [iso.comp_inv_eq]

lemma plus_comp_iso_inv_eq_plus_lift (hP : presheaf.is_sheaf J ((J.plus_obj P) ⋙ F)) :
  (J.plus_comp_iso F P).inv = J.plus_lift (whisker_right (J.to_plus _) _) hP :=
by { apply J.plus_lift_unique, simp [iso.comp_inv_eq] }

end category_theory.grothendieck_topology
