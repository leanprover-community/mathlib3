/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.sites.sheafification
import category_theory.limits.functor_category
import category_theory.limits.filtered_colimit_commutes_finite_limit

/-!

# Left exactness of sheafification

In this file we show that sheafification commutes with finite limits.

-/
namespace category_theory.grothendieck_topology

open category_theory
open category_theory.limits
open opposite

universes w v u
variables {C : Type (max v u)} [category.{v} C] {J : grothendieck_topology C}
variables {D : Type w} [category.{max v u} D]
variables {K : Type (max v u)} [small_category K]
variables [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), has_multiequalizer (S.index P)]

noncomputable theory

instance (X : C) (K : Type (max v u)) [small_category K] [has_limits_of_shape K D]
  (F : K ⥤ Cᵒᵖ ⥤ D) : preserves_limit F (J.diagram_functor D X) :=
preserves_limit_of_evaluation _ _ $ λ W,
preserves_limit_of_preserves_limit_cone (limit.is_limit _)
{ lift := λ E, multiequalizer.lift _ _ (λ i,
    (is_limit_of_preserves ((evaluation _ _).obj (op i.Y)) (limit.is_limit F)).lift
    ⟨_,λ k, E.π.app k ≫ multiequalizer.ι _ i, begin
      intros a b f,
      dsimp,
      rw [category.id_comp, category.assoc, ← E.w f],
      dsimp [diagram_nat_trans],
      simp only [multiequalizer.lift_ι, category.assoc],
    end⟩) begin
      intros i,
      change (_ ≫ _) ≫ _ = (_ ≫ _) ≫ _,
      dsimp [evaluate_combined_cones],
      erw [category.comp_id, category.comp_id, category.assoc,
        category.assoc, ← (limit.lift F _).naturality, ← (limit.lift F _).naturality,
        ← category.assoc, ← category.assoc],
      congr' 1, ext1,
      erw [category.assoc, category.assoc, limit.lift_π, limit.lift_π,
        limit.lift_π_assoc, limit.lift_π_assoc, category.assoc,
        category.assoc, multiequalizer.condition],
      refl,
    end,
  fac' := begin
    intros E k,
    dsimp [diagram_nat_trans],
    ext1,
    simp only [multiequalizer.lift_ι, multiequalizer.lift_ι_assoc, category.assoc],
    change (_ ≫ _) ≫ _ = _,
    dsimp [evaluate_combined_cones],
    erw [category.comp_id, category.assoc, ← nat_trans.comp_app, limit.lift_π, limit.lift_π],
  end,
  uniq' := begin
    intros E m hm,
    ext,
    simp only [category.assoc, multiequalizer.lift_ι],
    change _ = (_ ≫ _) ≫ _,
    dsimp [evaluate_combined_cones],
    erw [category.comp_id, category.assoc, ← nat_trans.comp_app, limit.lift_π, limit.lift_π],
    dsimp,
    rw ← hm,
    dsimp [diagram_nat_trans],
    simp,
  end } .

instance (X : C) (K : Type (max v u)) [small_category K] [has_limits_of_shape K D] :
  preserves_limits_of_shape K (J.diagram_functor D X) := ⟨⟩

instance (X : C) [has_limits D] : preserves_limits (J.diagram_functor D X) := ⟨⟩

variables [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]

@[simps]
def colimit_limit_diagram_iso {K : Type (max v u)} [small_category K]
  (F : K ⥤ Cᵒᵖ ⥤ D) (X : C) : colimit (F ⋙ J.diagram_functor D X).flip ≅
  F ⋙ J.plus_functor D ⋙ (evaluation _ _).obj (op X) :=
nat_iso.of_components (λ k,
  let h := is_colimit_of_preserves ((evaluation _ _).obj k)
    (colimit.is_colimit ((F ⋙ J.diagram_functor D X).flip)) in
  h.cocone_point_unique_up_to_iso (colimit.is_colimit _))
begin
  intros a b f,
  ext1,
  dsimp [is_colimit.cocone_point_unique_up_to_iso, colim_map, is_colimit.map],
  rw ← (colimit.ι (F ⋙ J.diagram_functor D X).flip j).naturality_assoc,
  erw [colimit_obj_iso_colimit_comp_evaluation_ι_app_hom,
    colimit_obj_iso_colimit_comp_evaluation_ι_app_hom_assoc,
    colimit.ι_desc],
  refl,
end

variables [concrete_category.{max v u} D]
variables [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]

instance (K : Type (max v u))
  [small_category K] [fin_category K] [has_limits_of_shape K D]
  [preserves_limits_of_shape K (forget D)]
  [reflects_limits_of_shape K (forget D)] :
  preserves_limits_of_shape K (J.plus_functor D) :=
begin
  constructor, intros F, apply preserves_limit_of_evaluation, intros X,
  apply preserves_limit_of_preserves_limit_cone (limit.is_limit F),
  refine ⟨λ S, _, _, _⟩,
  { dsimp [plus_obj],
    let e := colimit_limit_iso (F ⋙ J.diagram_functor D X.unop),
    let t : J.diagram (limit F) (unop X) ≅ limit (F ⋙ J.diagram_functor D X.unop) :=
      (is_limit_of_preserves (J.diagram_functor D X.unop)
      (limit.is_limit _)).cone_point_unique_up_to_iso (limit.is_limit _),
    let p : (J.plus_obj (limit F)).obj X ≅ colimit (limit (F ⋙ J.diagram_functor D X.unop)) :=
      has_colimit.iso_of_nat_iso t,
    refine limit.lift _ S ≫ (has_limit.iso_of_nat_iso _).hom ≫ e.inv ≫ p.inv,
    refine nat_iso.of_components (λ k, _) _,
    { dsimp [plus_obj],
      let w : (colimit (F ⋙ J.diagram_functor D (unop X)).flip).obj k ≅
        colimit ((F ⋙ J.diagram_functor D X.unop).flip ⋙ (evaluation _ _).obj k) :=
        colimit_obj_iso_colimit_comp_evaluation _ _,
      refine w.symm },
    { intros i j f,
      ext w,
      dsimp [plus_map],
      erw [colimit.ι_map_assoc, colimit_obj_iso_colimit_comp_evaluation_ι_inv
        ((F ⋙ J.diagram_functor D (unop X)).flip) w j,
        colimit_obj_iso_colimit_comp_evaluation_ι_inv_assoc
        ((F ⋙ J.diagram_functor D (unop X)).flip) w i],
      rw ← (colimit.ι (F ⋙ J.diagram_functor D (unop X)).flip w).naturality,
      refl } },
  { intros S k,
    dsimp,
    rw [← (limit.is_limit (F ⋙ J.plus_functor D ⋙ (evaluation Cᵒᵖ D).obj X)).fac S k,
      category.assoc],
    congr' 1,
    dsimp,
    simp only [category.assoc],
    rw [← iso.eq_inv_comp, iso.inv_comp_eq, iso.inv_comp_eq],
    ext,
    dsimp [plus_map],
    simp only [has_colimit.iso_of_nat_iso_ι_hom_assoc, ι_colim_map],
    dsimp [is_limit.cone_point_unique_up_to_iso, has_limit.iso_of_nat_iso,
      is_limit.map],
    rw limit.lift_π,
    dsimp,
    rw ι_colimit_limit_iso_limit_π_assoc,
    simp_rw [← nat_trans.comp_app, ← category.assoc, ← nat_trans.comp_app],
    rw limit.lift_π,
    dsimp,
    congr' 1,
    rw ← nat_trans.comp_app,
    dsimp [-nat_trans.comp_app, nat_iso.of_components],
    dsimp,
    simpa },
  { intros S m hm,
    dsimp,
    simp_rw ← category.assoc,
    simp_rw iso.eq_comp_inv,
    rw ← iso.comp_inv_eq,
    ext,
    dsimp,
    simp only [limit.lift_π, category.assoc],
    rw ← hm,
    congr' 1,
    ext,
    dsimp [plus_map, plus_obj],
    erw colimit.ι_map,
    erw [colimit.ι_desc_assoc, limit.lift_π],
    dsimp,
    simp only [category.assoc],
    rw ι_colimit_limit_iso_limit_π_assoc,
    dsimp,
    simp only [nat_iso.of_components.inv_app,
      colimit_obj_iso_colimit_comp_evaluation_ι_app_hom, iso.symm_inv],
    dsimp [is_limit.cone_point_unique_up_to_iso],
    rw [← category.assoc, ← nat_trans.comp_app, limit.lift_π],
    refl }
end

instance [has_finite_limits D] [preserves_finite_limits (forget D)]
  [reflects_isomorphisms (forget D)] : preserves_finite_limits (J.plus_functor D) :=
begin
  constructor, introsI K _ _,
  haveI : reflects_limits_of_shape K (forget D) :=
    reflects_limits_of_shape_of_reflects_isomorphisms,
  apply_instance
end

instance (K : Type (max v u))
  [small_category K] [fin_category K] [has_limits_of_shape K D]
  [preserves_limits_of_shape K (forget D)]
  [reflects_limits_of_shape K (forget D)] :
  preserves_limits_of_shape K (J.sheafification D) :=
limits.comp_preserves_limits_of_shape _ _

instance [has_finite_limits D] [preserves_finite_limits (forget D)]
  [reflects_isomorphisms (forget D)] : preserves_finite_limits (J.sheafification D) :=
limits.comp_preserves_finite_limits _ _

end category_theory.grothendieck_topology
