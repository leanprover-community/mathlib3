/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.sites.sheafification
import category_theory.sites.limits
import category_theory.limits.functor_category
import category_theory.limits.filtered_colimit_commutes_finite_limit

/-!
# Left exactness of sheafification

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
In this file we show that sheafification commutes with finite limits.
-/

open category_theory
open category_theory.limits
open opposite

universes w v u
variables {C : Type (max v u)} [category.{v} C] {J : grothendieck_topology C}
variables {D : Type w} [category.{max v u} D]
variables [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), has_multiequalizer (S.index P)]

noncomputable theory

namespace category_theory.grothendieck_topology

/-- An auxiliary definition to be used in the proof of the fact that
`J.diagram_functor D X` preserves limits. -/
@[simps]
def cone_comp_evaluation_of_cone_comp_diagram_functor_comp_evaluation
  {X : C} {K : Type (max v u)} [small_category K]
  {F : K ⥤ Cᵒᵖ ⥤ D} {W : J.cover X} (i : W.arrow)
  (E : cone (F ⋙ J.diagram_functor D X ⋙ (evaluation (J.cover X)ᵒᵖ D).obj (op W))) :
  cone (F ⋙ (evaluation _ _).obj (op i.Y)) :=
{ X := E.X,
  π :=
  { app := λ k, E.π.app k ≫ multiequalizer.ι (W.index (F.obj k)) i,
    naturality' := begin
      intros a b f,
      dsimp,
      rw [category.id_comp, category.assoc, ← E.w f],
      dsimp [diagram_nat_trans],
      simp only [multiequalizer.lift_ι, category.assoc],
    end } }

/-- An auxiliary definition to be used in the proof of the fact that
`J.diagram_functor D X` preserves limits. -/
abbreviation lift_to_diagram_limit_obj
  {X : C} {K : Type (max v u)} [small_category K] [has_limits_of_shape K D]
  {W : (J.cover X)ᵒᵖ} (F : K ⥤ Cᵒᵖ ⥤ D)
  (E : cone (F ⋙ J.diagram_functor D X ⋙ (evaluation (J.cover X)ᵒᵖ D).obj W)) :
  E.X ⟶ (J.diagram (limit F) X).obj W :=
multiequalizer.lift _ _ (λ i,
  (is_limit_of_preserves ((evaluation _ _).obj (op i.Y)) (limit.is_limit _)).lift
  (cone_comp_evaluation_of_cone_comp_diagram_functor_comp_evaluation i E))
begin
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
end

instance (X : C) (K : Type (max v u)) [small_category K] [has_limits_of_shape K D]
  (F : K ⥤ Cᵒᵖ ⥤ D) : preserves_limit F (J.diagram_functor D X) :=
preserves_limit_of_evaluation _ _ $ λ W,
preserves_limit_of_preserves_limit_cone (limit.is_limit _)
{ lift := λ E, lift_to_diagram_limit_obj F E,
  fac' := begin
    intros E k,
    dsimp [diagram_nat_trans],
    ext1,
    simp only [multiequalizer.lift_ι, multiequalizer.lift_ι_assoc, category.assoc],
    change (_ ≫ _) ≫ _ = _,
    dsimp [evaluate_combined_cones],
    erw [category.comp_id, category.assoc, ← nat_trans.comp_app, limit.lift_π, limit.lift_π],
    refl,
  end,
  uniq' := begin
    intros E m hm,
    ext,
    delta lift_to_diagram_limit_obj,
    erw [multiequalizer.lift_ι, category.assoc],
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
variables [concrete_category.{max v u} D]
variables [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]

/-- An auxiliary definition to be used in the proof that `J.plus_functor D` commutes
with finite limits. -/
def lift_to_plus_obj_limit_obj {K : Type (max v u)} [small_category K] [fin_category K]
  [has_limits_of_shape K D] [preserves_limits_of_shape K (forget D)]
  [reflects_limits_of_shape K (forget D)] (F : K ⥤ Cᵒᵖ ⥤ D) (X : C)
  (S : cone (F ⋙ J.plus_functor D ⋙ (evaluation Cᵒᵖ D).obj (op X))) :
  S.X ⟶ (J.plus_obj (limit F)).obj (op X) :=
let
  e := colimit_limit_iso (F ⋙ J.diagram_functor D X),
  t : J.diagram (limit F) X ≅ limit (F ⋙ J.diagram_functor D X) :=
    (is_limit_of_preserves (J.diagram_functor D X) (limit.is_limit _)).cone_point_unique_up_to_iso
    (limit.is_limit _),
  p : (J.plus_obj (limit F)).obj (op X) ≅ colimit (limit (F ⋙ J.diagram_functor D X)) :=
    has_colimit.iso_of_nat_iso t,
  s : colimit (F ⋙ J.diagram_functor D X).flip ≅
    F ⋙ J.plus_functor D ⋙ (evaluation Cᵒᵖ D).obj (op X) :=
      nat_iso.of_components (λ k, colimit_obj_iso_colimit_comp_evaluation _ k) begin
        intros i j f,
        rw [← iso.eq_comp_inv, category.assoc, ← iso.inv_comp_eq],
        ext w,
        dsimp [plus_map],
        erw [colimit.ι_map_assoc, colimit_obj_iso_colimit_comp_evaluation_ι_inv
        ((F ⋙ J.diagram_functor D X).flip) w j,
        colimit_obj_iso_colimit_comp_evaluation_ι_inv_assoc
        ((F ⋙ J.diagram_functor D X).flip) w i],
      rw ← (colimit.ι (F ⋙ J.diagram_functor D X).flip w).naturality,
      refl
    end in
limit.lift _ S ≫ (has_limit.iso_of_nat_iso s.symm).hom ≫ e.inv ≫ p.inv

-- This lemma should not be used directly. Instead, one should use the fact that
-- `J.plus_functor D` preserves finite limits, along with the fact that
-- evaluation preserves limits.
lemma lift_to_plus_obj_limit_obj_fac {K : Type (max v u)} [small_category K] [fin_category K]
  [has_limits_of_shape K D] [preserves_limits_of_shape K (forget D)]
  [reflects_limits_of_shape K (forget D)] (F : K ⥤ Cᵒᵖ ⥤ D) (X : C)
  (S : cone (F ⋙ J.plus_functor D ⋙ (evaluation Cᵒᵖ D).obj (op X))) (k) :
  lift_to_plus_obj_limit_obj F X S ≫ (J.plus_map (limit.π F k)).app (op X) = S.π.app k :=
begin
  dsimp only [lift_to_plus_obj_limit_obj],
  rw [← (limit.is_limit (F ⋙ J.plus_functor D ⋙ (evaluation Cᵒᵖ D).obj (op X))).fac S k,
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
  rw [limit.lift_π, category.assoc],
  congr' 1,
  rw ← iso.comp_inv_eq,
  erw colimit.ι_desc,
  refl,
end

instance (K : Type (max v u))
  [small_category K] [fin_category K] [has_limits_of_shape K D]
  [preserves_limits_of_shape K (forget D)]
  [reflects_limits_of_shape K (forget D)] :
  preserves_limits_of_shape K (J.plus_functor D) :=
begin
  constructor, intros F, apply preserves_limit_of_evaluation, intros X,
  apply preserves_limit_of_preserves_limit_cone (limit.is_limit F),
  refine ⟨λ S, lift_to_plus_obj_limit_obj F X.unop S, _, _⟩,
  { intros S k,
    apply lift_to_plus_obj_limit_obj_fac },
  { intros S m hm,
    dsimp [lift_to_plus_obj_limit_obj],
    simp_rw [← category.assoc, iso.eq_comp_inv, ← iso.comp_inv_eq],
    ext,
    simp only [limit.lift_π, category.assoc, ← hm],
    congr' 1,
    ext,
    dsimp [plus_map, plus_obj],
    erw [colimit.ι_map, colimit.ι_desc_assoc, limit.lift_π],
    dsimp,
    simp only [category.assoc],
    rw ι_colimit_limit_iso_limit_π_assoc,
    simp only [nat_iso.of_components_inv_app,
      colimit_obj_iso_colimit_comp_evaluation_ι_app_hom, iso.symm_inv],
    dsimp [is_limit.cone_point_unique_up_to_iso],
    rw [← category.assoc, ← nat_trans.comp_app, limit.lift_π],
    refl }
end

instance [has_finite_limits D] [preserves_finite_limits (forget D)]
  [reflects_isomorphisms (forget D)] : preserves_finite_limits (J.plus_functor D) :=
begin
  apply preserves_finite_limits_of_preserves_finite_limits_of_size.{max v u},
  introsI K _ _,
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

namespace category_theory

variables [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]
variables [concrete_category.{max v u} D]
variables [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]
variables [preserves_limits (forget D)]
variables [reflects_isomorphisms (forget D)]
variables (K : Type (max v u))
variables [small_category K] [fin_category K] [has_limits_of_shape K D]

instance : preserves_limits_of_shape K (presheaf_to_Sheaf J D) :=
begin
  constructor, intros F, constructor, intros S hS,
  apply is_limit_of_reflects (Sheaf_to_presheaf J D),
  haveI : reflects_limits_of_shape K (forget D) :=
    reflects_limits_of_shape_of_reflects_isomorphisms,
  apply is_limit_of_preserves (J.sheafification D) hS,
end

instance [has_finite_limits D] : preserves_finite_limits (presheaf_to_Sheaf J D) :=
begin
  apply preserves_finite_limits_of_preserves_finite_limits_of_size.{max v u},
  intros, resetI, apply_instance
end

end category_theory
