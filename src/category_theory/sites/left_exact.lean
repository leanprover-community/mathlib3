import category_theory.sites.sheafification
import category_theory.limits.functor_category

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

end category_theory.grothendieck_topology
