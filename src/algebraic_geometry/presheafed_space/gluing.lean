/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import topology.gluing
import algebraic_geometry.open_immersion
import algebraic_geometry.locally_ringed_space.has_colimits

/-!
# Gluing Structured spaces
-/

noncomputable theory

open topological_space category_theory opposite
open category_theory.limits algebraic_geometry.PresheafedSpace
open category_theory.glue_data

namespace algebraic_geometry

universes v u

variables (C : Type u) [category.{v} C]

namespace PresheafedSpace

@[nolint has_inhabited_instance]
structure glue_data extends glue_data (PresheafedSpace C) :=
  (f_open : ∀ i j, is_open_immersion (f i j))

attribute [instance] glue_data.f_open

namespace glue_data

variables {C} (D : glue_data C)

local notation `D'` := D.to_glue_data

abbreviation to_Top_glue_data : Top.glue_data :=
{ f_open := λ i j, (D.f_open i j).base_open,
  to_glue_data := D' .map_glue_data (forget C) }

section end

variable [has_limits C]

lemma imm_open_embedding (i : D.ι) : open_embedding (D' .imm i).base :=
begin
  rw ← (show _ = (D' .imm i).base, from D' .imm_glued_iso_inv (PresheafedSpace.forget _) _),
  exact open_embedding.comp (Top.homeo_of_iso
    (D' .glued_iso (PresheafedSpace.forget _)).symm).open_embedding
    (D.to_Top_glue_data.imm_open_embedding i)
end

lemma pullback_fst_preimage_snd_image (X Y Z : Top) (f : X ⟶ Z) (g : Y ⟶ Z) (U : set X) :
  (pullback.snd : pullback f g ⟶ _) '' ((pullback.fst : pullback f g ⟶ _) ⁻¹' U)
    = g ⁻¹' (f '' U) :=
begin
  ext x,
  split,
  { rintros ⟨y, hy, rfl⟩,
    exact ⟨(pullback.fst : pullback f g ⟶ _) y, hy,
     concrete_category.congr_hom pullback.condition y⟩ },
  { rintros ⟨y, hy, eq⟩,
     exact ⟨(Top.pullback_iso_prod_subtype f g).inv ⟨⟨_,_⟩,eq⟩, by simpa, by simp⟩ },
end

lemma pullback_base (i j k : D.ι)  (S : set (D.V (i, j)).carrier) :
  ((pullback.snd : pullback (D.f i j) (D.f i k) ⟶ _).base) ''
    (((pullback.fst : pullback (D.f i j) (D.f i k) ⟶ _).base) ⁻¹' S) =
      (D.f i k).base ⁻¹' ((D.f i j).base '' S) :=
begin
  have eq₁ : _ = (pullback.fst : pullback (D.f i j) (D.f i k) ⟶ _).base :=
    preserves_pullback.iso_hom_fst (forget C) _ _,
  have eq₂ : _ = (pullback.snd : pullback (D.f i j) (D.f i k) ⟶ _).base :=
    preserves_pullback.iso_hom_snd (forget C) _ _,
  rw [← eq₁, ← eq₂],
  erw ← set.image_image,
  rw coe_comp,
  erw ← set.preimage_preimage,
  rw [set.image_preimage_eq, pullback_fst_preimage_snd_image],
  refl,
  rw ← Top.epi_iff_surjective,
  apply_instance
end


@[simp, reassoc]
lemma f_inv_app_f_app (i j k : D.ι)  (U : (opens (D.V (i, j)).carrier)) :
  (D.f_open i j).inv_app U ≫ (D.f i k).c.app _ =
    (pullback.fst : pullback (D.f i j) (D.f i k) ⟶ _).c.app (op U) ≫
    (PresheafedSpace.is_open_immersion.pullback_snd_of_left (D.f i j) (D.f i k)).inv_app (unop _)
    ≫ (D.V _).presheaf.map (eq_to_hom (
      begin
        delta is_open_immersion.open_functor,
        dsimp only [functor.op, is_open_map.functor, opens.map, unop_op],congr,
        apply pullback_base,
      end)) :=
begin
  rw ← cancel_epi (inv ((D.f_open i j).inv_app U)),
  rw is_iso.inv_hom_id_assoc,
  rw PresheafedSpace.is_open_immersion.inv_inv_app,
  simp_rw category.assoc,
  erw (pullback.fst : pullback (D.f i j) (D.f i k) ⟶ _).c.naturality_assoc,
  have := PresheafedSpace.congr_app (@pullback.condition _ _ _ _ _ (D.f i j) (D.f i k) _),
  dsimp only [comp_c_app] at this,
  reassoc! this,
  erw this,
  erw ← functor.map_comp_assoc,
  erw PresheafedSpace.is_open_immersion.inv_naturality_assoc,
  erw PresheafedSpace.is_open_immersion.app_inv_app_assoc,
  erw ← (D.V (i, k)).presheaf.map_comp,
  erw ← (D.V (i, k)).presheaf.map_comp,
  convert (category.comp_id _).symm,
  erw (D.V (i, k)).presheaf.map_id,
  refl
end

lemma imm_image_preimage_eq (i j : D.ι) (U : opens (D.U i).carrier) :
  (opens.map (D.to_glue_data.imm j).base).obj
    ((D.imm_open_embedding i).is_open_map.functor.obj U) =
      (D.f_open j i).open_functor.obj ((opens.map (D.to_glue_data.t j i).base).obj
        ((opens.map (D.to_glue_data.f i j).base).obj U)) :=
begin
  dsimp only [opens.map, is_open_map.functor],
  congr' 1,
  erw ← (show _ = (D.to_glue_data.imm i).base, from
    D' .imm_glued_iso_inv (PresheafedSpace.forget _) i),
  erw ← (show _ = (D.to_glue_data.imm j).base, from
    D' .imm_glued_iso_inv (PresheafedSpace.forget _) j),
  rw [coe_comp, coe_comp],
  conv_lhs { erw [← set.image_image, ← set.preimage_preimage] },
  rw set.preimage_image_eq,
  dsimp only,
  refine eq.trans (D.to_Top_glue_data.preimage_image_eq_image' _ _ _) _,
  rw [coe_comp, set.image_comp],
  congr' 1,
  erw set.eq_preimage_iff_image_eq,
  rw set.image_image,
  simp_rw ← comp_apply,
  erw ← comp_base,
  convert set.image_id _,
  erw D' .t_inv,
  refl,
  { change function.bijective (Top.homeo_of_iso (as_iso _)),
    exact homeomorph.bijective _,
    apply_instance },
  { rw ← Top.mono_iff_injective,
    apply_instance }
end

def opens_image_preimage_map (i j : D.ι) (U : opens (D.U i).carrier) :
  (D.U i).presheaf.obj (op U) ⟶ (D.U j).presheaf.obj
    (op ((opens.map (D' .imm j).base).obj ((D.imm_open_embedding i).is_open_map.functor.obj U))) :=
(D.f i j).c.app (op U) ≫ (D.t j i).c.app _ ≫
  (D.f_open j i).inv_app (unop _) ≫ (D.to_glue_data.U j).presheaf.map
    (eq_to_hom (D.imm_image_preimage_eq i j U)).op

section end

/--
We can prove the `eq` along with the lemma. Thus this is bundled together here, and the
lemma itself is seaparated below.
-/
lemma opens_image_preimage_map_app' (i j k : D.ι) (U : opens (D.U i).carrier) :
  ∃ eq, D.opens_image_preimage_map i j U ≫ (D.f j k).c.app _ =
    (pullback.fst ≫ D.t j i ≫ D.f i j : pullback (D.f j i) (D.f j k) ⟶ _).c.app (op U) ≫
     (is_open_immersion.pullback_snd_of_left (D.f j i) (D.f j k)).inv_app (unop _) ≫
      (D.V (j, k)).presheaf.map (eq_to_hom eq) :=
begin
  split,
  delta opens_image_preimage_map,
  simp_rw category.assoc,
  rw (D.f j k).c.naturality,
  rw f_inv_app_f_app_assoc,
  erw ← (D.V (j, k)).presheaf.map_comp,
  simp_rw ← category.assoc,
  erw ← comp_c_app,
  erw ← comp_c_app,
  simp_rw category.assoc,
  dsimp only [functor.op, unop_op, quiver.hom.unop_op],
  rw [eq_to_hom_map (opens.map _), eq_to_hom_op, eq_to_hom_trans],
  congr
end

lemma opens_image_preimage_map_app (i j k : D.ι) (U : opens (D.U i).carrier) :
D.opens_image_preimage_map i j U ≫ (D.f j k).c.app _ =
    (pullback.fst ≫ D.t j i ≫ D.f i j : pullback (D.f j i) (D.f j k) ⟶ _).c.app (op U) ≫
     (is_open_immersion.pullback_snd_of_left (D.f j i) (D.f j k)).inv_app (unop _) ≫
      (D.V (j, k)).presheaf.map (eq_to_hom ((opens_image_preimage_map_app' D i j k U).some)) :=
(opens_image_preimage_map_app' D i j k U).some_spec

lemma opens_image_preimage_map_app_assoc (i j k : D.ι) (U : opens (D.U i).carrier)
  {X' : C} (f' : _ ⟶ X') :
  D.opens_image_preimage_map i j U ≫ (D.f j k).c.app _ ≫ f' =
    (pullback.fst ≫ D.t j i ≫ D.f i j : pullback (D.f j i) (D.f j k) ⟶ _).c.app (op U) ≫
    (is_open_immersion.pullback_snd_of_left (D.f j i) (D.f j k)).inv_app (unop _) ≫
    (D.V (j, k)).presheaf.map (eq_to_hom ((opens_image_preimage_map_app' D i j k U).some)) ≫ f' :=
by { simp_rw ← category.assoc, congr' 1, simp_rw category.assoc,
  convert opens_image_preimage_map_app _ _ _ _ _ }


lemma snd_inv_app_t_app' (i j k : D.ι) (U : opens (pullback (D.f i j) (D.f i k)).carrier) :
  ∃ eq, (is_open_immersion.pullback_snd_of_left (D.f i j) (D.f i k)).inv_app U ≫
  (D.t _ _).c.app _ ≫ (D.V (k, i)).presheaf.map (eq_to_hom eq) = (D.t' _ _ _).c.app _ ≫
    (is_open_immersion.pullback_fst_of_right (D.f k j) (D.f k i)).inv_app (unop _) :=
begin
  split,
  rw ← is_iso.eq_inv_comp,
  rw PresheafedSpace.is_open_immersion.inv_inv_app,
  rw category.assoc,
  rw (D.t' k i j).c.naturality_assoc,
  simp_rw ← category.assoc,
  erw ← comp_c_app,
  rw congr_app (D.t_fac k i j),
  rw comp_c_app,
  simp_rw category.assoc,
  erw is_open_immersion.inv_naturality,
  erw is_open_immersion.inv_naturality_assoc,
  erw is_open_immersion.app_inv_app'_assoc,
  simp_rw [← (D.to_glue_data.V (k, i)).presheaf.map_comp,
    eq_to_hom_map (functor.op _), eq_to_hom_op, eq_to_hom_trans],
  { rintros x ⟨y, hy, eq⟩,
    replace eq := concrete_category.congr_arg ((D.to_glue_data.t i k).base) eq,
    change (pullback.snd ≫ D.t i k).base y = (D.t k i ≫ D.t i k).base x at eq,
    rw [D' .t_inv, id_base, Top.id_app] at eq,
    subst eq,
    use (inv (D.t' k i j)).base y,
    change ((inv (D.t' k i j)) ≫ pullback.fst).base y = _,
    congr' 2,
    rw [is_iso.inv_comp_eq, D' .t_fac_assoc, D' .t_inv, category.comp_id] }
end

@[simp, reassoc]
lemma snd_inv_app_t_app (i j k : D.ι) (U : opens (pullback (D.f i j) (D.f i k)).carrier) :
  (is_open_immersion.pullback_snd_of_left (D.f i j) (D.f i k)).inv_app U ≫
  (D.t _ _).c.app _ = (D.t' _ _ _).c.app _ ≫
  (is_open_immersion.pullback_fst_of_right (D.f k j) (D.f k i)).inv_app (unop _) ≫
  (D.V (k, i)).presheaf.map (eq_to_hom (D.snd_inv_app_t_app' i j k U).some.symm) :=
begin
  have e := (D.snd_inv_app_t_app' i j k U).some_spec,
  reassoc! e,
  rw ← e,
  simp,
end

section end

def imm_inv_app_π_app (i : D.ι) (U : opens (D.U i).carrier) (j) :
  (D.to_glue_data.U i).presheaf.obj (op U) ⟶ (D.to_glue_data.diagram.multispan.obj j).presheaf.obj
    (op ((opens.map (colimit.ι D.to_glue_data.diagram.multispan j).base).obj
      ((D.imm_open_embedding i).is_open_map.functor.obj U))) :=
begin
  rcases j with (⟨j, k⟩|j),
    { refine D.opens_image_preimage_map i j U ≫ (D.f j k).c.app _ ≫
       (D.V (j, k)).presheaf.map (eq_to_hom _),
      dsimp only [functor.op, opens.map, unop_op],
      congr' 2,
      rw set.preimage_preimage,
      change (D.f j k ≫ D' .imm j).base ⁻¹' _ = _,
      congr' 3,
      exact colimit.w D' .diagram.multispan (walking_multispan.hom.fst (j, k))
      },
    exact D.opens_image_preimage_map i j U
end


def imm_inv_app (i : D.ι) (U : opens (D.U i).carrier) :
  (D.U i).presheaf.obj (op U) ⟶ limit (pointwise_diagram D.to_glue_data.diagram.multispan
    ((D.imm_open_embedding i).is_open_map.functor.obj U)) :=
limit.lift (pointwise_diagram D.to_glue_data.diagram.multispan
    ((D.imm_open_embedding i).is_open_map.functor.obj U))
{ X := (D.U i).presheaf.obj (op U),
  π := { app := λ j, D.imm_inv_app_π_app i U (unop j),
  naturality' :=
  begin
    rintros X Y f',
    induction X using opposite.rec,
    induction Y using opposite.rec,
    let f : Y ⟶ X := f'.unop, have : f' = f.op := rfl, clear_value f, subst this,
    rcases f with (_|⟨j,k⟩|⟨j,k⟩),
    { erw category.id_comp,
      erw category_theory.functor.map_id,
      rw category.comp_id },
    { erw category.id_comp, congr' 1 },
    erw category.id_comp,
    change D.opens_image_preimage_map i j U ≫
      (D.f j k).c.app _ ≫
        (D.V (j, k)).presheaf.map (eq_to_hom _) =
          D.opens_image_preimage_map _ _ _ ≫
            ((D.f k j).c.app _ ≫ (D.t j k).c.app _) ≫
              (D.V (j, k)).presheaf.map (eq_to_hom _),
    erw opens_image_preimage_map_app_assoc,
    simp_rw category.assoc,
    erw opens_image_preimage_map_app_assoc,
    erw (D.t j k).c.naturality_assoc,
    rw snd_inv_app_t_app_assoc,
    erw ← PresheafedSpace.comp_c_app_assoc,
    have : D.t' j k i ≫ pullback.fst ≫ D.t k i ≫ D.to_glue_data.f i k =
      (pullback_symmetry _ _).hom ≫ pullback.fst ≫ D.t j i ≫ D.f i j,
    { rw [← D' .t_fac_assoc, D' .t'_comp_eq_pullback_symmetry_assoc,
        pullback_symmetry_hom_comp_snd_assoc, pullback.condition, D' .t_fac_assoc] },
    rw congr_app this,
    erw PresheafedSpace.comp_c_app_assoc (pullback_symmetry _ _).hom,
    simp_rw category.assoc,
    congr' 1,
    rw ← is_iso.eq_inv_comp,
    erw is_open_immersion.inv_inv_app,
    simp_rw category.assoc,
    erw nat_trans.naturality_assoc,
    erw ← PresheafedSpace.comp_c_app_assoc,
    erw congr_app (pullback_symmetry_hom_comp_snd _ _),
    simp_rw category.assoc,
    erw is_open_immersion.inv_naturality_assoc,
    erw is_open_immersion.inv_naturality_assoc,
    erw is_open_immersion.inv_naturality_assoc,
    erw is_open_immersion.app_inv_app_assoc,
    repeat { erw ← (D.V (j, k)).presheaf.map_comp },
    congr,
  end } }

lemma imm_inv_app_π_id' (i : D.ι) (U : opens (D.U i).carrier) :
  ∃ eq, D.imm_inv_app i U ≫ limit.π (pointwise_diagram D.to_glue_data.diagram.multispan
    ((D.imm_open_embedding i).is_open_map.functor.obj U)) (op (walking_multispan.right i)) =
    (D.U i).presheaf.map (eq_to_hom eq) :=
begin
  split,
  delta imm_inv_app,
  rw limit.lift_π,
  change D.opens_image_preimage_map i i U = _,
  dsimp [opens_image_preimage_map],
  rw congr_app (D.t_id _),
  rw id_c_app,
  rw ← functor.map_comp,
  erw is_open_immersion.inv_naturality_assoc,
  erw is_open_immersion.app_inv_app'_assoc,
  simp only [eq_to_hom_op, eq_to_hom_trans, eq_to_hom_map (functor.op _), ← functor.map_comp],
  rw set.range_iff_surjective.mpr _,
  { simp },
  { rw ← Top.epi_iff_surjective,
    apply_instance }
end

lemma π_imm_inv_app_π (i j : D.ι) (U : opens (D.U i).carrier) :
  limit.π (pointwise_diagram D.to_glue_data.diagram.multispan
    ((D.imm_open_embedding i).is_open_map.functor.obj U)) (op (walking_multispan.right i)) ≫
  (D.U i).presheaf.map (eq_to_hom (D.imm_inv_app_π_id' i U).some.symm) ≫
  D.imm_inv_app i U ≫ limit.π _ (op (walking_multispan.right j)) =
    limit.π _ (op (walking_multispan.right j)) :=
begin
  rw ← cancel_mono ((pointwise_diagram D' .diagram.multispan _).map
    (quiver.hom.op (walking_multispan.hom.snd (i, j))) ≫ (𝟙 _)),
  simp_rw category.assoc,
  rw limit.w_assoc,
  erw limit.lift_π_assoc,
  rw [category.comp_id, category.comp_id],
  change _ ≫ _ ≫ (_ ≫ _) ≫ _ = _,
  rw [congr_app (D.t_id _), id_c_app],
  simp_rw category.assoc,
  rw [← functor.map_comp_assoc, is_open_immersion.inv_naturality_assoc],
  erw is_open_immersion.app_inv_app_assoc,
  iterate 3 { rw ← functor.map_comp_assoc },
  rw nat_trans.naturality_assoc,
  erw ← (D.V (i, j)).presheaf.map_comp,
  convert limit.w (pointwise_diagram D.to_glue_data.diagram.multispan _)
    (quiver.hom.op (walking_multispan.hom.fst (i, j))),
  { rw category.comp_id,
    apply_with mono_comp { instances := ff },
    change mono ((_ ≫ D.f j i).c.app _),
    rw comp_c_app,
    apply_with mono_comp { instances := ff },
    erw D.imm_image_preimage_eq i j U,
    all_goals { apply_instance } },
end

lemma π_imm_inv_app_eq_id (i : D.ι) (U : opens (D.U i).carrier) :
  limit.π (pointwise_diagram D.to_glue_data.diagram.multispan
    ((D.imm_open_embedding i).is_open_map.functor.obj U)) (op (walking_multispan.right i)) ≫
  (D.U i).presheaf.map (eq_to_hom (D.imm_inv_app_π_id' i U).some.symm) ≫
  D.imm_inv_app i U = 𝟙 _ :=
begin
  ext j,
  induction j using opposite.rec,
  rcases j with (⟨j, k⟩|⟨j⟩),
  { rw ← limit.w (pointwise_diagram D.to_glue_data.diagram.multispan _)
    (quiver.hom.op (walking_multispan.hom.fst (j, k))),
    rw ← category.assoc,
    rw category.id_comp,
    congr' 1,
    simp_rw category.assoc,
    apply π_imm_inv_app_π },
  { simp_rw category.assoc,
    rw category.id_comp,
    apply π_imm_inv_app_π }
end

instance pointwise_diagram_π_is_iso (i : D.ι) (U : opens (D.U i).carrier) :
  is_iso (limit.π (pointwise_diagram D.to_glue_data.diagram.multispan
    ((D.imm_open_embedding i).is_open_map.functor.obj U)) (op (walking_multispan.right i))) :=
begin
  use (D.U i).presheaf.map (eq_to_hom (D.imm_inv_app_π_id' i U).some.symm) ≫
    D.imm_inv_app i U,
  split,
  { apply π_imm_inv_app_eq_id },
  { rw [category.assoc, ← inv_eq_to_hom, functor.map_inv, is_iso.inv_comp_eq, category.comp_id],
    exact (D.imm_inv_app_π_id' _ _).some_spec }
end

instance imm_is_open_immersion (i : D.ι) :
is_open_immersion (D' .imm i) :=
{ base_open := D.imm_open_embedding i,
  c_iso := λ U, by { erw ← colimit_presheaf_obj_iso_pointwise_limit_hom_π, apply_instance } }

def V_pullback_cone_is_limit (i j : D.ι) : is_limit (D' .V_pullback_cone i j) :=
pullback_cone.is_limit_aux' _ $ λ s,
begin
  fsplit,
  refine PresheafedSpace.is_open_immersion.lift (D.f i j) s.fst _,
  { erw ← D.to_Top_glue_data.preimage_range j i,
    have : s.fst.base ≫ D.to_Top_glue_data.to_glue_data.imm i =
      s.snd.base ≫ D.to_Top_glue_data.to_glue_data.imm j,
    { rw ← D' .imm_glued_iso_hom (PresheafedSpace.forget _) _,
      rw ← D' .imm_glued_iso_hom (PresheafedSpace.forget _) _,
      have := congr_arg PresheafedSpace.hom.base s.condition,
      rw [comp_base, comp_base] at this,
      reassoc! this,
      exact this _ },
    rw [← set.image_subset_iff, ← set.image_univ, ← set.image_comp, set.image_univ,
      ← coe_comp, this, coe_comp, ← set.image_univ, set.image_comp],
    exact set.image_subset_range _ _ },
  split,
  { apply is_open_immersion.lift_fac },
  split,
  { rw [← cancel_mono (D' .imm j), category.assoc],
    conv_rhs { rw ← s.condition },
    rw [← (D' .V_pullback_cone i j).condition],
    erw is_open_immersion.lift_fac_assoc },
  { intros m e₁ e₂,
    rw ← cancel_mono (D.f i j),
    erw e₁,
    rw is_open_immersion.lift_fac }
end

lemma imm_jointly_surjective (x : D' .glued) :
  ∃ (i : D.ι) (y : D.U i), (D' .imm i).base y = x :=
D' .imm_jointly_surjective (PresheafedSpace.forget _ ⋙ category_theory.forget Top) x

end glue_data

end PresheafedSpace

namespace SheafedSpace

variables (C) [has_products C]

@[nolint has_inhabited_instance]
structure glue_data extends glue_data (SheafedSpace C) :=
  (f_open : ∀ i j, SheafedSpace.is_open_immersion (f i j))

attribute [instance] glue_data.f_open

namespace glue_data

variables {C} (D : glue_data C)

local notation `D'` := D.to_glue_data

abbreviation to_PresheafedSpace_glue_data : PresheafedSpace.glue_data C :=
{ f_open := D.f_open,
  to_glue_data := D' .map_glue_data forget_to_PresheafedSpace }

variable [has_limits C]

abbreviation iso_PresheafedSpace : D' .glued.to_PresheafedSpace ≅
  D.to_PresheafedSpace_glue_data.to_glue_data.glued :=
D' .glued_iso forget_to_PresheafedSpace

abbreviation imm_iso_PresheafedSpace_inv (i : D.ι) :
  D.to_PresheafedSpace_glue_data.to_glue_data.imm i ≫ D.iso_PresheafedSpace.inv = D' .imm i :=
D' .imm_glued_iso_inv _ _

instance imm_is_open_immersion (i : D.ι) :
is_open_immersion (D' .imm i) :=
by { rw ← D.imm_iso_PresheafedSpace_inv, apply_instance }

lemma imm_jointly_surjective (x : D' .glued) :
  ∃ (i : D.ι) (y : D.U i), (D' .imm i).base y = x :=
D' .imm_jointly_surjective (SheafedSpace.forget _ ⋙ category_theory.forget Top) x

def V_pullback_cone_is_limit (i j : D.ι) : is_limit (D' .V_pullback_cone i j) :=
D' .V_pullback_cone_is_limit_of_map forget_to_PresheafedSpace i j
  (D.to_PresheafedSpace_glue_data.V_pullback_cone_is_limit _ _)

end glue_data

end SheafedSpace

namespace LocallyRingedSpace

@[nolint has_inhabited_instance]
structure glue_data extends glue_data LocallyRingedSpace :=
  (f_open : ∀ i j, LocallyRingedSpace.is_open_immersion (f i j))

attribute [instance] glue_data.f_open

namespace glue_data

variables (D : glue_data)

local notation `D'` := D.to_glue_data

abbreviation to_SheafedSpace_glue_data : SheafedSpace.glue_data CommRing :=
{ f_open := D.f_open,
  to_glue_data := D' .map_glue_data forget_to_SheafedSpace }

abbreviation iso_SheafedSpace : D' .glued.to_SheafedSpace ≅
  D.to_SheafedSpace_glue_data.to_glue_data.glued :=
D' .glued_iso forget_to_SheafedSpace

abbreviation imm_iso_SheafedSpace_inv (i : D.ι) :
  D.to_SheafedSpace_glue_data.to_glue_data.imm i ≫ D.iso_SheafedSpace.inv = (D' .imm i).1 :=
D' .imm_glued_iso_inv forget_to_SheafedSpace i

instance imm_is_open_immersion (i : D.ι) :
is_open_immersion (D' .imm i) :=
by { delta is_open_immersion, rw ← D.imm_iso_SheafedSpace_inv,
  apply PresheafedSpace.is_open_immersion.comp }

instance (i j k : D.ι) :
    preserves_limit (cospan (D.to_glue_data.f i j) (D.to_glue_data.f i k))
      (forget_to_SheafedSpace) := infer_instance

lemma imm_jointly_surjective (x : D' .glued) :
  ∃ (i : D.ι) (y : D.U i), (D' .imm i).1.base y = x :=
D' .imm_jointly_surjective ((LocallyRingedSpace.forget_to_SheafedSpace ⋙
  SheafedSpace.forget _) ⋙ forget Top) x

def V_pullback_cone_is_limit (i j : D.ι) : is_limit (D' .V_pullback_cone i j) :=
D' .V_pullback_cone_is_limit_of_map forget_to_SheafedSpace i j
  (D.to_SheafedSpace_glue_data.V_pullback_cone_is_limit _ _)

end glue_data

end LocallyRingedSpace

namespace Scheme

@[nolint has_inhabited_instance]
structure glue_data extends glue_data Scheme :=
  (f_open : ∀ i j, is_open_immersion (f i j))

attribute [instance] glue_data.f_open

namespace glue_data

variables (D : glue_data)

include D

local notation `D'` := D.to_glue_data

abbreviation to_LocallyRingedSpace_glue_data : LocallyRingedSpace.glue_data :=
{ f_open := D.f_open,
  to_glue_data := D' .map_glue_data forget }

def glued_Scheme : Scheme :=
begin
  apply LocallyRingedSpace.is_open_immersion.Scheme
    D.to_LocallyRingedSpace_glue_data.to_glue_data.glued,
  intro x,
  apply nonempty.some,
  rcases D.to_LocallyRingedSpace_glue_data.imm_jointly_surjective x with ⟨i, y, rfl⟩,
  rcases (D.U i).mem_cover y with ⟨z, z_eq⟩,
  constructor,
  fsplit,
  { exact (costructured_arrow.map (D.to_LocallyRingedSpace_glue_data.to_glue_data.imm i)).obj
      ((costructured_arrow.post Spec forget _).obj ((D.U i).cover y)) },
  split,
  { conv_lhs { rw ← z_eq },
    exact set.mem_range_self z },
  dsimp,
  change LocallyRingedSpace.is_open_immersion
    (_ ≫ D.to_LocallyRingedSpace_glue_data.to_glue_data.imm i),
  apply_instance
end

instance : creates_colimit D.to_glue_data.diagram.multispan forget :=
creates_colimit_of_fully_faithful_of_iso D.glued_Scheme
  (has_colimit.iso_of_nat_iso (D' .diagram_iso forget).symm)

instance : has_multicoequalizer D.to_glue_data.diagram :=
has_colimit_of_created _ forget

abbreviation glued := D' .glued
abbreviation imm := D' .imm

abbreviation iso_LocallyRingedSpace : D.glued.to_LocallyRingedSpace ≅
  D.to_LocallyRingedSpace_glue_data.to_glue_data.glued :=
D' .glued_iso forget

lemma imm_iso_LocallyRingedSpace_inv (i : D.ι) :
  D.to_LocallyRingedSpace_glue_data.to_glue_data.imm i ≫
    D.iso_LocallyRingedSpace.inv = D' .imm i :=
D' .imm_glued_iso_inv forget i

instance imm_is_open_immersion (i : D.ι) :
is_open_immersion (D' .imm i) :=
by { rw ← D.imm_iso_LocallyRingedSpace_inv, apply_instance }

lemma imm_jointly_surjective (x : D' .glued.carrier) :
  ∃ (i : D.ι) (y : (D.U i).carrier), (D.imm i).1.base y = x :=
D' .imm_jointly_surjective ((forget ⋙ LocallyRingedSpace.forget_to_SheafedSpace ⋙
  SheafedSpace.forget _) ⋙ category_theory.forget Top)

@[simp, reassoc]
lemma glue_condition (i j : D.ι) :
  D.t i j ≫ D.f j i ≫ D.imm j = D.f i j ≫ D.imm i :=
D' .glue_condition i j

def V_pullback_cone (i j : D.ι) : pullback_cone (D.imm i) (D.imm j) :=
pullback_cone.mk (D.f i j) (D.t i j ≫ D.f j i) (by simp)

def V_pullback_cone_is_limit (i j : D.ι) :
  is_limit (D.V_pullback_cone i j) :=
D' .V_pullback_cone_is_limit_of_map forget i j
  (D.to_LocallyRingedSpace_glue_data.V_pullback_cone_is_limit _ _)


end glue_data

end Scheme

end algebraic_geometry
-- #lint
