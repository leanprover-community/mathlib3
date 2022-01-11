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

local notation `𝖣` := D.to_glue_data

abbreviation to_Top_glue_data : Top.glue_data :=
{ f_open := λ i j, (D.f_open i j).base_open,
  to_glue_data := 𝖣 .map_glue_data (forget C) }

section end

variable [has_limits C]

lemma ι_open_embedding (i : D.J) : open_embedding (𝖣 .ι i).base :=
begin
  rw ← (show _ = (𝖣 .ι i).base, from 𝖣 .ι_glued_iso_inv (PresheafedSpace.forget _) _),
  exact open_embedding.comp (Top.homeo_of_iso
    (𝖣 .glued_iso (PresheafedSpace.forget _)).symm).open_embedding
    (D.to_Top_glue_data.ι_open_embedding i)
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

lemma pullback_base (i j k : D.J)  (S : set (D.V (i, j)).carrier) :
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
lemma f_inv_app_f_app (i j k : D.J)  (U : (opens (D.V (i, j)).carrier)) :
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

lemma ι_image_preimage_eq (i j : D.J) (U : opens (D.U i).carrier) :
  (opens.map (𝖣 .ι j).base).obj
    ((D.ι_open_embedding i).is_open_map.functor.obj U) =
      (D.f_open j i).open_functor.obj ((opens.map (𝖣 .t j i).base).obj
        ((opens.map (𝖣 .f i j).base).obj U)) :=
begin
  dsimp only [opens.map, is_open_map.functor],
  congr' 1,
  erw ← (show _ = (𝖣 .ι i).base, from
    𝖣 .ι_glued_iso_inv (PresheafedSpace.forget _) i),
  erw ← (show _ = (𝖣 .ι j).base, from
    𝖣 .ι_glued_iso_inv (PresheafedSpace.forget _) j),
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
  erw 𝖣 .t_inv,
  refl,
  { change function.bijective (Top.homeo_of_iso (as_iso _)),
    exact homeomorph.bijective _,
    apply_instance },
  { rw ← Top.mono_iff_injective,
    apply_instance }
end

def opens_image_preimage_map (i j : D.J) (U : opens (D.U i).carrier) :
  (D.U i).presheaf.obj (op U) ⟶ (D.U j).presheaf.obj
    (op ((opens.map (𝖣 .ι j).base).obj ((D.ι_open_embedding i).is_open_map.functor.obj U))) :=
(D.f i j).c.app (op U) ≫ (D.t j i).c.app _ ≫
  (D.f_open j i).inv_app (unop _) ≫ (𝖣 .U j).presheaf.map
    (eq_to_hom (D.ι_image_preimage_eq i j U)).op

/--
We can prove the `eq` along with the lemma. Thus this is bundled together here, and the
lemma itself is separated below.
-/
lemma opens_image_preimage_map_app' (i j k : D.J) (U : opens (D.U i).carrier) :
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

lemma opens_image_preimage_map_app (i j k : D.J) (U : opens (D.U i).carrier) :
D.opens_image_preimage_map i j U ≫ (D.f j k).c.app _ =
    (pullback.fst ≫ D.t j i ≫ D.f i j : pullback (D.f j i) (D.f j k) ⟶ _).c.app (op U) ≫
     (is_open_immersion.pullback_snd_of_left (D.f j i) (D.f j k)).inv_app (unop _) ≫
      (D.V (j, k)).presheaf.map (eq_to_hom ((opens_image_preimage_map_app' D i j k U).some)) :=
(opens_image_preimage_map_app' D i j k U).some_spec

lemma opens_image_preimage_map_app_assoc (i j k : D.J) (U : opens (D.U i).carrier)
  {X' : C} (f' : _ ⟶ X') :
  D.opens_image_preimage_map i j U ≫ (D.f j k).c.app _ ≫ f' =
    (pullback.fst ≫ D.t j i ≫ D.f i j : pullback (D.f j i) (D.f j k) ⟶ _).c.app (op U) ≫
    (is_open_immersion.pullback_snd_of_left (D.f j i) (D.f j k)).inv_app (unop _) ≫
    (D.V (j, k)).presheaf.map (eq_to_hom ((opens_image_preimage_map_app' D i j k U).some)) ≫ f' :=
by { simp_rw ← category.assoc, congr' 1, simp_rw category.assoc,
  convert opens_image_preimage_map_app _ _ _ _ _ }


lemma snd_inv_app_t_app' (i j k : D.J) (U : opens (pullback (D.f i j) (D.f i k)).carrier) :
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
  simp_rw [← (𝖣 .V (k, i)).presheaf.map_comp,
    eq_to_hom_map (functor.op _), eq_to_hom_op, eq_to_hom_trans],
  { rintros x ⟨y, hy, eq⟩,
    replace eq := concrete_category.congr_arg ((𝖣 .t i k).base) eq,
    change (pullback.snd ≫ D.t i k).base y = (D.t k i ≫ D.t i k).base x at eq,
    rw [𝖣 .t_inv, id_base, Top.id_app] at eq,
    subst eq,
    use (inv (D.t' k i j)).base y,
    change ((inv (D.t' k i j)) ≫ pullback.fst).base y = _,
    congr' 2,
    rw [is_iso.inv_comp_eq, 𝖣 .t_fac_assoc, 𝖣 .t_inv, category.comp_id] }
end

@[simp, reassoc]
lemma snd_inv_app_t_app (i j k : D.J) (U : opens (pullback (D.f i j) (D.f i k)).carrier) :
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

def ι_inv_app_π_app (i : D.J) (U : opens (D.U i).carrier) (j) :
  (𝖣 .U i).presheaf.obj (op U) ⟶ (𝖣 .diagram.multispan.obj j).presheaf.obj
    (op ((opens.map (colimit.ι 𝖣 .diagram.multispan j).base).obj
      ((D.ι_open_embedding i).is_open_map.functor.obj U))) :=
begin
  rcases j with (⟨j, k⟩|j),
    { refine D.opens_image_preimage_map i j U ≫ (D.f j k).c.app _ ≫
       (D.V (j, k)).presheaf.map (eq_to_hom _),
      dsimp only [functor.op, opens.map, unop_op],
      congr' 2,
      rw set.preimage_preimage,
      change (D.f j k ≫ 𝖣 .ι j).base ⁻¹' _ = _,
      congr' 3,
      exact colimit.w 𝖣 .diagram.multispan (walking_multispan.hom.fst (j, k))
      },
    exact D.opens_image_preimage_map i j U
end


def ι_inv_app (i : D.J) (U : opens (D.U i).carrier) :
  (D.U i).presheaf.obj (op U) ⟶ limit (componentwise_diagram 𝖣 .diagram.multispan
    ((D.ι_open_embedding i).is_open_map.functor.obj U)) :=
limit.lift (componentwise_diagram 𝖣 .diagram.multispan
    ((D.ι_open_embedding i).is_open_map.functor.obj U))
{ X := (D.U i).presheaf.obj (op U),
  π := { app := λ j, D.ι_inv_app_π_app i U (unop j),
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
    have : D.t' j k i ≫ pullback.fst ≫ D.t k i ≫ 𝖣 .f i k =
      (pullback_symmetry _ _).hom ≫ pullback.fst ≫ D.t j i ≫ D.f i j,
    { rw [← 𝖣 .t_fac_assoc, 𝖣 .t'_comp_eq_pullback_symmetry_assoc,
        pullback_symmetry_hom_comp_snd_assoc, pullback.condition, 𝖣 .t_fac_assoc] },
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

lemma ι_inv_app_π (i : D.J) (U : opens (D.U i).carrier) :
  ∃ eq, D.ι_inv_app i U ≫ limit.π (componentwise_diagram 𝖣 .diagram.multispan
    ((D.ι_open_embedding i).is_open_map.functor.obj U)) (op (walking_multispan.right i)) =
    (D.U i).presheaf.map (eq_to_hom eq) :=
begin
  split,
  delta ι_inv_app,
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

lemma π_ι_inv_app_π (i j : D.J) (U : opens (D.U i).carrier) :
  limit.π (componentwise_diagram 𝖣 .diagram.multispan
    ((D.ι_open_embedding i).is_open_map.functor.obj U)) (op (walking_multispan.right i)) ≫
  (D.U i).presheaf.map (eq_to_hom (D.ι_inv_app_π i U).some.symm) ≫
  D.ι_inv_app i U ≫ limit.π _ (op (walking_multispan.right j)) =
    limit.π _ (op (walking_multispan.right j)) :=
begin
  rw ← cancel_mono ((componentwise_diagram 𝖣 .diagram.multispan _).map
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
  convert limit.w (componentwise_diagram 𝖣 .diagram.multispan _)
    (quiver.hom.op (walking_multispan.hom.fst (i, j))),
  { rw category.comp_id,
    apply_with mono_comp { instances := ff },
    change mono ((_ ≫ D.f j i).c.app _),
    rw comp_c_app,
    apply_with mono_comp { instances := ff },
    erw D.ι_image_preimage_eq i j U,
    all_goals { apply_instance } },
end

lemma π_ι_inv_app_eq_id (i : D.J) (U : opens (D.U i).carrier) :
  limit.π (componentwise_diagram 𝖣 .diagram.multispan
    ((D.ι_open_embedding i).is_open_map.functor.obj U)) (op (walking_multispan.right i)) ≫
  (D.U i).presheaf.map (eq_to_hom (D.ι_inv_app_π i U).some.symm) ≫
  D.ι_inv_app i U = 𝟙 _ :=
begin
  ext j,
  induction j using opposite.rec,
  rcases j with (⟨j, k⟩|⟨j⟩),
  { rw ← limit.w (componentwise_diagram 𝖣 .diagram.multispan _)
    (quiver.hom.op (walking_multispan.hom.fst (j, k))),
    rw ← category.assoc,
    rw category.id_comp,
    congr' 1,
    simp_rw category.assoc,
    apply π_ι_inv_app_π },
  { simp_rw category.assoc,
    rw category.id_comp,
    apply π_ι_inv_app_π }
end

instance componentwise_diagram_π_is_iso (i : D.J) (U : opens (D.U i).carrier) :
  is_iso (limit.π (componentwise_diagram 𝖣 .diagram.multispan
    ((D.ι_open_embedding i).is_open_map.functor.obj U)) (op (walking_multispan.right i))) :=
begin
  use (D.U i).presheaf.map (eq_to_hom (D.ι_inv_app_π i U).some.symm) ≫
    D.ι_inv_app i U,
  split,
  { apply π_ι_inv_app_eq_id },
  { rw [category.assoc, ← inv_eq_to_hom, functor.map_inv, is_iso.inv_comp_eq, category.comp_id],
    exact (D.ι_inv_app_π _ _).some_spec }
end

instance ι_is_open_immersion (i : D.J) :
is_open_immersion (𝖣 .ι i) :=
{ base_open := D.ι_open_embedding i,
  c_iso := λ U, by { erw ← colimit_presheaf_obj_iso_componentwise_limit_hom_π, apply_instance } }

def V_pullback_cone_is_limit (i j : D.J) : is_limit (𝖣 .V_pullback_cone i j) :=
pullback_cone.is_limit_aux' _ $ λ s,
begin
  fsplit,
  refine PresheafedSpace.is_open_immersion.lift (D.f i j) s.fst _,
  { erw ← D.to_Top_glue_data.preimage_range j i,
    have : s.fst.base ≫ D.to_Top_glue_data.to_glue_data.ι i =
      s.snd.base ≫ D.to_Top_glue_data.to_glue_data.ι j,
    { rw ← 𝖣 .ι_glued_iso_hom (PresheafedSpace.forget _) _,
      rw ← 𝖣 .ι_glued_iso_hom (PresheafedSpace.forget _) _,
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
  { rw [← cancel_mono (𝖣 .ι j), category.assoc],
    conv_rhs { rw ← s.condition },
    rw [← (𝖣 .V_pullback_cone i j).condition],
    erw is_open_immersion.lift_fac_assoc },
  { intros m e₁ e₂,
    rw ← cancel_mono (D.f i j),
    erw e₁,
    rw is_open_immersion.lift_fac }
end

lemma ι_jointly_surjective (x : 𝖣 .glued) :
  ∃ (i : D.J) (y : D.U i), (𝖣 .ι i).base y = x :=
𝖣 .ι_jointly_surjective (PresheafedSpace.forget _ ⋙ category_theory.forget Top) x

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

local notation `𝖣` := D.to_glue_data

abbreviation to_PresheafedSpace_glue_data : PresheafedSpace.glue_data C :=
{ f_open := D.f_open,
  to_glue_data := 𝖣 .map_glue_data forget_to_PresheafedSpace }

variable [has_limits C]

abbreviation iso_PresheafedSpace : 𝖣 .glued.to_PresheafedSpace ≅
  D.to_PresheafedSpace_glue_data.to_glue_data.glued :=
𝖣 .glued_iso forget_to_PresheafedSpace

abbreviation ι_iso_PresheafedSpace_inv (i : D.J) :
  D.to_PresheafedSpace_glue_data.to_glue_data.ι i ≫ D.iso_PresheafedSpace.inv = 𝖣 .ι i :=
𝖣 .ι_glued_iso_inv _ _

instance ι_is_open_immersion (i : D.J) :
is_open_immersion (𝖣 .ι i) :=
by { rw ← D.ι_iso_PresheafedSpace_inv, apply_instance }

lemma ι_jointly_surjective (x : 𝖣 .glued) :
  ∃ (i : D.J) (y : D.U i), (𝖣 .ι i).base y = x :=
𝖣 .ι_jointly_surjective (SheafedSpace.forget _ ⋙ category_theory.forget Top) x

def V_pullback_cone_is_limit (i j : D.J) : is_limit (𝖣 .V_pullback_cone i j) :=
𝖣 .V_pullback_cone_is_limit_of_map forget_to_PresheafedSpace i j
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

local notation `𝖣` := D.to_glue_data

abbreviation to_SheafedSpace_glue_data : SheafedSpace.glue_data CommRing :=
{ f_open := D.f_open,
  to_glue_data := 𝖣 .map_glue_data forget_to_SheafedSpace }

abbreviation iso_SheafedSpace : 𝖣 .glued.to_SheafedSpace ≅
  D.to_SheafedSpace_glue_data.to_glue_data.glued :=
𝖣 .glued_iso forget_to_SheafedSpace

abbreviation ι_iso_SheafedSpace_inv (i : D.J) :
  D.to_SheafedSpace_glue_data.to_glue_data.ι i ≫ D.iso_SheafedSpace.inv = (𝖣 .ι i).1 :=
𝖣 .ι_glued_iso_inv forget_to_SheafedSpace i

instance ι_is_open_immersion (i : D.J) :
is_open_immersion (𝖣 .ι i) :=
by { delta is_open_immersion, rw ← D.ι_iso_SheafedSpace_inv,
  apply PresheafedSpace.is_open_immersion.comp }

instance (i j k : D.J) :
    preserves_limit (cospan (𝖣 .f i j) (𝖣 .f i k))
      (forget_to_SheafedSpace) := infer_instance

lemma ι_jointly_surjective (x : 𝖣 .glued) :
  ∃ (i : D.J) (y : D.U i), (𝖣 .ι i).1.base y = x :=
𝖣 .ι_jointly_surjective ((LocallyRingedSpace.forget_to_SheafedSpace ⋙
  SheafedSpace.forget _) ⋙ forget Top) x

def V_pullback_cone_is_limit (i j : D.J) : is_limit (𝖣 .V_pullback_cone i j) :=
𝖣 .V_pullback_cone_is_limit_of_map forget_to_SheafedSpace i j
  (D.to_SheafedSpace_glue_data.V_pullback_cone_is_limit _ _)

end glue_data

end LocallyRingedSpace

namespace Scheme

/--
A family of gluing data consists of
1. An index type `J`
2. An Scheme `U i` for each `i : J`.
3. An Scheme `V i j` for each `i j : J`.
  (Note that this is `J × J → Scheme` rather than `J → J → Scheme` to connect to the
  limits library easier.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the Schemes `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subschemes of the glued space.
-/
@[nolint has_inhabited_instance]
structure glue_data extends glue_data Scheme :=
  (f_open : ∀ i j, is_open_immersion (f i j))

attribute [instance] glue_data.f_open

namespace glue_data

variables (D : glue_data)

include D

local notation `𝖣` := D.to_glue_data

abbreviation to_LocallyRingedSpace_glue_data : LocallyRingedSpace.glue_data :=
{ f_open := D.f_open,
  to_glue_data := 𝖣 .map_glue_data forget_to_LocallyRingedSpace }

def glued_Scheme : Scheme :=
begin
  apply LocallyRingedSpace.is_open_immersion.Scheme
    D.to_LocallyRingedSpace_glue_data.to_glue_data.glued,
  intro x,
  obtain ⟨i, y, rfl⟩ := D.to_LocallyRingedSpace_glue_data.ι_jointly_surjective x,
  refine ⟨_, _ ≫ D.to_LocallyRingedSpace_glue_data.to_glue_data.ι i, _⟩,
  swap, exact (D.U i).affine_cover.map y,
  split,
  { dsimp,
    rw [coe_comp, set.range_comp],
    refine set.mem_image_of_mem _ _,
    exact (D.U i).affine_cover.covers y },
  { apply_instance },
end

instance : creates_colimit 𝖣 .diagram.multispan forget_to_LocallyRingedSpace :=
creates_colimit_of_fully_faithful_of_iso D.glued_Scheme
  (has_colimit.iso_of_nat_iso (𝖣 .diagram_iso forget_to_LocallyRingedSpace).symm)

instance : preserves_colimit 𝖣 .diagram.multispan forget_to_Top :=
begin
  delta forget_to_Top LocallyRingedSpace.forget_to_Top,
  apply_instance,
end

instance : has_multicoequalizer 𝖣 .diagram :=
has_colimit_of_created _ forget_to_LocallyRingedSpace

abbreviation glued := 𝖣 .glued
abbreviation ι := 𝖣 .ι

abbreviation iso_LocallyRingedSpace : D.glued.to_LocallyRingedSpace ≅
  D.to_LocallyRingedSpace_glue_data.to_glue_data.glued :=
𝖣 .glued_iso forget_to_LocallyRingedSpace

lemma ι_iso_LocallyRingedSpace_inv (i : D.J) :
  D.to_LocallyRingedSpace_glue_data.to_glue_data.ι i ≫
    D.iso_LocallyRingedSpace.inv = 𝖣 .ι i :=
𝖣 .ι_glued_iso_inv forget_to_LocallyRingedSpace i

instance ι_is_open_immersion (i : D.J) :
is_open_immersion (𝖣 .ι i) :=
by { rw ← D.ι_iso_LocallyRingedSpace_inv, apply_instance }

lemma ι_jointly_surjective (x : 𝖣 .glued.carrier) :
  ∃ (i : D.J) (y : (D.U i).carrier), (D.ι i).1.base y = x :=
𝖣 .ι_jointly_surjective (forget_to_Top ⋙ forget Top) x

@[simp, reassoc]
lemma glue_condition (i j : D.J) :
  D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i :=
𝖣 .glue_condition i j

def V_pullback_cone (i j : D.J) : pullback_cone (D.ι i) (D.ι j) :=
pullback_cone.mk (D.f i j) (D.t i j ≫ D.f j i) (by simp)

def V_pullback_cone_is_limit (i j : D.J) :
  is_limit (D.V_pullback_cone i j) :=
𝖣 .V_pullback_cone_is_limit_of_map forget_to_LocallyRingedSpace i j
  (D.to_LocallyRingedSpace_glue_data.V_pullback_cone_is_limit _ _)

def iso_carrier :
  D.glued.carrier ≅ D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data
    .to_PresheafedSpace_glue_data.to_Top_glue_data.to_glue_data.glued :=
begin
  refine (PresheafedSpace.forget _).map_iso _ ≪≫
    glue_data.glued_iso _ (PresheafedSpace.forget _),
  refine SheafedSpace.forget_to_PresheafedSpace.map_iso _ ≪≫
  SheafedSpace.glue_data.iso_PresheafedSpace _,
  refine LocallyRingedSpace.forget_to_SheafedSpace.map_iso _ ≪≫
  LocallyRingedSpace.glue_data.iso_SheafedSpace _,
  exact Scheme.glue_data.iso_LocallyRingedSpace _
end

lemma ι_iso_carrier_inv (i : D.J) :
  D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data
    .to_PresheafedSpace_glue_data.to_Top_glue_data.to_glue_data.ι i ≫ D.iso_carrier.inv =
    (D.ι i).1.base :=
begin
  delta iso_carrier,
  simp only [functor.map_iso_inv, iso.trans_inv, iso.trans_assoc,
    glue_data.ι_glued_iso_inv_assoc, functor.map_iso_trans, category.assoc],
  iterate 3 { erw ← comp_base },
  simp_rw ← category.assoc,
  rw D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data.ι_iso_PresheafedSpace_inv i,
  erw D.to_LocallyRingedSpace_glue_data.ι_iso_SheafedSpace_inv i,
  change (_ ≫ D.iso_LocallyRingedSpace.inv).1.base = _,
  rw D.ι_iso_LocallyRingedSpace_inv i
end

/--
An equivalence relation on `Σ i, D.U i` that holds iff `𝖣 .ι i x = 𝖣 .ι j y`.
See `Scheme.gluing_data.ι_eq_iff`.
 -/
def rel (a b : Σ i, ((D.U i).carrier : Type*)) : Prop :=
  a = b ∨ ∃ (x : (D.V (a.1, b.1)).carrier),
    (D.f _ _).1.base x = a.2 ∧ (D.t _ _ ≫ D.f _ _).1.base x = b.2

lemma ι_eq_iff (i j : D.J) (x : (D.U i).carrier) (y : (D.U j).carrier) :
  (𝖣 .ι i).1.base x = (𝖣 .ι j).1.base y ↔ D.rel ⟨i, x⟩ ⟨j, y⟩ :=
begin
  refine iff.trans _ (D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data
      .to_PresheafedSpace_glue_data.to_Top_glue_data.ι_eq_iff_rel i j x y),
  rw ← ((Top.mono_iff_injective D.iso_carrier.inv).mp infer_instance).eq_iff,
    simp_rw [← comp_apply, D.ι_iso_carrier_inv]
end

lemma is_open_iff (U : set D.glued.carrier) : is_open U ↔ ∀ i, is_open ((D.ι i).1.base ⁻¹' U) :=
begin
  rw ← (Top.homeo_of_iso D.iso_carrier.symm).is_open_preimage,
  rw Top.glue_data.is_open_iff,
  apply forall_congr,
  intro i,
  erw [← set.preimage_comp, ← coe_comp, ι_iso_carrier_inv]
end

end glue_data

end Scheme

end algebraic_geometry
-- #lint
