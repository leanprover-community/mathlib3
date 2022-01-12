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

Given a family of gluing data of structured spaces, we may glue them together.

The construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `algebraic_geometry.PresheafedSpace.glue_data`: A structure containing the family of gluing data.
* `category_theory.glue_data.glued`: The glued presheafed space.
    This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
    can be used.
* `category_theory.glue_data.ι`: The immersion `ι i : U i ⟶ glued` for each `i : J`.

## Main results

* `algebraic_geometry.PresheafedSpace.glue_data.ι_is_open_immersion`: The map `ι i : U i ⟶ glued`
  is an open immersion for each `i : J`.

## Implementation details

Almost the whole file is dedicated to showing tht `ι i` is an open immersion. The fact that
this is an open embedding of topological spaces follows from `topology.gluing.lean`, and it remains
to construct `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_X, ι i '' U)` for each `U ⊆ U i`.
Since `Γ(𝒪_X, ι i '' U)` is the the limit of `diagram_over_open`, the components of the structure
sheafs of the spaces in the gluing diagram, we need to construct a map
`ι_inv_app_π_app : Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_V, U_V)` for each `V` in the gluing diagram.
This is easy once we know that the `U_V` always falls in `U_i ∩ V`, so the restriction map suffices.
The hard part is to verify that these restriction maps and transition maps indeed commute, which
involves quite some diagram chasing and uses the cocycle identity.

-/

noncomputable theory

open topological_space category_theory opposite
open category_theory.limits algebraic_geometry.PresheafedSpace
open category_theory.glue_data

namespace algebraic_geometry

universes v u

variables (C : Type u) [category.{v} C]

namespace PresheafedSpace


/--
A family of gluing data consists of
1. An index type `J`
2. A presheafed space `U i` for each `i : J`.
3. A presheafed space `V i j` for each `i j : J`.
  (Note that this is `J × J → PresheafedSpace C` rather than `J → J → PresheafedSpace C` to
  connect to the limits library easier.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the spaces `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subspaces of the glued space.
-/
@[nolint has_inhabited_instance]
structure glue_data extends glue_data (PresheafedSpace C) :=
  (f_open : ∀ i j, is_open_immersion (f i j))

attribute [instance] glue_data.f_open

namespace glue_data

variables {C} (D : glue_data C)

local notation `𝖣` := D.to_glue_data
local notation `π₁` f `,` g := @pullback.fst _ _ _ _ _ f g _
local notation `π₂` f `,` g := @pullback.snd _ _ _ _ _ f g _

/-- The glue data of topological spaces associated to a family of glue data of PresheafedSpaces. -/
abbreviation to_Top_glue_data : Top.glue_data :=
{ f_open := λ i j, (D.f_open i j).base_open,
  to_glue_data := 𝖣 .map_glue_data (forget C) }

lemma ι_open_embedding [has_limits C] (i : D.J) : open_embedding (𝖣 .ι i).base :=
begin
  rw ← (show _ = (𝖣 .ι i).base, from 𝖣 .ι_glued_iso_inv (PresheafedSpace.forget _) _),
  exact open_embedding.comp (Top.homeo_of_iso
    (𝖣 .glued_iso (PresheafedSpace.forget _)).symm).open_embedding
    (D.to_Top_glue_data.ι_open_embedding i)
end

lemma pullback_fst_preimage_snd_image (X Y Z : Top) (f : X ⟶ Z) (g : Y ⟶ Z) (U : set X) :
  (π₂ f , g) '' ((π₁ f , g) ⁻¹' U) = g ⁻¹' (f '' U) :=
begin
  ext x,
  split,
  { rintros ⟨y, hy, rfl⟩,
    exact ⟨(π₁ f , g) y, hy,
     concrete_category.congr_hom pullback.condition y⟩ },
  { rintros ⟨y, hy, eq⟩,
     exact ⟨(Top.pullback_iso_prod_subtype f g).inv ⟨⟨_,_⟩,eq⟩, by simpa, by simp⟩ },
end

lemma pullback_base (i j k : D.J)  (S : set (D.V (i, j)).carrier) :
  ((π₂ (D.f i j) , (D.f i k)).base) '' (((π₁ (D.f i j) , (D.f i k)).base) ⁻¹' S) =
    (D.f i k).base ⁻¹' ((D.f i j).base '' S) :=
begin
  have eq₁ : _ = (π₁ (D.f i j) , (D.f i k)).base := preserves_pullback.iso_hom_fst (forget C) _ _,
  have eq₂ : _ = (π₂ (D.f i j) , (D.f i k)).base := preserves_pullback.iso_hom_snd (forget C) _ _,
  rw [← eq₁, ← eq₂, coe_comp, set.image_comp, coe_comp, set.preimage_comp,
    set.image_preimage_eq, pullback_fst_preimage_snd_image],
  refl,
  rw ← Top.epi_iff_surjective,
  apply_instance
end

@[simp, reassoc]
lemma f_inv_app_f_app (i j k : D.J)  (U : (opens (D.V (i, j)).carrier)) :
  (D.f_open i j).inv_app U ≫ (D.f i k).c.app _ =
    (π₁ (D.f i j) , (D.f i k)).c.app (op U) ≫
    (PresheafedSpace.is_open_immersion.pullback_snd_of_left (D.f i j) (D.f i k)).inv_app (unop _)
    ≫ (D.V _).presheaf.map (eq_to_hom (
      begin
        delta is_open_immersion.open_functor,
        dsimp only [functor.op, is_open_map.functor, opens.map, unop_op],
        congr,
        apply pullback_base,
      end)) :=
begin
  have := PresheafedSpace.congr_app (@pullback.condition _ _ _ _ _ (D.f i j) (D.f i k) _),
  dsimp only [comp_c_app] at this,
  rw [← cancel_epi (inv ((D.f_open i j).inv_app U)), is_iso.inv_hom_id_assoc,
    is_open_immersion.inv_inv_app],
  simp_rw category.assoc,
  erw [(π₁ (D.f i j) , (D.f i k)).c.naturality_assoc,
    reassoc_of this, ← functor.map_comp_assoc, is_open_immersion.inv_naturality_assoc,
    is_open_immersion.app_inv_app_assoc, ← (D.V (i, k)).presheaf.map_comp,
    ← (D.V (i, k)).presheaf.map_comp],
  convert (category.comp_id _).symm,
  erw (D.V (i, k)).presheaf.map_id,
  refl
end

/--
We can prove the `eq` along with the lemma. Thus this is bundled together here, and the
lemma itself is separated below.
-/
lemma snd_inv_app_t_app' (i j k : D.J) (U : opens (pullback (D.f i j) (D.f i k)).carrier) :
  ∃ eq, (is_open_immersion.pullback_snd_of_left (D.f i j) (D.f i k)).inv_app U ≫
  (D.t _ _).c.app _ ≫ (D.V (k, i)).presheaf.map (eq_to_hom eq) = (D.t' _ _ _).c.app _ ≫
    (is_open_immersion.pullback_fst_of_right (D.f k j) (D.f k i)).inv_app (unop _) :=
begin
  split,
  rw [← is_iso.eq_inv_comp, is_open_immersion.inv_inv_app, category.assoc,
    (D.t' k i j).c.naturality_assoc],
  simp_rw ← category.assoc,
  erw ← comp_c_app,
  rw [congr_app (D.t_fac k i j), comp_c_app],
  simp_rw category.assoc,
  erw [is_open_immersion.inv_naturality, is_open_immersion.inv_naturality_assoc,
    is_open_immersion.app_inv_app'_assoc],
  simp_rw [← (𝖣 .V (k, i)).presheaf.map_comp,
    eq_to_hom_map (functor.op _), eq_to_hom_op, eq_to_hom_trans],
  rintros x ⟨y, hy, eq⟩,
  replace eq := concrete_category.congr_arg ((𝖣 .t i k).base) eq,
  change ((π₂ _, _) ≫ D.t i k).base y = (D.t k i ≫ D.t i k).base x at eq,
  rw [𝖣 .t_inv, id_base, Top.id_app] at eq,
  subst eq,
  use (inv (D.t' k i j)).base y,
  change ((inv (D.t' k i j)) ≫ (π₁ _, _)).base y = _,
  congr' 2,
  rw [is_iso.inv_comp_eq, 𝖣 .t_fac_assoc, 𝖣 .t_inv, category.comp_id]
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

variable [has_limits C]

lemma ι_image_preimage_eq (i j : D.J) (U : opens (D.U i).carrier) :
  (opens.map (𝖣 .ι j).base).obj
    ((D.ι_open_embedding i).is_open_map.functor.obj U) =
      (D.f_open j i).open_functor.obj ((opens.map (𝖣 .t j i).base).obj
        ((opens.map (𝖣 .f i j).base).obj U)) :=
begin
  dsimp only [opens.map, is_open_map.functor],
  congr' 1,
  rw [← (show _ = (𝖣 .ι i).base, from 𝖣 .ι_glued_iso_inv (PresheafedSpace.forget _) i),
    ← (show _ = (𝖣 .ι j).base, from 𝖣 .ι_glued_iso_inv (PresheafedSpace.forget _) j),
    coe_comp, coe_comp, set.image_comp, set.preimage_comp, set.preimage_image_eq],
  refine eq.trans (D.to_Top_glue_data.preimage_image_eq_image' _ _ _) _,
  rw [coe_comp, set.image_comp],
  congr' 1,
  erw set.eq_preimage_iff_image_eq,
  rw ← set.image_comp,
  change (D.t i j ≫ D.t j i).base '' _ = _,
  rw 𝖣 .t_inv,
  { simp },
  { change function.bijective (Top.homeo_of_iso (as_iso _)),
    exact homeomorph.bijective _,
    apply_instance },
  { rw ← Top.mono_iff_injective,
    apply_instance }
end

/-- (Implementation). The map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{U_j}, 𝖣.ι j ⁻¹' (𝖣.ι i '' U))`. -/
def opens_image_preimage_map (i j : D.J) (U : opens (D.U i).carrier) :
  (D.U i).presheaf.obj (op U) ⟶ (D.U j).presheaf.obj
    (op ((opens.map (𝖣 .ι j).base).obj ((D.ι_open_embedding i).is_open_map.functor.obj U))) :=
(D.f i j).c.app (op U) ≫ (D.t j i).c.app _ ≫
  (D.f_open j i).inv_app (unop _) ≫ (𝖣 .U j).presheaf.map
    (eq_to_hom (D.ι_image_preimage_eq i j U)).op

lemma opens_image_preimage_map_app' (i j k : D.J) (U : opens (D.U i).carrier) :
  ∃ eq, D.opens_image_preimage_map i j U ≫ (D.f j k).c.app _ =
    ((π₁ (D.f j i) , (D.f j k)) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫
     (is_open_immersion.pullback_snd_of_left (D.f j i) (D.f j k)).inv_app (unop _) ≫
      (D.V (j, k)).presheaf.map (eq_to_hom eq) :=
begin
  split,
  delta opens_image_preimage_map,
  simp_rw category.assoc,
  rw [(D.f j k).c.naturality, f_inv_app_f_app_assoc],
  erw ← (D.V (j, k)).presheaf.map_comp,
  simp_rw ← category.assoc,
  erw [← comp_c_app, ← comp_c_app],
  simp_rw category.assoc,
  dsimp only [functor.op, unop_op, quiver.hom.unop_op],
  rw [eq_to_hom_map (opens.map _), eq_to_hom_op, eq_to_hom_trans],
  congr
end

lemma opens_image_preimage_map_app (i j k : D.J) (U : opens (D.U i).carrier) :
  D.opens_image_preimage_map i j U ≫ (D.f j k).c.app _ =
  ((π₁ (D.f j i) , (D.f j k)) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫
  (is_open_immersion.pullback_snd_of_left (D.f j i) (D.f j k)).inv_app (unop _) ≫
  (D.V (j, k)).presheaf.map (eq_to_hom ((opens_image_preimage_map_app' D i j k U).some)) :=
(opens_image_preimage_map_app' D i j k U).some_spec

lemma opens_image_preimage_map_app_assoc (i j k : D.J) (U : opens (D.U i).carrier)
  {X' : C} (f' : _ ⟶ X') :
  D.opens_image_preimage_map i j U ≫ (D.f j k).c.app _ ≫ f' =
    ((π₁ (D.f j i) , (D.f j k)) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫
    (is_open_immersion.pullback_snd_of_left (D.f j i) (D.f j k)).inv_app (unop _) ≫
    (D.V (j, k)).presheaf.map (eq_to_hom ((opens_image_preimage_map_app' D i j k U).some)) ≫ f' :=
by simpa only [category.assoc]
  using congr_arg (λ g, g ≫ f') (opens_image_preimage_map_app D i j k U)

/-- (Implementation) Given a open subset of one of the spaces `U ⊆ Uᵢ`, The sheaf component of
the image `ι '' U` in the glued space is the limit of this diagram. -/
abbreviation diagram_over_open {i : D.J} (U : opens (D.U i).carrier) :
  (walking_multispan _ _)ᵒᵖ ⥤ C :=
componentwise_diagram 𝖣 .diagram.multispan ((D.ι_open_embedding i).is_open_map.functor.obj U)

/-- (Implementation) We construct the map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_V, U_V)` for each `V` in the gluing
diagram. We will lift these maps into `ι_inv_app`. -/
def ι_inv_app_π_app (i : D.J) (U : opens (D.U i).carrier) (j) :
  (𝖣 .U i).presheaf.obj (op U) ⟶ (D.diagram_over_open U).obj (op j) :=
begin
  rcases j with (⟨j, k⟩|j),
  { refine D.opens_image_preimage_map i j U ≫ (D.f j k).c.app _ ≫
      (D.V (j, k)).presheaf.map (eq_to_hom _),
    dsimp only [functor.op, opens.map, unop_op],
    congr' 2,
    rw set.preimage_preimage,
    change (D.f j k ≫ 𝖣 .ι j).base ⁻¹' _ = _,
    congr' 3,
    exact colimit.w 𝖣 .diagram.multispan (walking_multispan.hom.fst (j, k)) },
  { exact D.opens_image_preimage_map i j U }
end

/-- (Implementation) The natural map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_X, 𝖣.ι i '' U)`.
This forms the inverse of `(𝖣.ι i).c.app (op U)`. -/
def ι_inv_app (i : D.J) (U : opens (D.U i).carrier) :
  (D.U i).presheaf.obj (op U) ⟶ limit (D.diagram_over_open U) :=
limit.lift (D.diagram_over_open U)
{ X := (D.U i).presheaf.obj (op U),
  π := { app := λ j, D.ι_inv_app_π_app i U (unop j),
  naturality' := λ X Y f', begin
    induction X using opposite.rec,
    induction Y using opposite.rec,
    let f : Y ⟶ X := f'.unop, have : f' = f.op := rfl, clear_value f, subst this,
    rcases f with (_|⟨j,k⟩|⟨j,k⟩),
    { erw [category.id_comp, category_theory.functor.map_id],
      rw category.comp_id },
    { erw category.id_comp, congr' 1 },
    erw category.id_comp,
    change D.opens_image_preimage_map i j U ≫ (D.f j k).c.app _ ≫
      (D.V (j, k)).presheaf.map (eq_to_hom _) = D.opens_image_preimage_map _ _ _ ≫
      ((D.f k j).c.app _ ≫ (D.t j k).c.app _) ≫ (D.V (j, k)).presheaf.map (eq_to_hom _),
    erw opens_image_preimage_map_app_assoc,
    simp_rw category.assoc,
    erw [opens_image_preimage_map_app_assoc, (D.t j k).c.naturality_assoc],
    rw snd_inv_app_t_app_assoc,
    erw ← PresheafedSpace.comp_c_app_assoc,
    have : D.t' j k i ≫ (π₁ _, _) ≫ D.t k i ≫ 𝖣 .f i k =
      (pullback_symmetry _ _).hom ≫ (π₁ _, _) ≫ D.t j i ≫ D.f i j,
    { rw [← 𝖣 .t_fac_assoc, 𝖣 .t'_comp_eq_pullback_symmetry_assoc,
        pullback_symmetry_hom_comp_snd_assoc, pullback.condition, 𝖣 .t_fac_assoc] },
    rw congr_app this,
    erw PresheafedSpace.comp_c_app_assoc (pullback_symmetry _ _).hom,
    simp_rw category.assoc,
    congr' 1,
    rw ← is_iso.eq_inv_comp,
    erw is_open_immersion.inv_inv_app,
    simp_rw category.assoc,
    erw [nat_trans.naturality_assoc, ← PresheafedSpace.comp_c_app_assoc,
      congr_app (pullback_symmetry_hom_comp_snd _ _)],
    simp_rw category.assoc,
    erw [is_open_immersion.inv_naturality_assoc, is_open_immersion.inv_naturality_assoc,
      is_open_immersion.inv_naturality_assoc, is_open_immersion.app_inv_app_assoc],
    repeat { erw ← (D.V (j, k)).presheaf.map_comp },
    congr,
  end } }
.

-- needs a docstring and a better name
abbreviation foo (i j : D.J) (U : opens (D.U i).carrier) :=
limit.π (D.diagram_over_open U) (op (walking_multispan.right j))

lemma ι_inv_app_π (i : D.J) (U : opens (D.U i).carrier) :
  ∃ eq, D.ι_inv_app i U ≫ (D.foo i i U) =
    (D.U i).presheaf.map (eq_to_hom eq) :=
begin
  split,
  delta ι_inv_app,
  rw limit.lift_π,
  change D.opens_image_preimage_map i i U = _,
  dsimp [opens_image_preimage_map],
  rw [congr_app (D.t_id _), id_c_app, ← functor.map_comp],
  erw [is_open_immersion.inv_naturality_assoc, is_open_immersion.app_inv_app'_assoc],
  simp only [eq_to_hom_op, eq_to_hom_trans, eq_to_hom_map (functor.op _), ← functor.map_comp],
  rw set.range_iff_surjective.mpr _,
  { simp },
  { rw ← Top.epi_iff_surjective,
    apply_instance }
end

-- needs a docstring and a better name
abbreviation bar (i : D.J) (U : opens (D.U i).carrier) :=
(D.U i).presheaf.map (eq_to_iso (D.ι_inv_app_π i U).some).inv

lemma π_ι_inv_app_π (i j : D.J) (U : opens (D.U i).carrier) :
  (D.foo i i U) ≫ D.bar i U ≫ D.ι_inv_app i U ≫ (D.foo i j U) = D.foo i j U :=
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
  D.foo i i U ≫ D.bar i U ≫ D.ι_inv_app i U = 𝟙 _ :=
begin
  ext j,
  induction j using opposite.rec,
  rcases j with (⟨j, k⟩|⟨j⟩),
  { rw [← limit.w (componentwise_diagram 𝖣 .diagram.multispan _)
      (quiver.hom.op (walking_multispan.hom.fst (j, k))), ← category.assoc, category.id_comp],
    congr' 1,
    simp_rw category.assoc,
    apply π_ι_inv_app_π },
  { simp_rw category.assoc,
    rw category.id_comp,
    apply π_ι_inv_app_π }
end

instance componentwise_diagram_π_is_iso (i : D.J) (U : opens (D.U i).carrier) :
  is_iso (D.foo i i U) :=
begin
  use D.bar i U ≫ D.ι_inv_app i U,
  split,
  { apply π_ι_inv_app_eq_id },
  { rw [category.assoc, (D.ι_inv_app_π _ _).some_spec],
    exact iso.inv_hom_id ((D.to_glue_data.U i).presheaf.map_iso (eq_to_iso _)) }
end

instance ι_is_open_immersion (i : D.J) :
  is_open_immersion (𝖣 .ι i) :=
{ base_open := D.ι_open_embedding i,
  c_iso := λ U, by { erw ← colimit_presheaf_obj_iso_componentwise_limit_hom_π, apply_instance } }

end glue_data

end PresheafedSpace

end algebraic_geometry
