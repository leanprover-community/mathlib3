/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import topology.gluing
import algebraic_geometry.presheafed_space.open_immersion
import algebraic_geometry.presheafed_space.has_colimits

/-!
# Gluing Topological spaces

Given a family of gluing data, consisting of
1. An index type `ι`
2. A topological space `U i` for each `i : ι`.
3. An open subset `V i j ⊆ U i` for each `i j : ι`.
4. A transition map `f i j : V i j ⟶ V j i` for each `i j : ι`.
such that
5. `V i i = U i`.
6. `f i i` is the identity.
7. `f i j x ∈ V j k` for all `x ∈ V i j ∩ V i k`.
8. `f i j ≫ f j k = f i k`.

We can then glue the topological spaces `U i` along `V i j`.

THe construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `Top.gluing_data`: A structure containing the family of gluing data.
* `Top.gluing_data.glued`: The glued topological space.
    This is defined as the coequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API can
    be used.
* `Top.gluing_data.imm`: The immersion `imm i : U i ⟶ glued` for each `i : ι`.
* `Top.gluing_data.rel`: A relation on `Σ i, D.U i` defined by `⟨i, x⟩ ~ ⟨j, y⟩` iff
    `⟨i, x⟩ = ⟨j, y⟩` or `f i j x = y`. See `Top.gluing_data.imm_eq_iff_rel`.

## Main results

* `Top.gluing_data.is_open_iff`: A set in `glued` is open iff its preimage along each `imm i` is
    open.
* `Top.gluing_data.imm_jointly_surjective`: The `imm i`s are jointly surjective.
* `Top.gluing_data.glue_condition` : `f i j ≫ imm j = imm i`.
* `Top.gluing_data.rel_equiv`: `rel` is an equivalence relation.
* `Top.gluing_data.imm_eq_iff_rel`: `imm i x = imm j y ↔ ⟨i, x⟩ ~ ⟨j, y⟩`.
* `Top.gluing_data.image_inter`: The intersection of the images of `U i` and `U j` in `glued` is
    `V i j`.
* `Top.gluing_data.preimage_range`: The preimage of the image of `U i` in `U j` is `V i j`.
* `Top.gluing_data.preimage_image_eq_preimage_f`: The preimage of the image of some `U ⊆ U i` is
    given by the preimage along `f j i`.
* `Top.gluing_data.imm_open_embedding`: Each of the `imm i`s are open embeddings.

-/

noncomputable theory

open topological_space category_theory opposite
open category_theory.limits algebraic_geometry.PresheafedSpace
namespace algebraic_geometry

universes v u

variables (C : Type u) [category.{v} C]

/--
A family of gluing data consists of
1. An index type `ι`
2. A topological space `U i` for each `i : ι`.
3. An open subset `V i j ⊆ U i` for each `i j : ι`.
4. A transition map `f i j : V i j ⟶ V j i` for each `i j : ι`.
such that
5. `V i i = U i`.
6. `f i i` is the identity.
7. `f i j x ∈ V j k` for all `x ∈ V i j ∩ V i k`.
8. `f i j ≫ f j k = f i k`.

We can then glue the topological spaces `U i` along `V i j`.
-/
@[nolint has_inhabited_instance]
structure glue_data extends glue_data (PresheafedSpace C) :=
  (f_open : ∀ i j, is_open_immersion (f i j))

attribute [instance] glue_data.f_open

open category_theory.glue_data

namespace glue_data

variables {C} (D : glue_data C) [has_limits C]

local notation `D'` := D.to_glue_data

abbreviation to_top_glue_data : Top.glue_data :=
{ f_open := λ i j, (D.f_open i j).base_open,
  to_glue_data := D' .map_glue_data (forget C) }

section end

def diagram_iso : D' .diagram.multispan ⋙ forget C ≅
  D.to_top_glue_data.to_glue_data.diagram.multispan :=
D' .diagram_iso _

def carrier_iso : D' .glued.carrier ≅ D.to_top_glue_data.to_glue_data.glued :=
preserves_colimit_iso (forget C) D' .diagram.multispan ≪≫ colim.map_iso D.diagram_iso

lemma imm_carrier_iso_eq (i : D.ι) :
  (D' .imm i).base ≫ D.carrier_iso.hom = D.to_top_glue_data.imm i :=
begin
  erw ← category.assoc,
  rw ← iso.eq_comp_inv,
  erw ι_colim_map,
  change (forget C).map _ ≫ _ = _,
  erw ι_preserves_colimits_iso_hom,
  erw category.id_comp
end

lemma imm_carrier_inv_eq (i : D.ι) :
  D.to_top_glue_data.imm i ≫ D.carrier_iso.inv = (D' .imm i).base :=
by { rw ← imm_carrier_iso_eq, simp }

lemma imm_open_embedding (i : D.ι) : open_embedding (D' .imm i).base :=
begin
  rw ← imm_carrier_inv_eq,
  exact open_embedding.comp (Top.homeo_of_iso D.carrier_iso.symm).open_embedding
    (D.to_top_glue_data.imm_open_embedding i)
end

lemma lem (i j k : D.ι)  (U : (opens (D.V (i, j)).carrier)) :
  (D.f_open i j).inv_app U ≫ (D.f i k).c.app _ =
    (pullback.fst : pullback (D.f i j) (D.f i k) ⟶ _).c.app (op U) ≫
    (PresheafedSpace.is_open_immersion.pullback_snd_of_left (D.f i j) (D.f i k)).inv_app (unop _)
    ≫ (D.V _).presheaf.map (eq_to_hom (by { delta is_open_immersion.open_functor
, dsimp only [functor.op, is_open_map.functor, opens.map, unop_op], congr, })) :=
begin
  -- rw ← cancel_epi (inv ((D.f_open i j).inv_app U)),
  -- rw is_iso.inv_hom_id_assoc,
  -- rw PresheafedSpace.is_open_immersion.inv_inv_app,
  -- simp_rw category.assoc,
  -- erw (pullback.fst : pullback (D.f i j) (D.f i k) ⟶ _).c.naturality_assoc,
  -- have := PresheafedSpace.congr_app (@pullback.condition _ _ _ _ _ (D.f i j) (D.f i k) _),
  -- dsimp only [comp_c_app] at this,
  -- reassoc! this,
  -- erw this,
  -- erw ← functor.map_comp_assoc,
  -- erw PresheafedSpace.is_open_immersion.inv_naturality_assoc,
  -- erw PresheafedSpace.is_open_immersion.app_inv_app_assoc,
  -- erw ← (D.V (i, k)).presheaf.map_comp,
  -- erw ← (D.V (i, k)).presheaf.map_comp,
  -- convert (category.comp_id _).symm,
  -- erw (D.V (i, k)).presheaf.map_id,
  -- refl,
end

def opens_image_preimage_map (i j : D.ι) (U : opens (D.U i).carrier) :
  (D.U i).presheaf.obj (op U) ⟶ (D.U j).presheaf.obj
    (op ((opens.map (D' .imm j).base).obj ((D.imm_open_embedding i).is_open_map.functor.obj U))) :=
begin
  refine (D.f i j).c.app (op U) ≫ _,
  change (D.to_glue_data.V (i, j)).presheaf.obj _ ⟶ _,
  dsimp only [functor.op],
  let H : is_open_immersion (D.t i j) := infer_instance,
  refine H.inv_app _ ≫ (D.f_open j i).inv_app _ ≫ (D.to_glue_data.U j).presheaf.map (eq_to_hom _).op,
  dsimp only [opens.map, is_open_map.functor],
  congr' 1,
  dsimp,
  rw [← D.imm_carrier_inv_eq,← D.imm_carrier_inv_eq, coe_comp, coe_comp],
  conv_lhs { erw [← set.image_image, ← set.preimage_preimage] },
  rw set.preimage_image_eq,
  dsimp only,
  erw Top.glue_data.preimage_image_eq_image',
  rw coe_comp,
  rw set.image_image,
  refl,
  rw ← Top.mono_iff_injective,
  apply_instance
end

section end

lemma opens_image_preimage_map (i j k : D.ι) (U : opens (D.U i).carrier) :
  D.opens_image_preimage_map i j U ≫
    (D.to_glue_data.f j k).c.app _ ≫
        (D.to_glue_data.V (j, k)).presheaf.map (eq_to_hom _) =
          D.opens_image_preimage_map i k U ≫
            (D.to_glue_data.f k j).c.app _ ≫ (D.to_glue_data.t j k).c.app _


def inv_f (i : D.ι) (U : opens (D.U i).carrier) :
  (D.U i).presheaf.obj (op U) ⟶ limit (pointwise_diagram D.to_glue_data.diagram.multispan
    ((D.imm_open_embedding i).is_open_map.functor.obj U)) :=
limit.lift (pointwise_diagram D.to_glue_data.diagram.multispan
    ((D.imm_open_embedding i).is_open_map.functor.obj U))
{ X := (D.U i).presheaf.obj (op U),
  π := { app :=
  begin
    intro j,
    induction j using opposite.rec,
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
  end,
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
          (_ ≫ _ ≫ _) ≫
            ((D.f k j).c.app _ ≫ (D.t j k).c.app _) ≫
              (D.V (j, k)).presheaf.map (eq_to_hom _),
    simp_rw category.assoc,
    erw (D.f k j).c.naturality_assoc,
    -- erw is_open_immersion.app_inv_app_assoc,
    -- erw is_open_immersion.inv_naturality_assoc,
    -- dsimp [pointwise_diagram, opens_image_preimage_map],
    -- simp,

  end }

lemma lem (i : D.ι) (U : opens (D.U i)) :

end glue_data

end algebraic_geometry
