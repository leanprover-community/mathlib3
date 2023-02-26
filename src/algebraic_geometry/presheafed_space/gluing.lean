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

Given a family of gluing data of structured spaces (presheafed spaces, sheafed spaces, or locally
ringed spaces), we may glue them together.

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
* `algebraic_geometry.PresheafedSpace.glue_data.ι_jointly_surjective` : The underlying maps of
  `ι i : U i ⟶ glued` are jointly surjective.
* `algebraic_geometry.PresheafedSpace.glue_data.V_pullback_cone_is_limit` : `V i j` is the pullback
  (intersection) of `U i` and `U j` over the glued space.

Analogous results are also provided for `SheafedSpace` and `LocallyRingedSpace`.

## Implementation details

Almost the whole file is dedicated to showing tht `ι i` is an open immersion. The fact that
this is an open embedding of topological spaces follows from `topology.gluing.lean`, and it remains
to construct `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_X, ι i '' U)` for each `U ⊆ U i`.
Since `Γ(𝒪_X, ι i '' U)` is the the limit of `diagram_over_open`, the components of the structure
sheafs of the spaces in the gluing diagram, we need to construct a map
`ι_inv_app_π_app : Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_V, U_V)` for each `V` in the gluing diagram.

We will refer to ![this diagram](https://i.imgur.com/P0phrwr.png) in the following doc strings.
The `X` is the glued space, and the dotted arrow is a partial inverse guaranteed by the fact
that it is an open immersion. The map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{U_j}, _)` is given by the composition
of the red arrows, and the map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{V_{jk}}, _)` is given by the composition of the
blue arrows. To lift this into a map from `Γ(𝒪_X, ι i '' U)`, we also need to show that these
commute with the maps in the diagram (the green arrows), which is just a lengthy diagram-chasing.

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
@[nolint has_nonempty_instance]
structure glue_data extends glue_data (PresheafedSpace.{v} C) :=
(f_open : ∀ i j, is_open_immersion (f i j))

attribute [instance] glue_data.f_open

namespace glue_data

variables {C} (D : glue_data C)

local notation `𝖣` := D.to_glue_data
local notation `π₁ `i`, `j`, `k := @pullback.fst _ _ _ _ _ (D.f i j) (D.f i k) _
local notation `π₂ `i`, `j`, `k := @pullback.snd _ _ _ _ _ (D.f i j) (D.f i k) _
local notation `π₁⁻¹ `i`, `j`, `k :=
(PresheafedSpace.is_open_immersion.pullback_fst_of_right (D.f i j) (D.f i k)).inv_app
local notation `π₂⁻¹ `i`, `j`, `k :=
(PresheafedSpace.is_open_immersion.pullback_snd_of_left (D.f i j) (D.f i k)).inv_app

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

lemma pullback_base (i j k : D.J)  (S : set (D.V (i, j)).carrier) :
  (π₂ i, j, k) '' ((π₁ i, j, k) ⁻¹' S) = D.f i k ⁻¹' (D.f i j '' S) :=
begin
  have eq₁ : _ = (π₁ i, j, k).base := preserves_pullback.iso_hom_fst (forget C) _ _,
  have eq₂ : _ = (π₂ i, j, k).base := preserves_pullback.iso_hom_snd (forget C) _ _,
  rw [coe_to_fun_eq, coe_to_fun_eq, ← eq₁, ← eq₂, coe_comp, set.image_comp, coe_comp,
    set.preimage_comp, set.image_preimage_eq, Top.pullback_snd_image_fst_preimage],
  refl,
  rw ← Top.epi_iff_surjective,
  apply_instance
end

/-- The red and the blue arrows in ![this diagram](https://i.imgur.com/0GiBUh6.png) commute. -/
@[simp, reassoc]
lemma f_inv_app_f_app (i j k : D.J)  (U : (opens (D.V (i, j)).carrier)) :
  (D.f_open i j).inv_app U ≫ (D.f i k).c.app _ =
    (π₁ i, j, k).c.app (op U) ≫ (π₂⁻¹ i, j, k) (unop _) ≫ (D.V _).presheaf.map (eq_to_hom
      (begin
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
  erw [(π₁ i, j, k).c.naturality_assoc,
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
  ∃ eq, (π₂⁻¹ i, j, k) U ≫ (D.t k i).c.app _ ≫ (D.V (k, i)).presheaf.map (eq_to_hom eq) =
    (D.t' k i j).c.app _ ≫ (π₁⁻¹ k, j, i) (unop _) :=
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
  change ((π₂ i, j, k) ≫ D.t i k).base y = (D.t k i ≫ D.t i k).base x at eq,
  rw [𝖣 .t_inv, id_base, Top.id_app] at eq,
  subst eq,
  use (inv (D.t' k i j)).base y,
  change ((inv (D.t' k i j)) ≫ (π₁ k, i, j)).base y = _,
  congr' 2,
  rw [is_iso.inv_comp_eq, 𝖣 .t_fac_assoc, 𝖣 .t_inv, category.comp_id]
end

/-- The red and the blue arrows in ![this diagram](https://i.imgur.com/q6X1GJ9.png) commute. -/
@[simp, reassoc]
lemma snd_inv_app_t_app (i j k : D.J) (U : opens (pullback (D.f i j) (D.f i k)).carrier) :
  (π₂⁻¹ i, j, k) U ≫ (D.t k i).c.app _ = (D.t' k i j).c.app _ ≫ (π₁⁻¹ k, j, i) (unop _) ≫
    (D.V (k, i)).presheaf.map (eq_to_hom (D.snd_inv_app_t_app' i j k U).some.symm) :=
begin
  have e := (D.snd_inv_app_t_app' i j k U).some_spec,
  reassoc! e,
  rw ← e,
  simp [eq_to_hom_map],
end

variable [has_limits C]

lemma ι_image_preimage_eq (i j : D.J) (U : opens (D.U i).carrier) :
  (opens.map (𝖣 .ι j).base).obj ((D.ι_open_embedding i).is_open_map.functor.obj U) =
  (D.f_open j i).open_functor.obj ((opens.map (𝖣 .t j i).base).obj
    ((opens.map (𝖣 .f i j).base).obj U)) :=
begin
  ext1,
  dsimp only [opens.map_coe, is_open_map.functor_obj_coe],
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

/-- (Implementation). The map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{U_j}, 𝖣.ι j ⁻¹' (𝖣.ι i '' U))` -/
def opens_image_preimage_map (i j : D.J) (U : opens (D.U i).carrier) :
  (D.U i).presheaf.obj (op U) ⟶ (D.U j).presheaf.obj _ :=
(D.f i j).c.app (op U) ≫ (D.t j i).c.app _ ≫ (D.f_open j i).inv_app (unop _) ≫
  (𝖣 .U j).presheaf.map (eq_to_hom (D.ι_image_preimage_eq i j U)).op

lemma opens_image_preimage_map_app' (i j k : D.J) (U : opens (D.U i).carrier) :
  ∃ eq, D.opens_image_preimage_map i j U ≫ (D.f j k).c.app _ =
    ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫ (π₂⁻¹ j, i, k) (unop _) ≫
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

/-- The red and the blue arrows in ![this diagram](https://i.imgur.com/mBzV1Rx.png) commute. -/
lemma opens_image_preimage_map_app (i j k : D.J) (U : opens (D.U i).carrier) :
  D.opens_image_preimage_map i j U ≫ (D.f j k).c.app _ =
  ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫ (π₂⁻¹ j, i, k) (unop _) ≫
    (D.V (j, k)).presheaf.map (eq_to_hom ((opens_image_preimage_map_app' D i j k U).some)) :=
(opens_image_preimage_map_app' D i j k U).some_spec

-- This is proved separately since `reassoc` somehow timeouts.
lemma opens_image_preimage_map_app_assoc (i j k : D.J) (U : opens (D.U i).carrier)
  {X' : C} (f' : _ ⟶ X') :
  D.opens_image_preimage_map i j U ≫ (D.f j k).c.app _ ≫ f' =
    ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫ (π₂⁻¹ j, i, k) (unop _) ≫
    (D.V (j, k)).presheaf.map (eq_to_hom ((opens_image_preimage_map_app' D i j k U).some)) ≫ f' :=
by simpa only [category.assoc]
  using congr_arg (λ g, g ≫ f') (opens_image_preimage_map_app D i j k U)

/-- (Implementation) Given an open subset of one of the spaces `U ⊆ Uᵢ`, the sheaf component of
the image `ι '' U` in the glued space is the limit of this diagram. -/
abbreviation diagram_over_open {i : D.J} (U : opens (D.U i).carrier) :
  (walking_multispan _ _)ᵒᵖ ⥤ C :=
componentwise_diagram 𝖣 .diagram.multispan ((D.ι_open_embedding i).is_open_map.functor.obj U)

/-- (Implementation)
The projection from the limit of `diagram_over_open` to a component of `D.U j`. -/
abbreviation diagram_over_open_π {i : D.J} (U : opens (D.U i).carrier) (j : D.J) :=
limit.π (D.diagram_over_open U) (op (walking_multispan.right j))

/-- (Implementation) We construct the map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_V, U_V)` for each `V` in the gluing
diagram. We will lift these maps into `ι_inv_app`. -/
def ι_inv_app_π_app {i : D.J} (U : opens (D.U i).carrier) (j) :
  (𝖣 .U i).presheaf.obj (op U) ⟶ (D.diagram_over_open U).obj (op j) :=
begin
  rcases j with (⟨j, k⟩|j),
  { refine D.opens_image_preimage_map i j U ≫ (D.f j k).c.app _ ≫
      (D.V (j, k)).presheaf.map (eq_to_hom _),
    rw [functor.op_obj],
    congr' 1, ext1,
    dsimp only [functor.op_obj, opens.map_coe, unop_op, is_open_map.functor_obj_coe],
    rw set.preimage_preimage,
    change (D.f j k ≫ 𝖣 .ι j).base ⁻¹' _ = _,
    congr' 3,
    exact colimit.w 𝖣 .diagram.multispan (walking_multispan.hom.fst (j, k)) },
  { exact D.opens_image_preimage_map i j U }
end

/-- (Implementation) The natural map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_X, 𝖣.ι i '' U)`.
This forms the inverse of `(𝖣.ι i).c.app (op U)`. -/
def ι_inv_app {i : D.J} (U : opens (D.U i).carrier) :
  (D.U i).presheaf.obj (op U) ⟶ limit (D.diagram_over_open U) :=
limit.lift (D.diagram_over_open U)
{ X := (D.U i).presheaf.obj (op U),
  π := { app := λ j, D.ι_inv_app_π_app U (unop j),
  naturality' := λ X Y f', begin
    induction X using opposite.rec,
    induction Y using opposite.rec,
    let f : Y ⟶ X := f'.unop, have : f' = f.op := rfl, clear_value f, subst this,
    rcases f with (_|⟨j,k⟩|⟨j,k⟩),
    { erw [category.id_comp, category_theory.functor.map_id],
      rw category.comp_id },
    { erw category.id_comp, congr' 1 },
    erw category.id_comp,
    -- It remains to show that the blue is equal to red + green in the original diagram.
    -- The proof strategy is illustrated in ![this diagram](https://i.imgur.com/mBzV1Rx.png)
    -- where we prove red = pink = light-blue = green = blue.
    change D.opens_image_preimage_map i j U ≫ (D.f j k).c.app _ ≫
      (D.V (j, k)).presheaf.map (eq_to_hom _) = D.opens_image_preimage_map _ _ _ ≫
      ((D.f k j).c.app _ ≫ (D.t j k).c.app _) ≫ (D.V (j, k)).presheaf.map (eq_to_hom _),
    erw opens_image_preimage_map_app_assoc,
    simp_rw category.assoc,
    erw [opens_image_preimage_map_app_assoc, (D.t j k).c.naturality_assoc],
    rw snd_inv_app_t_app_assoc,
    erw ← PresheafedSpace.comp_c_app_assoc,
    -- light-blue = green is relatively easy since the part that differs does not involve
    -- partial inverses.
    have : D.t' j k i ≫ (π₁ k, i, j) ≫ D.t k i ≫ 𝖣 .f i k =
      (pullback_symmetry _ _).hom ≫ (π₁ j, i, k) ≫ D.t j i ≫ D.f i j,
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

/-- `ι_inv_app` is the left inverse of `D.ι i` on `U`. -/
lemma ι_inv_app_π {i : D.J} (U : opens (D.U i).carrier) :
  ∃ eq, D.ι_inv_app U ≫ D.diagram_over_open_π U i = (D.U i).presheaf.map (eq_to_hom eq) :=
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

/-- The `eq_to_hom` given by `ι_inv_app_π`. -/
abbreviation ι_inv_app_π_eq_map {i : D.J} (U : opens (D.U i).carrier) :=
(D.U i).presheaf.map (eq_to_iso (D.ι_inv_app_π U).some).inv

/-- `ι_inv_app` is the right inverse of `D.ι i` on `U`. -/
lemma π_ι_inv_app_π (i j : D.J) (U : opens (D.U i).carrier) :
  D.diagram_over_open_π U i ≫ D.ι_inv_app_π_eq_map U ≫ D.ι_inv_app U ≫
    D.diagram_over_open_π U j = D.diagram_over_open_π U j :=
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

/-- `ι_inv_app` is the inverse of `D.ι i` on `U`. -/
lemma π_ι_inv_app_eq_id (i : D.J) (U : opens (D.U i).carrier) :
  D.diagram_over_open_π U i ≫ D.ι_inv_app_π_eq_map U ≫ D.ι_inv_app U = 𝟙 _ :=
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
  is_iso (D.diagram_over_open_π U i) :=
begin
  use D.ι_inv_app_π_eq_map U ≫ D.ι_inv_app U,
  split,
  { apply π_ι_inv_app_eq_id },
  { rw [category.assoc, (D.ι_inv_app_π _).some_spec],
    exact iso.inv_hom_id ((D.to_glue_data.U i).presheaf.map_iso (eq_to_iso _)) }
end

instance ι_is_open_immersion (i : D.J) :
  is_open_immersion (𝖣 .ι i) :=
{ base_open := D.ι_open_embedding i,
  c_iso := λ U, by { erw ← colimit_presheaf_obj_iso_componentwise_limit_hom_π, apply_instance } }

/-- The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.

Vᵢⱼ ⟶ Uᵢ
 |      |
 ↓      ↓
 Uⱼ ⟶ X
-/
def V_pullback_cone_is_limit (i j : D.J) : is_limit (𝖣 .V_pullback_cone i j) :=
pullback_cone.is_limit_aux' _ $ λ s,
begin
  refine ⟨_, _, _, _⟩,
  { refine PresheafedSpace.is_open_immersion.lift (D.f i j) s.fst _,
    erw ← D.to_Top_glue_data.preimage_range j i,
    have : s.fst.base ≫ D.to_Top_glue_data.to_glue_data.ι i =
      s.snd.base ≫ D.to_Top_glue_data.to_glue_data.ι j,
    { rw [← 𝖣 .ι_glued_iso_hom (PresheafedSpace.forget _) _,
        ← 𝖣 .ι_glued_iso_hom (PresheafedSpace.forget _) _],
      have := congr_arg PresheafedSpace.hom.base s.condition,
      rw [comp_base, comp_base] at this,
      reassoc! this,
      exact this _ },
    rw [← set.image_subset_iff, ← set.image_univ, ← set.image_comp, set.image_univ,
      ← coe_comp, this, coe_comp, ← set.image_univ, set.image_comp],
    exact set.image_subset_range _ _ },
  { apply is_open_immersion.lift_fac },
  { rw [← cancel_mono (𝖣 .ι j), category.assoc, ← (𝖣 .V_pullback_cone i j).condition],
    conv_rhs { rw ← s.condition },
    erw is_open_immersion.lift_fac_assoc },
  { intros m e₁ e₂, rw ← cancel_mono (D.f i j), erw e₁, rw is_open_immersion.lift_fac }
end

lemma ι_jointly_surjective (x : 𝖣 .glued) :
  ∃ (i : D.J) (y : D.U i), (𝖣 .ι i).base y = x :=
𝖣 .ι_jointly_surjective (PresheafedSpace.forget _ ⋙ category_theory.forget Top) x

end glue_data

end PresheafedSpace

namespace SheafedSpace

variables (C) [has_products.{v} C]

/--
A family of gluing data consists of
1. An index type `J`
2. A sheafed space `U i` for each `i : J`.
3. A sheafed space `V i j` for each `i j : J`.
  (Note that this is `J × J → SheafedSpace C` rather than `J → J → SheafedSpace C` to
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
@[nolint has_nonempty_instance]
structure glue_data extends glue_data (SheafedSpace.{v} C) :=
(f_open : ∀ i j, SheafedSpace.is_open_immersion (f i j))

attribute [instance] glue_data.f_open

namespace glue_data

variables {C} (D : glue_data C)

local notation `𝖣` := D.to_glue_data

/-- The glue data of presheafed spaces associated to a family of glue data of sheafed spaces. -/
abbreviation to_PresheafedSpace_glue_data : PresheafedSpace.glue_data C :=
{ f_open := D.f_open,
  to_glue_data := 𝖣 .map_glue_data forget_to_PresheafedSpace }

variable [has_limits C]

/-- The gluing as sheafed spaces is isomorphic to the gluing as presheafed spaces. -/
abbreviation iso_PresheafedSpace : 𝖣 .glued.to_PresheafedSpace ≅
  D.to_PresheafedSpace_glue_data.to_glue_data.glued :=
𝖣 .glued_iso forget_to_PresheafedSpace

lemma ι_iso_PresheafedSpace_inv (i : D.J) :
  D.to_PresheafedSpace_glue_data.to_glue_data.ι i ≫ D.iso_PresheafedSpace.inv = 𝖣 .ι i :=
𝖣 .ι_glued_iso_inv _ _

instance ι_is_open_immersion (i : D.J) :
  is_open_immersion (𝖣 .ι i) :=
by { rw ← D.ι_iso_PresheafedSpace_inv, apply_instance }

lemma ι_jointly_surjective (x : 𝖣 .glued) :
  ∃ (i : D.J) (y : D.U i), (𝖣 .ι i).base y = x :=
𝖣 .ι_jointly_surjective (SheafedSpace.forget _ ⋙ category_theory.forget Top) x

/-- The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.

Vᵢⱼ ⟶ Uᵢ
 |      |
 ↓      ↓
 Uⱼ ⟶ X
-/
def V_pullback_cone_is_limit (i j : D.J) : is_limit (𝖣 .V_pullback_cone i j) :=
𝖣 .V_pullback_cone_is_limit_of_map forget_to_PresheafedSpace i j
  (D.to_PresheafedSpace_glue_data.V_pullback_cone_is_limit _ _)

end glue_data

end SheafedSpace

namespace LocallyRingedSpace

/--
A family of gluing data consists of
1. An index type `J`
2. A locally ringed space `U i` for each `i : J`.
3. A locally ringed space `V i j` for each `i j : J`.
  (Note that this is `J × J → LocallyRingedSpace` rather than `J → J → LocallyRingedSpace` to
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
@[nolint has_nonempty_instance]
structure glue_data extends glue_data LocallyRingedSpace :=
(f_open : ∀ i j, LocallyRingedSpace.is_open_immersion (f i j))

attribute [instance] glue_data.f_open

namespace glue_data

variables (D : glue_data)

local notation `𝖣` := D.to_glue_data

/-- The glue data of ringed spaces associated to a family of glue data of locally ringed spaces. -/
abbreviation to_SheafedSpace_glue_data : SheafedSpace.glue_data CommRing :=
{ f_open := D.f_open,
  to_glue_data := 𝖣 .map_glue_data forget_to_SheafedSpace }

/-- The gluing as locally ringed spaces is isomorphic to the gluing as ringed spaces. -/
abbreviation iso_SheafedSpace : 𝖣 .glued.to_SheafedSpace ≅
  D.to_SheafedSpace_glue_data.to_glue_data.glued :=
𝖣 .glued_iso forget_to_SheafedSpace

lemma ι_iso_SheafedSpace_inv (i : D.J) :
  D.to_SheafedSpace_glue_data.to_glue_data.ι i ≫ D.iso_SheafedSpace.inv = (𝖣 .ι i).1 :=
𝖣 .ι_glued_iso_inv forget_to_SheafedSpace i

instance ι_is_open_immersion (i : D.J) :
  is_open_immersion (𝖣 .ι i) :=
by { delta is_open_immersion, rw ← D.ι_iso_SheafedSpace_inv,
  apply PresheafedSpace.is_open_immersion.comp }

instance (i j k : D.J) :
  preserves_limit (cospan (𝖣 .f i j) (𝖣 .f i k)) forget_to_SheafedSpace :=
infer_instance

lemma ι_jointly_surjective (x : 𝖣 .glued) :
  ∃ (i : D.J) (y : D.U i), (𝖣 .ι i).1.base y = x :=
𝖣 .ι_jointly_surjective ((LocallyRingedSpace.forget_to_SheafedSpace ⋙
  SheafedSpace.forget _) ⋙ forget Top) x

/-- The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.

Vᵢⱼ ⟶ Uᵢ
 |      |
 ↓      ↓
 Uⱼ ⟶ X
-/
def V_pullback_cone_is_limit (i j : D.J) : is_limit (𝖣 .V_pullback_cone i j) :=
𝖣 .V_pullback_cone_is_limit_of_map forget_to_SheafedSpace i j
  (D.to_SheafedSpace_glue_data.V_pullback_cone_is_limit _ _)

end glue_data

end LocallyRingedSpace

end algebraic_geometry
