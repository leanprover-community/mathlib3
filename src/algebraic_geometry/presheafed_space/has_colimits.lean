/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebraic_geometry.presheafed_space
import topology.category.Top.limits
import topology.sheaves.limits
import category_theory.limits.concrete_category

/-!
# `PresheafedSpace C` has colimits.

If `C` has limits, then the category `PresheafedSpace C` has colimits,
and the forgetful functor to `Top` preserves these colimits.

When restricted to a diagram where the underlying continuous maps are open embeddings,
this says that we can glue presheaved spaces.

Given a diagram `F : J ⥤ PresheafedSpace C`,
we first build the colimit of the underlying topological spaces,
as `colimit (F ⋙ PresheafedSpace.forget C)`. Call that colimit space `X`.

Our strategy is to push each of the presheaves `F.obj j`
forward along the continuous map `colimit.ι (F ⋙ PresheafedSpace.forget C) j` to `X`.
Since pushforward is functorial, we obtain a diagram `J ⥤ (presheaf C X)ᵒᵖ`
of presheaves on a single space `X`.
(Note that the arrows now point the other direction,
because this is the way `PresheafedSpace C` is set up.)

The limit of this diagram then constitutes the colimit presheaf.
-/

noncomputable theory

universes v u

open category_theory
open Top
open Top.presheaf
open topological_space
open opposite
open category_theory.category
open category_theory.limits
open category_theory.functor

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v} C]


namespace algebraic_geometry

namespace PresheafedSpace

@[simp]
lemma map_id_c_app (F : J ⥤ PresheafedSpace C) (j) (U) :
  (F.map (𝟙 j)).c.app (op U) =
    (pushforward.id (F.obj j).presheaf).inv.app (op U) ≫
      (pushforward_eq (by { simp, refl }) (F.obj j).presheaf).hom.app (op U) :=
begin
  cases U,
  dsimp,
  simp [PresheafedSpace.congr_app (F.map_id j)],
  refl,
end

@[simp]
lemma map_comp_c_app (F : J ⥤ PresheafedSpace C) {j₁ j₂ j₃} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃) (U) :
  (F.map (f ≫ g)).c.app (op U) =
    (F.map g).c.app (op U) ≫
    (pushforward_map (F.map g).base (F.map f).c).app (op U) ≫
    (pushforward.comp (F.obj j₁).presheaf (F.map f).base (F.map g).base).inv.app (op U) ≫
    (pushforward_eq (by { rw F.map_comp, refl }) _).hom.app _ :=
begin
  cases U,
  dsimp,
  simp only [PresheafedSpace.congr_app (F.map_comp f g)],
  dsimp, simp, dsimp, simp, -- See note [dsimp, simp]
end

/--
Given a diagram of presheafed spaces,
we can push all the presheaves forward to the colimit `X` of the underlying topological spaces,
obtaining a diagram in `(presheaf C X)ᵒᵖ`.
-/
@[simps]
def pushforward_diagram_to_colimit (F : J ⥤ PresheafedSpace C) :
  J ⥤ (presheaf C (colimit (F ⋙ PresheafedSpace.forget C)))ᵒᵖ :=
{ obj := λ j, op ((colimit.ι (F ⋙ PresheafedSpace.forget C) j) _* (F.obj j).presheaf),
  map := λ j j' f,
  (pushforward_map (colimit.ι (F ⋙ PresheafedSpace.forget C) j') (F.map f).c ≫
    (pushforward.comp (F.obj j).presheaf ((F ⋙ PresheafedSpace.forget C).map f)
      (colimit.ι (F ⋙ PresheafedSpace.forget C) j')).inv ≫
    (pushforward_eq (colimit.w (F ⋙ PresheafedSpace.forget C) f) (F.obj j).presheaf).hom).op,
  map_id' := λ j,
  begin
    apply (op_equiv _ _).injective,
    ext U,
    op_induction U,
    cases U,
    dsimp, simp, dsimp, simp,
  end,
  map_comp' := λ j₁ j₂ j₃ f g,
  begin
    apply (op_equiv _ _).injective,
    ext U,
    dsimp,
    simp only [map_comp_c_app, id.def, eq_to_hom_op, pushforward_map_app, eq_to_hom_map, assoc,
      id_comp, pushforward.comp_inv_app, pushforward_eq_hom_app],
    dsimp,
    simp only [eq_to_hom_trans, id_comp],
    congr' 1,
    -- The key fact is `(F.map f).c.congr`,
    -- which allows us in rewrite in the argument of `(F.map f).c.app`.
    rw (F.map f).c.congr,
    -- Now we pick up the pieces. First, we say what we want to replace that open set by:
    swap 3,
    refine op ((opens.map (colimit.ι (F ⋙ PresheafedSpace.forget C) j₂)).obj (unop U)),
    -- Now we show the open sets are equal.
    swap 2,
    { apply unop_injective,
      rw ←opens.map_comp_obj,
      congr,
      exact colimit.w (F ⋙ PresheafedSpace.forget C) g, },
    -- Finally, the original goal is now easy:
    swap 2,
    { simp, refl, },
  end, }

variables [has_limits C]

/--
Auxiliary definition for `PresheafedSpace.has_colimits`.
-/
@[simps]
def colimit (F : J ⥤ PresheafedSpace C) : PresheafedSpace C :=
{ carrier := colimit (F ⋙ PresheafedSpace.forget C),
  presheaf := limit (pushforward_diagram_to_colimit F).left_op, }

/--
Auxiliary definition for `PresheafedSpace.has_colimits`.
-/
@[simps]
def colimit_cocone (F : J ⥤ PresheafedSpace C) : cocone F :=
{ X := colimit F,
  ι :=
  { app := λ j,
    { base := colimit.ι (F ⋙ PresheafedSpace.forget C) j,
      c := limit.π _ (op j), },
    naturality' := λ j j' f,
    begin
      fapply PresheafedSpace.ext,
      { ext x,
        exact colimit.w_apply (F ⋙ PresheafedSpace.forget C) f x, },
      { ext U,
        op_induction U,
        cases U,
        dsimp,
        simp only [PresheafedSpace.id_c_app, eq_to_hom_op, eq_to_hom_map, assoc,
          pushforward.comp_inv_app],
        rw ← congr_arg nat_trans.app (limit.w (pushforward_diagram_to_colimit F).left_op f.op),
        dsimp,
        simp only [eq_to_hom_op, eq_to_hom_map, assoc, id_comp, pushforward.comp_inv_app],
        congr,
        dsimp,
        simp only [id_comp],
        rw ←is_iso.inv_comp_eq,
        simp, refl, }
    end, }, }

namespace colimit_cocone_is_colimit

/--
Auxiliary definition for `PresheafedSpace.colimit_cocone_is_colimit`.
-/
def desc_c_app (F : J ⥤ PresheafedSpace C) (s : cocone F) (U : (opens ↥(s.X.carrier))ᵒᵖ) :
  s.X.presheaf.obj U ⟶
    (colimit.desc (F ⋙ PresheafedSpace.forget C)
         ((PresheafedSpace.forget C).map_cocone s) _*
       limit (pushforward_diagram_to_colimit F).left_op).obj
      U :=
begin
  refine
    limit.lift _ { X := s.X.presheaf.obj U, π := { app := λ j, _, naturality' := λ j j' f, _, }} ≫
      (limit_obj_iso_limit_comp_evaluation _ _).inv,
  -- We still need to construct the `app` and `naturality'` fields omitted above.
  { refine (s.ι.app (unop j)).c.app U ≫ (F.obj (unop j)).presheaf.map (eq_to_hom _),
    dsimp,
    rw ←opens.map_comp_obj,
    simp, },
  { rw (PresheafedSpace.congr_app (s.w f.unop).symm U),
    dsimp,
    have w := functor.congr_obj (congr_arg opens.map
      (colimit.ι_desc ((PresheafedSpace.forget C).map_cocone s) (unop j))) (unop U),
    simp only [opens.map_comp_obj_unop] at w,
    replace w := congr_arg op w,
    have w' := nat_trans.congr (F.map f.unop).c w,
    rw w',
    dsimp, simp, dsimp, simp, refl, },
end

lemma desc_c_naturality (F : J ⥤ PresheafedSpace C) (s : cocone F)
  {U V : (opens ↥(s.X.carrier))ᵒᵖ} (i : U ⟶ V) :
  s.X.presheaf.map i ≫ desc_c_app F s V =
  desc_c_app F s U ≫ (colimit.desc (F ⋙ forget C)
    ((forget C).map_cocone s) _* (colimit_cocone F).X.presheaf).map i :=
begin
  dsimp [desc_c_app],
  ext,
  simp only [limit.lift_π, nat_trans.naturality, limit.lift_π_assoc, eq_to_hom_map, assoc,
    pushforward_obj_map, nat_trans.naturality_assoc, op_map,
    limit_obj_iso_limit_comp_evaluation_inv_π_app_assoc,
    limit_obj_iso_limit_comp_evaluation_inv_π_app],
  dsimp,
  have w := functor.congr_hom (congr_arg opens.map
    (colimit.ι_desc ((PresheafedSpace.forget C).map_cocone s) (unop j))) (i.unop),
  simp only [opens.map_comp_map] at w,
  replace w := congr_arg quiver.hom.op w,
  rw w,
  dsimp, simp,
end

end colimit_cocone_is_colimit

open colimit_cocone_is_colimit

/--
Auxiliary definition for `PresheafedSpace.has_colimits`.
-/
def colimit_cocone_is_colimit (F : J ⥤ PresheafedSpace C) : is_colimit (colimit_cocone F) :=
{ desc := λ s,
  { base := colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).map_cocone s),
    c :=
    { app := λ U, desc_c_app F s U,
      naturality' := λ U V i, desc_c_naturality F s i }, },
  fac' := -- tidy can do this but it takes too long
  begin
    intros s j,
    dsimp,
    fapply PresheafedSpace.ext,
    { simp, },
    { ext,
      dsimp [desc_c_app],
      simp only [eq_to_hom_op, limit.lift_π_assoc, eq_to_hom_map, assoc, pushforward.comp_inv_app,
                 limit_obj_iso_limit_comp_evaluation_inv_π_app_assoc],
      dsimp,
      simp },
  end,
  uniq' := λ s m w,
  begin
    -- We need to use the identity on the continuous maps twice, so we prepare that first:
    have t : m.base = colimit.desc (F ⋙ PresheafedSpace.forget C)
                        ((PresheafedSpace.forget C).map_cocone s),
    { ext,
      dsimp,
      simp only [colimit.ι_desc_apply, map_cocone_ι_app],
      rw ← w j,
      simp, },
    fapply PresheafedSpace.ext, -- could `ext` please not reorder goals?
    { exact t, },
    { ext U j, dsimp [desc_c_app],
      simp only [limit.lift_π, eq_to_hom_op, eq_to_hom_map, assoc,
        limit_obj_iso_limit_comp_evaluation_inv_π_app],
      rw PresheafedSpace.congr_app (w (unop j)).symm U,
      dsimp,
      have w := congr_arg op (functor.congr_obj (congr_arg opens.map t) (unop U)),
      rw nat_trans.congr (limit.π (pushforward_diagram_to_colimit F).left_op j) w,
      simp, dsimp, simp, }
  end, }

/--
When `C` has limits, the category of presheaved spaces with values in `C` itself has colimits.
-/
instance : has_colimits (PresheafedSpace C) :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F, has_colimit.mk
    { cocone     := colimit_cocone F,
      is_colimit := colimit_cocone_is_colimit F } } }

/--
The underlying topological space of a colimit of presheaved spaces is
the colimit of the underlying topological spaces.
-/
instance forget_preserves_colimits : preserves_colimits (PresheafedSpace.forget C) :=
{ preserves_colimits_of_shape := λ J 𝒥, by exactI
  { preserves_colimit := λ F, preserves_colimit_of_preserves_colimit_cocone
    (colimit_cocone_is_colimit F)
    begin
      apply is_colimit.of_iso_colimit (colimit.is_colimit _),
      fapply cocones.ext,
      { refl, },
      { intro j, dsimp, simp, }
    end } }

end PresheafedSpace

end algebraic_geometry
