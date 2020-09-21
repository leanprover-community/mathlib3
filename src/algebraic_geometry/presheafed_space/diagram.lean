/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebraic_geometry.presheafed_space
import topology.category.Top.limits
import category_theory.limits.functor_category

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
variables {C : Type u} [category.{v} C] [has_limits C]


namespace algebraic_geometry

-- TODO move
instance (X : Top) : has_limits (presheaf C X) := by { dsimp [presheaf], apply_instance, }

@[simp]
lemma bar {X Y : PresheafedSpace C} {f g : X ⟶ Y} (e : f = g) (U) :
  f.c.app (op U) = g.c.app (op U) ≫ (pushforward_eq (congr_arg PresheafedSpace.hom.base e.symm) X.presheaf).hom.app (op U) :=
begin
  subst e,
  simp only [pushforward_eq_rfl, comp_id],
end

@[simp]
lemma foo (F : J ⥤ PresheafedSpace C) (j) (U) : (F.map (𝟙 j)).c.app (op U) =
  (pushforward.id (F.obj j).presheaf).inv.app (op U) ≫ (pushforward_eq (by { simp, refl }) (F.obj j).presheaf).hom.app (op U) :=
begin
  cases U,
  dsimp,
  simp [bar (F.map_id j)],
  refl,
end

@[simp]
lemma foo' (F : J ⥤ PresheafedSpace C) {j₁ j₂ j₃} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃) (U) : (F.map (f ≫ g)).c.app (op U) =
  (F.map g).c.app (op U) ≫ begin refine (pushforward_map (F.map g).base _).app _, refine (F.map f).c, end ≫ (pushforward.comp (F.obj j₁).presheaf (F.map f).base (F.map g).base).inv.app (op U) ≫
    begin refine (pushforward_eq _ _).hom.app _, erw F.map_comp, refl, end :=
begin
  cases U,
  dsimp,
  simp [bar (F.map_comp f g)],
  dsimp,
  erw id_comp,
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
  map_id' :=
  begin
    intro j,
    apply (op_equiv _ _).injective,
    ext U,
    op_induction U,
    cases U,
    dsimp,
    simp,
    dsimp,
    erw id_comp,
    simp,
  end,
  map_comp' :=
  begin
    intros j₁ j₂ j₃ f g,
    apply (op_equiv _ _).injective,
    ext U,
    op_induction U,
    cases U,
    dsimp,
    simp,
    dsimp,
    erw id_comp,
    erw id_comp,
    erw id_comp,
    simp,
    congr' 1,
    rw (F.map f).c.congr,
    swap 3,
    refine op ⟨⇑(colimit.ι (F ⋙ PresheafedSpace.forget C) j₂) ⁻¹' U_val, _⟩,
    swap 3,
    apply unop_injective,
    simp [set.preimage_preimage],
    congr,
    funext,
    exact Top.colimit.w_apply (F ⋙ PresheafedSpace.forget C) g _,
    swap 2,
    simp,
    refl,
  end, }

@[simps]
def colimit (F : J ⥤ PresheafedSpace C) : PresheafedSpace C :=
{ carrier := colimit (F ⋙ PresheafedSpace.forget C),
  presheaf := limit (pushforward_diagram_to_colimit F).left_op, }

lemma quux {X Y Z : C} (f : X ⟶ Z) (g : X = Y) (h : Y ⟶ Z) :
  f = eq_to_hom g ≫ h ↔ eq_to_hom g.symm ≫ f = h :=
begin
  fsplit,
  intro w,
  rw w, simp,
  intro w,
  rw ←w, simp,
end

@[simps]
def colimit_cocone (F : J ⥤ PresheafedSpace C) : cocone F :=
{ X := colimit F,
  ι :=
  { app := λ j,
    { base := colimit.ι (F ⋙ PresheafedSpace.forget C) j,
      c := limit.π _ (op j), },
    naturality' :=
    begin
      intros j j' f,
      dsimp,
      fapply PresheafedSpace.ext,
      { dsimp,
        simp,
        ext x,
        exact Top.colimit.w_apply _ f _, },
      { dsimp,
        ext U,
        op_induction U,
        dsimp,
        simp,
        -- erw [id_comp, id_comp],
        have := limit.w (pushforward_diagram_to_colimit F).left_op f.op,
        have := congr_arg nat_trans.app this,
        rw ←this,
        cases U,
        dsimp,
        simp,
        -- erw [id_comp],
        congr,
        dsimp,
        erw [id_comp],
        rw quux,
        simp,
        refl,
         }
    end, }, }

namespace colimit_cocone_is_colimit

def desc_c_app (F : J ⥤ PresheafedSpace C) (s : cocone F) (U : (opens ↥(s.X.carrier))ᵒᵖ) :
  s.X.presheaf.obj U ⟶
    (colimit.desc (F ⋙ PresheafedSpace.forget C)
         ((PresheafedSpace.forget C).map_cocone s) _*
       limit (pushforward_diagram_to_colimit F).left_op).obj
      U :=
begin
      -- dsimp [pushforward],
      refine limit.lift _ { X := s.X.presheaf.obj U, π := _} ≫ (limit_obj_iso_limit_comp_evaluation _ _).inv,
      -- dsimp,
      fsplit,
      { intro j,
      -- dsimp [pushforward],
      refine (s.ι.app (unop j)).c.app U ≫ (F.obj (unop j)).presheaf.map (eq_to_hom _),
      dsimp,
      congr' 1,
      rw ←opens.map_comp_obj,
      congr' 2,
      simp, },
      { intros j j' f, dsimp, simp,
        have := s.w f.unop,
        have := (PresheafedSpace.congr_app this.symm U).symm,
        rw ←this, dsimp, simp,
        congr' 1,
        dsimp,
        simp,
        have w := functor.congr_obj (congr_arg opens.map (colimit.ι_desc ((PresheafedSpace.forget C).map_cocone s) (unop j))) (unop U),
        simp only [opens.map_comp_obj_unop] at w,
        replace w := congr_arg op w,
        have w' := nat_trans.congr (F.map f.unop).c w,
        rw w',
        dsimp,
        simp,
        refl, },
    end

end colimit_cocone_is_colimit

open colimit_cocone_is_colimit

def colimit_cocone_is_colimit (F : J ⥤ PresheafedSpace C) : is_colimit (colimit_cocone F) :=
{ desc := λ s,
  { base := colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).map_cocone s),
    c :=
    { app := λ U, desc_c_app F s U,
      naturality' := λ U V i,
      begin
        dsimp [desc_c_app],
        ext,
        simp only [limit.lift_π, nat_trans.naturality, limit.lift_π_assoc, eq_to_hom_map, assoc,
          pushforward_obj_map, nat_trans.naturality_assoc, op_map,
          limit_obj_iso_limit_comp_evaluation_inv_π_app_assoc,
          limit_obj_iso_limit_comp_evaluation_inv_π_app],
        dsimp,
        have w := functor.congr_hom (congr_arg opens.map (colimit.ι_desc ((PresheafedSpace.forget C).map_cocone s) (unop j))) (i.unop),
        simp only [opens.map_comp_map] at w,
        replace w := congr_arg has_hom.hom.op w,
        rw w,
        dsimp,
        simp,
      end, }, },
  -- fac' := begin sorry, end, -- works by tidy
  uniq' := λ s m w,
  begin
    have t : m.base = colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).map_cocone s),
    { ext,
      dsimp,
      simp only [colimit.ι_desc_apply, map_cocone_ι],
      rw ← w j,
      simp, },
    fapply PresheafedSpace.ext, -- could `ext` please not reorder goals?
    { exact t, },
    { ext U j, dsimp [desc_c_app], simp,
      rw PresheafedSpace.congr_app (w (unop j)).symm U,
      simp,
      dsimp,
      simp,
      have w := functor.congr_obj (congr_arg opens.map t) (unop U),
      replace w := congr_arg op w,
      have w' := nat_trans.congr (limit.π (pushforward_diagram_to_colimit F).left_op j) w,
      rw w',
      simp, }
  end, }

instance : has_colimits (PresheafedSpace C) :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F, has_colimit.mk
    { cocone     := colimit_cocone F,
      is_colimit := colimit_cocone_is_colimit F } } }

instance forget_preserves_colimits : preserves_colimits (PresheafedSpace.forget C) :=
{ preserves_colimits_of_shape := λ J 𝒥, by exactI
  { preserves_colimit := λ F, preserves_colimit_of_preserves_colimit_cocone
    (colimit_cocone_is_colimit F)
    begin
      apply is_colimit.of_iso_colimit (colimit.is_colimit _),
      fapply cocones.ext,
      refl,
      intro j,
      dsimp [colimit_cocone],
      simp,
    end } }

end algebraic_geometry
