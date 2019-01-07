-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Johan Commelin

import category_theory.comma
import category_theory.limits.limits

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

open category_theory category_theory.limits

variables {J : Type v} [small_category J]
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞
variable {X : C}

namespace category_theory.functor

def to_cocone (F : J ⥤ over X) : cocone (F ⋙ over.forget) :=
{ X := X,
  ι := { app := λ j, (F.obj j).hom } }

@[simp] lemma to_cocone_X (F : J ⥤ over X) : F.to_cocone.X = X := rfl
@[simp] lemma to_cocone_ι (F : J ⥤ over X) (j : J) : F.to_cocone.ι.app j = (F.obj j).hom := rfl

def to_cone (F : J ⥤ under X) : cone (F ⋙ under.forget) :=
{ X := X,
  π := { app := λ j, (F.obj j).hom } }

@[simp] lemma to_cone_X (F : J ⥤ under X) : F.to_cone.X = X := rfl
@[simp] lemma to_cone_π (F : J ⥤ under X) (j : J) : F.to_cone.π.app j = (F.obj j).hom := rfl

end category_theory.functor

namespace category_theory.over

def colimit [has_colimits_of_shape J C] (F : J ⥤ over X) : cocone F :=
{ X := mk $ colimit.desc (F ⋙ forget) F.to_cocone,
  ι :=
  { app := λ j, hom_mk $ colimit.ι (F ⋙ forget) j,
    naturality' :=
    begin
      intros j j' f,
      have := colimit.w (F ⋙ forget) f,
      tidy
    end } }

@[simp] lemma colimit_X_hom [has_colimits_of_shape J C] (F : J ⥤ over X) :
((colimit F).X).hom = colimit.desc (F ⋙ forget) F.to_cocone := rfl
@[simp] lemma colimit_ι_app [has_colimits_of_shape J C] (F : J ⥤ over X) (j : J) :
((colimit F).ι).app j = hom_mk (colimit.ι (F ⋙ forget) j) := rfl

def is_colimit [has_colimits_of_shape J C] (F : J ⥤ over X) : is_colimit (colimit F) :=
{ desc := λ s,
  { left := colimit.desc (F ⋙ forget) ((cocones.functoriality forget).obj s),
    w' :=
    begin
      ext1,
      have := (colimit.is_colimit (F ⋙ forget)).fac ((cocones.functoriality forget).obj s) j,
      dsimp at ⊢ this,
      simp [(category.assoc _ _ _ _).symm, this]
    end },
  uniq' :=
  begin
    intros s m w,
    ext1,
    { ext1,
      dsimp, simp only [category_theory.limits.colimit.ι_desc],
      rw ← (w j),
      simp },
    { exact dec_trivial }
  end }

end category_theory.over

namespace category_theory.under

def limit [has_limits_of_shape J C] (F : J ⥤ under X) : cone F :=
{ X := mk $ limit.lift (F ⋙ forget) F.to_cone,
  π :=
  { app := λ j, hom_mk $ limit.π (F ⋙ forget) j,
    naturality' :=
    begin
      intros j j' f,
      have := (limit.w (F ⋙ forget) f).symm,
      tidy
    end } }

@[simp] lemma limit_X_hom [has_limits_of_shape J C] (F : J ⥤ under X) :
((limit F).X).hom = limit.lift (F ⋙ forget) F.to_cone := rfl
@[simp] lemma limit_π_app [has_limits_of_shape J C] (F : J ⥤ under X) (j : J) :
((limit F).π).app j = hom_mk (limit.π (F ⋙ forget) j) := rfl

def is_limit [has_limits_of_shape J C] (F : J ⥤ under X) : is_limit (limit F) :=
{ lift := λ s,
  { right := limit.lift (F ⋙ forget) ((cones.functoriality forget).obj s),
    w' :=
    begin
      ext1,
      have := (limit.is_limit (F ⋙ forget)).fac ((cones.functoriality forget).obj s) j,
      dsimp at ⊢ this,
      simp [(category.assoc _ _ _ _).symm, this]
    end },
  uniq' :=
  begin
    intros s m w,
    ext1,
    { exact dec_trivial },
    { ext1,
      dsimp, simp only [category_theory.limits.limit.lift_π],
      rw ← (w j),
      simp }
  end }

end category_theory.under
