-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Johan Commelin, Reid Barton

import category_theory.comma
import category_theory.limits.preserves

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

def colimit (F : J ⥤ over X) [has_colimit (F ⋙ forget)] : cocone F :=
{ X := mk $ colimit.desc (F ⋙ forget) F.to_cocone,
  ι :=
  { app := λ j, hom_mk $ colimit.ι (F ⋙ forget) j,
    naturality' :=
    begin
      intros j j' f,
      have := colimit.w (F ⋙ forget) f,
      tidy
    end } }

@[simp] lemma colimit_X_hom (F : J ⥤ over X) [has_colimit (F ⋙ forget)] :
((colimit F).X).hom = colimit.desc (F ⋙ forget) F.to_cocone := rfl
@[simp] lemma colimit_ι_app (F : J ⥤ over X) [has_colimit (F ⋙ forget)] (j : J) :
((colimit F).ι).app j = hom_mk (colimit.ι (F ⋙ forget) j) := rfl

def forget_colimit_is_colimit (F : J ⥤ over X) [has_colimit (F ⋙ forget)] :
  is_colimit (forget.map_cocone (colimit F)) :=
is_colimit.of_iso_colimit (colimit.is_colimit (F ⋙ forget)) (cocones.ext (iso.refl _) (by tidy))

instance : reflects_colimits (forget : over X ⥤ C) :=
λ J 𝒥 F, by constructor; exactI λ t ht,
{ desc := λ s, hom_mk (ht.desc (forget.map_cocone s))
    begin
      apply ht.hom_ext, intro j,
      rw [←category.assoc, ht.fac],
      transitivity (F.obj j).hom,
      exact w (s.ι.app j), -- TODO: How to write (s.ι.app j).w?
      exact (w (t.ι.app j)).symm,
    end,
  fac' := begin
    intros s j, ext, exact ht.fac (forget.map_cocone s) j
    -- TODO: Ask Simon about multiple ext lemmas for defeq types (comma_morphism & over.category.hom)
  end,
  uniq' :=
  begin
    intros s m w,
    ext1 j,
    exact ht.uniq (forget.map_cocone s) m.left (λ j, congr_arg comma_morphism.left (w j))
  end }

instance has_colimit {F : J ⥤ over X} [has_colimit (F ⋙ forget)] : has_colimit F :=
{ cocone := colimit F,
  is_colimit := reflects_colimit.reflects (forget_colimit_is_colimit F) }

instance has_colimits_of_shape [has_colimits_of_shape J C] :
  has_colimits_of_shape J (over X) :=
λ F, infer_instance

instance has_colimits [has_colimits C] : has_colimits (over X) :=
λ J 𝒥, by resetI; apply_instance

instance forget_preserves_colimits [has_colimits C] {X : C} :
  preserves_colimits (forget : over X ⥤ C) :=
λ J 𝒥 F, by exactI
preserves_colimit_of_preserves_colimit_cocone (colimit.is_colimit F) (forget_colimit_is_colimit F)

end category_theory.over

namespace category_theory.under

def limit (F : J ⥤ under X) [has_limit (F ⋙ forget)] : cone F :=
{ X := mk $ limit.lift (F ⋙ forget) F.to_cone,
  π :=
  { app := λ j, hom_mk $ limit.π (F ⋙ forget) j,
    naturality' :=
    begin
      intros j j' f,
      have := (limit.w (F ⋙ forget) f).symm,
      tidy
    end } }

@[simp] lemma limit_X_hom (F : J ⥤ under X) [has_limit (F ⋙ forget)] :
((limit F).X).hom = limit.lift (F ⋙ forget) F.to_cone := rfl
@[simp] lemma limit_π_app (F : J ⥤ under X) [has_limit (F ⋙ forget)] (j : J) :
((limit F).π).app j = hom_mk (limit.π (F ⋙ forget) j) := rfl

def forget_limit_is_limit (F : J ⥤ under X) [has_limit (F ⋙ forget)] :
  is_limit (forget.map_cone (limit F)) :=
is_limit.of_iso_limit (limit.is_limit (F ⋙ forget)) (cones.ext (iso.refl _) (by tidy))

instance : reflects_limits (forget : under X ⥤ C) :=
λ J 𝒥 F, by constructor; exactI λ t ht,
{ lift := λ s, hom_mk (ht.lift (forget.map_cone s))
    begin
      apply ht.hom_ext, intro j,
      rw [category.assoc, ht.fac],
      transitivity (F.obj j).hom,
      exact w (s.π.app j),
      exact (w (t.π.app j)).symm,
    end,
  fac' := begin
    intros s j, ext, exact ht.fac (forget.map_cone s) j
  end,
  uniq' :=
  begin
    intros s m w,
    ext1 j,
    exact ht.uniq (forget.map_cone s) m.right (λ j, congr_arg comma_morphism.right (w j))
  end }

instance has_limit {F : J ⥤ under X} [has_limit (F ⋙ forget)] : has_limit F :=
{ cone := limit F,
  is_limit := reflects_limit.reflects (forget_limit_is_limit F) }

instance has_limits_of_shape [has_limits_of_shape J C] :
  has_limits_of_shape J (under X) :=
λ F, infer_instance

instance has_limits [has_limits C] : has_limits (under X) :=
λ J 𝒥, by resetI; apply_instance

instance forget_preserves_limits [has_limits C] {X : C} :
  preserves_limits (forget : under X ⥤ C) :=
λ J 𝒥 F, by exactI
preserves_limit_of_preserves_limit_cone (limit.is_limit F) (forget_limit_is_limit F)

end category_theory.under
