/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.preserves

open category_theory category_theory.category

namespace category_theory.limits

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u} [category.{v} C]

variables {J K : Type v} [small_category J] [small_category K]

@[simp] lemma cone.functor_w {F : J ⥤ (K ⥤ C)} (c : cone F) {j j' : J} (f : j ⟶ j') (k : K) :
  (c.π.app j).app k ≫ (F.map f).app k = (c.π.app j').app k :=
by convert ←nat_trans.congr_app (c.π.naturality f).symm k; apply id_comp

@[simp] lemma cocone.functor_w {F : J ⥤ (K ⥤ C)} (c : cocone F) {j j' : J} (f : j ⟶ j') (k : K) :
  (F.map f).app k ≫ (c.ι.app j').app k = (c.ι.app j).app k :=
by convert ←nat_trans.congr_app (c.ι.naturality f) k; apply comp_id

@[simps] def functor_category_limit_cone [has_limits_of_shape J C] (F : J ⥤ K ⥤ C) :
  cone F :=
{ X := F.flip ⋙ lim,
  π :=
  { app := λ j,
    { app := λ k, limit.π (F.flip.obj k) j },
      naturality' := λ j j' f,
        by ext k; convert (limit.w (F.flip.obj k) _).symm using 1; apply id_comp } }

@[simps] def functor_category_colimit_cocone [has_colimits_of_shape J C] (F : J ⥤ K ⥤ C) :
  cocone F :=
{ X := F.flip ⋙ colim,
  ι :=
  { app := λ j,
    { app := λ k, colimit.ι (F.flip.obj k) j },
      naturality' := λ j j' f,
        by ext k; convert (colimit.w (F.flip.obj k) _) using 1; apply comp_id } }

@[simp] def evaluate_functor_category_limit_cone
  [has_limits_of_shape J C] (F : J ⥤ K ⥤ C) (k : K) :
  ((evaluation K C).obj k).map_cone (functor_category_limit_cone F) ≅
    limit.cone (F.flip.obj k) :=
cones.ext (iso.refl _) (by tidy)

@[simp] def evaluate_functor_category_colimit_cocone
  [has_colimits_of_shape J C] (F : J ⥤ K ⥤ C) (k : K) :
  ((evaluation K C).obj k).map_cocone (functor_category_colimit_cocone F) ≅
    colimit.cocone (F.flip.obj k) :=
cocones.ext (iso.refl _) (by tidy)

def functor_category_is_limit_cone [has_limits_of_shape J C] (F : J ⥤ K ⥤ C) :
  is_limit (functor_category_limit_cone F) :=
{ lift := λ s,
  { app := λ k, limit.lift (F.flip.obj k) (((evaluation K C).obj k).map_cone s) },
  uniq' := λ s m w,
  begin
    ext1, ext1 k,
    exact is_limit.uniq _
      (((evaluation K C).obj k).map_cone s) (m.app k) (λ j, nat_trans.congr_app (w j) k)
  end }

def functor_category_is_colimit_cocone [has_colimits_of_shape J C] (F : J ⥤ K ⥤ C) :
  is_colimit (functor_category_colimit_cocone F) :=
{ desc := λ s,
  { app := λ k, colimit.desc (F.flip.obj k) (((evaluation K C).obj k).map_cocone s) },
  uniq' := λ s m w,
  begin
    ext1, ext1 k,
    exact is_colimit.uniq _
      (((evaluation K C).obj k).map_cocone s) (m.app k) (λ j, nat_trans.congr_app (w j) k)
  end }

instance functor_category_has_limits_of_shape
  [has_limits_of_shape J C] : has_limits_of_shape J (K ⥤ C) :=
{ has_limit := λ F,
  { cone := functor_category_limit_cone F,
    is_limit := functor_category_is_limit_cone F } }

instance functor_category_has_colimits_of_shape
  [has_colimits_of_shape J C] : has_colimits_of_shape J (K ⥤ C) :=
{ has_colimit := λ F,
  { cocone := functor_category_colimit_cocone F,
    is_colimit := functor_category_is_colimit_cocone F } }

instance functor_category_has_limits [has_limits C] : has_limits (K ⥤ C) :=
{ has_limits_of_shape := λ J 𝒥, by resetI; apply_instance }

instance functor_category_has_colimits [has_colimits C] : has_colimits (K ⥤ C) :=
{ has_colimits_of_shape := λ J 𝒥, by resetI; apply_instance }

instance evaluation_preserves_limits_of_shape [has_limits_of_shape J C] (k : K) :
  preserves_limits_of_shape J ((evaluation K C).obj k) :=
{ preserves_limit :=
  λ F, preserves_limit_of_preserves_limit_cone (limit.is_limit _) $
    is_limit.of_iso_limit (limit.is_limit _)
      (evaluate_functor_category_limit_cone F k).symm }

instance evaluation_preserves_colimits_of_shape [has_colimits_of_shape J C] (k : K) :
  preserves_colimits_of_shape J ((evaluation K C).obj k) :=
{ preserves_colimit :=
  λ F, preserves_colimit_of_preserves_colimit_cocone (colimit.is_colimit _) $
    is_colimit.of_iso_colimit (colimit.is_colimit _)
      (evaluate_functor_category_colimit_cocone F k).symm }

instance evaluation_preserves_limits [has_limits C] (k : K) :
  preserves_limits ((evaluation K C).obj k) :=
{ preserves_limits_of_shape := λ J 𝒥, by resetI; apply_instance }

instance evaluation_preserves_colimits [has_colimits C] (k : K) :
  preserves_colimits ((evaluation K C).obj k) :=
{ preserves_colimits_of_shape := λ J 𝒥, by resetI; apply_instance }

end category_theory.limits
