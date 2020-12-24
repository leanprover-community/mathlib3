/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.limits.preserves.basic

/-!
# Isomorphisms about functors which preserve (co)limits

If `G` preserves limits, and `C` and `D` have limits, then for any diagram `F : J ⥤ C` we have a
canonical isomorphism `preserves_limit_iso : G.obj (limit F) ≅ limit (F ⋙ G)`.
We also show that we can commute `is_limit.lift` of a preserved limit with `functor.map_cone`:
`(preserves_limit.preserves t).lift (G.map_cone c₂) = G.map (t.lift c₂)`.

The duals of these are also given. For functors which preserve (co)limits of specific shapes, see
`preserves/shapes.lean`.
-/

universes v u₁ u₂

noncomputable theory

namespace category_theory

open category limits

variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]
variables (G : C ⥤ D)
variables {J : Type v} [small_category J]
variables (F : J ⥤ C)

section
variables [preserves_limit F G]

@[simp]
lemma preserves_lift_map_cone (c₁ c₂ : cone F) (t : is_limit c₁) :
  (preserves_limit.preserves t).lift (G.map_cone c₂) = G.map (t.lift c₂) :=
((preserves_limit.preserves t).uniq (G.map_cone c₂) _ (by simp [← G.map_comp])).symm

variables [has_limit F] [has_limit (F ⋙ G)]
/--
If `G` preserves limits, we have an isomorphism from the image of the limit of a functor `F`
to the limit of the functor `F ⋙ G`.
-/
def preserves_limit_iso : G.obj (limit F) ≅ limit (F ⋙ G) :=
(preserves_limit.preserves (limit.is_limit _)).cone_point_unique_up_to_iso (limit.is_limit _)

@[simp, reassoc]
lemma preserves_limits_iso_hom_π (j) :
  (preserves_limit_iso G F).hom ≫ limit.π _ j = G.map (limit.π F j) :=
is_limit.cone_point_unique_up_to_iso_hom_comp _ _ j

@[simp, reassoc]
lemma preserves_limits_iso_inv_π (j) :
  (preserves_limit_iso G F).inv ≫ G.map (limit.π F j) = limit.π _ j :=
is_limit.cone_point_unique_up_to_iso_inv_comp _ _ j

@[simp, reassoc]
lemma lift_comp_preserves_limits_iso_hom (t : cone F) :
  G.map (limit.lift _ t) ≫ (preserves_limit_iso G F).hom = limit.lift (F ⋙ G) (G.map_cone _) :=
by { ext, simp [← G.map_comp] }
end

section
variables [preserves_colimit F G]

@[simp]
lemma preserves_desc_map_cocone (c₁ c₂ : cocone F) (t : is_colimit c₁) :
  (preserves_colimit.preserves t).desc (G.map_cocone _) = G.map (t.desc c₂) :=
((preserves_colimit.preserves t).uniq (G.map_cocone _) _ (by simp [← G.map_comp])).symm

variables [has_colimit F] [has_colimit (F ⋙ G)]
/--
If `G` preserves colimits, we have an isomorphism from the image of the colimit of a functor `F`
to the colimit of the functor `F ⋙ G`.
-/
-- TODO: think about swapping the order here
def preserves_colimit_iso : G.obj (colimit F) ≅ colimit (F ⋙ G) :=
(preserves_colimit.preserves (colimit.is_colimit _)).cocone_point_unique_up_to_iso
  (colimit.is_colimit _)

@[simp, reassoc]
lemma ι_preserves_colimits_iso_inv (j : J) :
  colimit.ι _ j ≫ (preserves_colimit_iso G F).inv = G.map (colimit.ι F j) :=
is_colimit.comp_cocone_point_unique_up_to_iso_inv _ (colimit.is_colimit (F ⋙ G)) j

@[simp, reassoc]
lemma ι_preserves_colimits_iso_hom (j : J) :
  G.map (colimit.ι F j) ≫ (preserves_colimit_iso G F).hom = colimit.ι (F ⋙ G) j :=
(preserves_colimit.preserves (colimit.is_colimit _)).comp_cocone_point_unique_up_to_iso_hom _ j

@[simp, reassoc]
lemma preserves_colimits_iso_inv_comp_desc (t : cocone F) :
  (preserves_colimit_iso G F).inv ≫ G.map (colimit.desc _ t) = colimit.desc _ (G.map_cocone t) :=
by { ext, simp [← G.map_comp] }
end

end category_theory
