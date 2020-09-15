/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.preserves.basic
import category_theory.limits.shapes

universes v u₁ u₂

noncomputable theory

open category_theory category_theory.category category_theory.limits

variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]
variables (G : C ⥤ D)

section
variables {J : Type v} [small_category J]
variables (F : J ⥤ C) [has_limit F] [has_limit (F ⋙ G)] [preserves_limit F G]
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

@[simp]
lemma preserves_lift_map_cone (c₁ c₂ : cone F) (t : is_limit c₁) :
  (preserves_limit.preserves t).lift (G.map_cone _) = G.map (t.lift c₂) :=
((preserves_limit.preserves t).uniq (G.map_cone _) _ (by simp [← G.map_comp])).symm

@[simp, reassoc]
lemma lift_comp_preserves_limits_iso_hom (t : cone F) :
  G.map (limit.lift _ t) ≫ (preserves_limit_iso G F).hom = limit.lift (F ⋙ G) (G.map_cone _) :=
by { ext, simp [← G.map_comp] }
end

section
variables {J : Type v} [small_category J]
variables (F : J ⥤ C) [has_colimit F] [has_colimit (F ⋙ G)] [preserves_colimit F G]
/--
If `G` preserves colimits, we have an isomorphism from the image of the colimit of a functor `F`
to the colimit of the functor `F ⋙ G`.
-/
-- TODO: think about swapping the order here
def preserves_colimit_iso : G.obj (colimit F) ≅ colimit (F ⋙ G) :=
(preserves_colimit.preserves (colimit.is_colimit _)).cocone_point_unique_up_to_iso (colimit.is_colimit _)

@[simp, reassoc]
lemma ι_preserves_colimits_iso_inv (j : J) :
  colimit.ι _ j ≫ (preserves_colimit_iso G F).inv = G.map (colimit.ι F j) :=
is_colimit.comp_cocone_point_unique_up_to_iso_inv _ (colimit.is_colimit (F ⋙ G)) j

@[simp, reassoc]
lemma ι_preserves_colimits_iso_hom (j : J) :
  G.map (colimit.ι F j) ≫ (preserves_colimit_iso G F).hom = colimit.ι (F ⋙ G) j :=
(preserves_colimit.preserves (colimit.is_colimit _)).comp_cocone_point_unique_up_to_iso_hom _ j

@[simp]
lemma preserves_desc_map_cocone (c₁ c₂ : cocone F) (t : is_colimit c₁) :
  (preserves_colimit.preserves t).desc (G.map_cocone _) = G.map (t.desc c₂) :=
((preserves_colimit.preserves t).uniq (G.map_cocone _) _ (by simp [← G.map_comp])).symm

@[simp, reassoc]
lemma preserves_colimits_iso_inv_comp_desc (t : cocone F) :
(preserves_colimit_iso G F).inv ≫ G.map (colimit.desc _ t) = colimit.desc (F ⋙ G) (G.map_cocone t) :=
by { ext, simp [← G.map_comp] }
end

section preserve_products

variables {J : Type v} (f : J → C)

/--
(Implementation). The map of a fan is a limit iff the fan consisting of the mapped morphisms
is a limit.
This essentially lets us commute `fan.mk` with `functor.map_cone`.
-/
def fan_map_cone_limit {P : C} (g : Π j, P ⟶ f j) :
  is_limit (G.map_cone (fan.mk g)) ≃ is_limit (fan.mk (λ j, G.map (g j)) : fan (λ j, G.obj (f j))) :=
begin
  refine (is_limit.postcompose_hom_equiv _ _).symm.trans (is_limit.equiv_iso_limit _),
  refine discrete.nat_iso (λ j, iso.refl (G.obj (f j))),
  refine cones.ext (iso.refl _) (λ j, by { dsimp, simp }),
end

/-- The property of reflecting products expressed in terms of fans. -/
def reflects_is_product [reflects_limits_of_shape (discrete J) G] {P : C} (g : Π j, P ⟶ f j)
  (t : is_limit (fan.mk (λ j, G.map (g j)) : fan (λ j, G.obj (f j)))) : is_limit (fan.mk g) :=
reflects_limit.reflects ((fan_map_cone_limit _ _ _).symm t)

/-- The property of preserving products expressed in terms of fans. -/
def preserves_is_product [preserves_limits_of_shape (discrete J) G] {P : C} (g : Π j, P ⟶ f j)
  (t : is_limit (fan.mk g)) :
  is_limit (fan.mk (λ j, G.map (g j)) : fan (λ j, G.obj (f j))) :=
fan_map_cone_limit _ _ _ (preserves_limit.preserves t)

variables [has_products_of_shape J C] [preserves_limits_of_shape (discrete J) G]

def preserves_the_product :
  is_limit (fan.mk (λ (j : J), G.map (pi.π f j)) : fan (λ j, G.obj (f j))) :=
preserves_is_product G f _ (product_is_product _)

variables [has_products_of_shape J D]

/--
If `G` preserves limits, we have an isomorphism from the image of a product to the product of the
images.
-/
-- TODO perhaps weaken the assumptions here, to just require the relevant limits?
def preserves_products_iso :
  G.obj (∏ f) ≅ ∏ (λ j, G.obj (f j)) :=
preserves_limit_iso G (discrete.functor f) ≪≫
  has_limit.iso_of_nat_iso (discrete.nat_iso (λ j, iso.refl _))

@[simp, reassoc]
lemma preserves_products_iso_hom_π (j) :
  (preserves_products_iso G f).hom ≫ pi.π _ j = G.map (pi.π f j) :=
by simp [preserves_products_iso]

@[simp, reassoc]
lemma map_lift_comp_preserves_products_iso_hom (P : C) (g : Π j, P ⟶ f j) :
  G.map (pi.lift g) ≫ (preserves_products_iso G f).hom = pi.lift (λ j, G.map (g j)) :=
by { ext, simp [preserves_products_iso] }

end preserve_products

section preserve_equalizers

open category_theory.limits.walking_parallel_pair

variables {X Y Z : C} {f g : X ⟶ Y} {h : Z ⟶ X}

/--
(Implementation). The map of a fork is a limit iff the fork consisting of the mapped morphisms
is a limit.
This essentially lets us commute `fork.of_ι` with `functor.map_cone`.
-/
def equalizer_map_cone_limit (w : h ≫ f = h ≫ g) (hw : G.map h ≫ G.map f = G.map h ≫ G.map g) :
  is_limit (G.map_cone (fork.of_ι h w)) ≃ is_limit (fork.of_ι (G.map h) hw) :=
(is_limit.postcompose_hom_equiv (diagram_iso_parallel_pair _) _).symm.trans
  (is_limit.equiv_iso_limit (fork.ext (iso.refl _) (by simp [fork.ι_eq_app_zero])))

/-- The property of preserving equalizers expressed in terms of forks. -/
def map_is_limit_of_preserves_of_is_limit [preserves_limit (parallel_pair f g) G] (w : h ≫ f = h ≫ g)
  (l : is_limit (fork.of_ι h w)) :
  is_limit (fork.of_ι (G.map h) (by simp only [←G.map_comp, w]) : fork (G.map f) (G.map g)) :=
equalizer_map_cone_limit G w _ (preserves_limit.preserves l)

/-- The property of reflecting equalizers expressed in terms of forks. -/
def is_limit_of_reflects_of_map_is_limit [reflects_limit (parallel_pair f g) G] (w : h ≫ f = h ≫ g)
  (l : is_limit (fork.of_ι (G.map h) (by simp only [←G.map_comp, w]) : fork (G.map f) (G.map g))) :
  is_limit (fork.of_ι h w) :=
reflects_limit.reflects ((equalizer_map_cone_limit G w _).symm l)

end preserve_equalizers
