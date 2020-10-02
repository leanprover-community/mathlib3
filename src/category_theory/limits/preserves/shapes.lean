/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.preserves.basic
import category_theory.limits.shapes.products

universes v u₁ u₂

noncomputable theory

open category_theory
open category_theory.limits

variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]
variables (G : C ⥤ D) [preserves_limits G]

section
variables {J : Type v} [small_category J]

/--
If `G` preserves limits, we have an isomorphism from the image of the limit of a functor `F`
to the limit of the functor `F ⋙ G`.
-/
def preserves_limits_iso (F : J ⥤ C) [has_limit F] [has_limit (F ⋙ G)] :
  G.obj (limit F) ≅ limit (F ⋙ G) :=
(cones.forget _).map_iso
  (is_limit.unique_up_to_iso
    (preserves_limit.preserves (limit.is_limit F))
    (limit.is_limit (F ⋙ G)))

@[simp, reassoc]
lemma preserves_limits_iso_hom_π
  (F : J ⥤ C) [has_limit F] [has_limit (F ⋙ G)] (j) :
  (preserves_limits_iso G F).hom ≫ limit.π _ j = G.map (limit.π F j) :=
begin
  dsimp [preserves_limits_iso, has_limit.iso_of_nat_iso, cones.postcompose,
    is_limit.unique_up_to_iso, is_limit.lift_cone_morphism],
  simp,
end

/--
If `G` preserves limits, we have an isomorphism
from the image of a product to the product of the images.
-/
-- TODO perhaps weaken the assumptions here, to just require the relevant limits?
def preserves_products_iso {J : Type v} (f : J → C) [has_limits C] [has_limits D] :
  G.obj (pi_obj f) ≅ pi_obj (λ j, G.obj (f j)) :=
preserves_limits_iso G (discrete.functor f) ≪≫
  has_limit.iso_of_nat_iso (discrete.nat_iso (λ j, iso.refl _))

@[simp, reassoc]
lemma preserves_products_iso_hom_π
  {J : Type v} (f : J → C) [has_limits C] [has_limits D] (j) :
  (preserves_products_iso G f).hom ≫ pi.π _ j = G.map (pi.π f j) :=
begin
  dsimp [preserves_products_iso, preserves_limits_iso, has_limit.iso_of_nat_iso, cones.postcompose,
         is_limit.unique_up_to_iso, is_limit.lift_cone_morphism, is_limit.map],
  simp only [limit.lift_π, discrete.nat_iso_hom_app, limit.cone_π, limit.lift_π_assoc,
             nat_trans.comp_app, category.assoc, functor.map_cone_π, is_limit.map_π],
  dsimp, simp, -- See note [dsimp, simp],
end

@[simp, reassoc]
lemma map_lift_comp_preserves_products_iso_hom
  {J : Type v} (f : J → C) [has_limits C] [has_limits D] (P : C) (g : Π j, P ⟶ f j) :
  G.map (pi.lift g) ≫ (preserves_products_iso G f).hom = pi.lift (λ j, G.map (g j)) :=
begin
  ext,
  simp only [limit.lift_π, fan.mk_π_app, preserves_products_iso_hom_π, category.assoc],
  simp only [←G.map_comp],
  simp only [limit.lift_π, fan.mk_π_app],
end

end
