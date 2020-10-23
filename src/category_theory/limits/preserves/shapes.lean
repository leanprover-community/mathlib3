/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.preserves.limits
import category_theory.limits.shapes

universes v u₁ u₂

noncomputable theory

open category_theory category_theory.category category_theory.limits

variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]
variables (G : C ⥤ D) [preserves_limits G]

section preserve_products

variables {J : Type v} (f : J → C)

/--
If `G` preserves limits, we have an isomorphism
from the image of a product to the product of the images.
-/
-- TODO perhaps weaken the assumptions here, to just require the relevant limits?
def preserves_products_iso {J : Type v} (f : J → C) [has_limits C] [has_limits D] :
  G.obj (pi_obj f) ≅ pi_obj (λ j, G.obj (f j)) :=
preserves_limit_iso G (discrete.functor f) ≪≫
  has_limit.iso_of_nat_iso (discrete.nat_iso (λ j, iso.refl _))

@[simp, reassoc]
lemma preserves_products_iso_hom_π
  {J : Type v} (f : J → C) [has_limits C] [has_limits D] (j) :
  (preserves_products_iso G f).hom ≫ pi.π _ j = G.map (pi.π f j) :=
by simp [preserves_products_iso]

@[simp, reassoc]
lemma map_lift_comp_preserves_products_iso_hom
  {J : Type v} (f : J → C) [has_limits C] [has_limits D] (P : C) (g : Π j, P ⟶ f j) :
  G.map (pi.lift g) ≫ (preserves_products_iso G f).hom = pi.lift (λ j, G.map (g j)) :=
by { ext, simp [←G.map_comp] }

end preserve_products
