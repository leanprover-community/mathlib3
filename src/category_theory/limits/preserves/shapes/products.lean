/-
Copyright (c) 2020 Scott Morrison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.limits.preserves.limits
import category_theory.limits.shapes

universes v u₁ u₂

noncomputable theory

open category_theory category_theory.category category_theory.limits

variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]
variables (G : C ⥤ D)

section preserve_products

variables {J : Type v} (f : J → C)

/--
(Implementation). The map of a fan is a limit iff the fan consisting of the mapped morphisms
is a limit.
This essentially lets us commute `fan.mk` with `functor.map_cone`.
-/
def fan_map_cone_limit {P : C} (g : Π j, P ⟶ f j) :
  is_limit (G.map_cone (fan.mk P g)) ≃
  is_limit (fan.mk _ (λ j, G.map (g j)) : fan (λ j, G.obj (f j))) :=
begin
  refine (is_limit.postcompose_hom_equiv _ _).symm.trans (is_limit.equiv_iso_limit _),
  refine discrete.nat_iso (λ j, iso.refl (G.obj (f j))),
  refine cones.ext (iso.refl _) (λ j, by { dsimp, simp }),
end

/-- The property of preserving products expressed in terms of fans. -/
def map_is_limit_of_preserves_of_is_limit [preserves_limit (discrete.functor f) G]
  {P : C} (g : Π j, P ⟶ f j) (t : is_limit (fan.mk _ g)) :
  is_limit (fan.mk _ (λ j, G.map (g j)) : fan (λ j, G.obj (f j))) :=
fan_map_cone_limit _ _ _ (preserves_limit.preserves t)

/-- The property of reflecting products expressed in terms of fans. -/
def is_limit_of_reflects_of_map_is_limit [reflects_limit (discrete.functor f) G]
  {P : C} (g : Π j, P ⟶ f j) (t : is_limit (fan.mk _ (λ j, G.map (g j)) : fan (λ j, G.obj (f j)))) :
  is_limit (fan.mk P g) :=
reflects_limit.reflects ((fan_map_cone_limit _ _ _).symm t)

variables [has_product f] [preserves_limit (discrete.functor f) G]

/--
If `G` preserves products and `C` has them, then the fan constructed of the mapped projection of a
product is a limit.
-/
def is_limit_of_has_product_of_preserves_limit :
  is_limit (fan.mk _ (λ (j : J), G.map (pi.π f j)) : fan (λ j, G.obj (f j))) :=
map_is_limit_of_preserves_of_is_limit G f _ (product_is_product _)

variables [has_product (λ (j : J), G.obj (f j))]

/--
If `G` preserves limits, we have an isomorphism from the image of a product to the product of the
images.
-/
def preserves_products_iso : G.obj (∏ f) ≅ ∏ (λ j, G.obj (f j)) :=
is_limit.cone_point_unique_up_to_iso
  (is_limit_of_has_product_of_preserves_limit G f)
  (limit.is_limit _)

@[simp, reassoc]
lemma preserves_products_iso_hom_π (j) :
  (preserves_products_iso G f).hom ≫ pi.π _ j = G.map (pi.π f j) :=
is_limit.cone_point_unique_up_to_iso_hom_comp _ _ _

@[simp, reassoc]
lemma map_lift_comp_preserves_products_iso_hom (P : C) (g : Π j, P ⟶ f j) :
  G.map (pi.lift g) ≫ (preserves_products_iso G f).hom = pi.lift (λ j, G.map (g j)) :=
by { ext, simp [← G.map_comp] }

end preserve_products
