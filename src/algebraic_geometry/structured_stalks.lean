-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Mario Carneiro, Reid Barton

import algebraic_geometry.stalks

universes v₁ v₂ u₁ u₂

open category_theory
open category_theory.limits

namespace algebraic_geometry

variables (C : Type u₁) [𝒞 : category.{v₁+1} C]
variables (V : Type u₂) [𝒱 : category.{v₂+1} V]
include 𝒞 𝒱
variables [has_colimits.{v₁} C]

structure StructuredStalkPresheafedSpace (F : V ⥤ C) extends PresheafedSpace.{v₁} C :=
(structured_stalk : Π x : to_Top, V)
(compatible : Π x : to_Top, F.obj (structured_stalk x) ≅ (to_PresheafedSpace.stalk x))

namespace StructuredStalkPresheafedSpace
variables {C V}
variables {F : V ⥤ C}

instance : has_coe_to_sort (StructuredStalkPresheafedSpace.{v₁ v₂} C V F) :=
{ S := Type v₁, coe := λ F, F.to_PresheafedSpace.to_Top.α }

structure hom (X Y : StructuredStalkPresheafedSpace.{v₁ v₂} C V F) :=
(hom : X.to_PresheafedSpace ⟶ Y.to_PresheafedSpace)
(structured_stalk_map : Π (x : X.to_Top), Y.structured_stalk ((hom : X.to_Top → Y.to_Top) x) ⟶ X.structured_stalk x)
(compatible' : Π (x : X.to_Top), F.map (structured_stalk_map x) = (Y.compatible (hom x)).hom ≫ PresheafedSpace.stalk_map hom x ≫ (X.compatible x).inv . obviously)

restate_axiom hom.compatible'
attribute [simp] hom.compatible

@[extensionality] lemma hom.ext
  {X Y : StructuredStalkPresheafedSpace.{v₁ v₂} C V F} {f g : hom X Y}
  (w : f.hom = g.hom) (h : ∀ x, f.structured_stalk_map x = by { convert g.structured_stalk_map x, rw w }) : f = g :=
begin
  cases f, cases g,
  dsimp at w,
  subst w,
  congr,
  exact funext h,
end


def id (X : StructuredStalkPresheafedSpace.{v₁ v₂} C V F) : hom X X :=
{ hom := 𝟙 _,
  structured_stalk_map := λ x, 𝟙 _ }

@[simp] lemma id_hom (X : StructuredStalkPresheafedSpace.{v₁ v₂} C V F) : X.id.hom = 𝟙 _ :=
rfl
@[simp] lemma id_map (X : StructuredStalkPresheafedSpace.{v₁ v₂} C V F) (x : X) : X.id.structured_stalk_map x = 𝟙 _ :=
rfl

def comp (X Y Z : StructuredStalkPresheafedSpace.{v₁ v₂} C V F) (f : hom X Y) (g : hom Y Z) : hom X Z :=
{ hom := f.hom ≫ g.hom,
  structured_stalk_map := λ x, g.structured_stalk_map ((f.hom : X.to_Top → Y.to_Top) x) ≫ f.structured_stalk_map x }

@[simp] lemma comp_hom (X Y Z : StructuredStalkPresheafedSpace.{v₁ v₂} C V F) (f : hom X Y) (g : hom Y Z) : (comp X Y Z f g).hom = f.hom ≫ g.hom :=
rfl
@[simp] lemma comp_map
  (X Y Z : StructuredStalkPresheafedSpace.{v₁ v₂} C V F) (f : hom X Y) (g : hom Y Z) (x) :
  (comp X Y Z f g).structured_stalk_map x =
    g.structured_stalk_map ((f.hom : X.to_Top → Y.to_Top) x) ≫ f.structured_stalk_map x :=
rfl

local attribute [simp] PresheafedSpace.id_c PresheafedSpace.comp_c

instance category_of_structured_presheaves : category (StructuredStalkPresheafedSpace.{v₁ v₂} C V F) :=
{ hom  := hom,
  id   := id,
  comp := comp,
  comp_id' := begin tidy, op_induction X_1, cases X_1, tidy, erw category.comp_id, erw category.id_comp, refl, end,
  id_comp' := begin tidy, op_induction X_1, cases X_1, tidy, erw category.id_comp, erw category_theory.functor.map_id, erw category.comp_id, erw category.comp_id, end,
  assoc' := begin tidy, op_induction X_1, cases X_1, tidy, erw category_theory.functor.map_id, erw category.comp_id, end }


end StructuredStalkPresheafedSpace

end algebraic_geometry
